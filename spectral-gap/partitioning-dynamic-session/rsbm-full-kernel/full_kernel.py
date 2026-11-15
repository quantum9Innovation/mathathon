#!/usr/bin/env python3
"""Exact full-kernel prototype and deterministic certificate verifier.

Field arithmetic and irreducibility checks are implemented here with
integer polynomial arithmetic. Recovery uses no rank oracle. Dense base-
field elimination appears only in the independent checks at the bottom.
"""
from pathlib import Path
import copy
import importlib.util
import itertools
import json
import math
import random
import sys

HERE = Path(__file__).resolve().parent


def trim(a):
    a = a[:]
    while a and a[-1] == 0:
        a.pop()
    return a


def poly_sub(a, b, p):
    return trim([((a[i] if i < len(a) else 0)
                  -(b[i] if i < len(b) else 0)) % p
                 for i in range(max(len(a), len(b)))])


def poly_rem(a, b, p):
    a, b = trim(a), trim(b)
    if not b:
        raise ZeroDivisionError
    inv = pow(b[-1], -1, p)
    while len(a) >= len(b):
        factor = a[-1]*inv % p
        shift = len(a)-len(b)
        for i, bi in enumerate(b):
            a[i+shift] = (a[i+shift]-factor*bi) % p
        a = trim(a)
    return a


def poly_mul_mod(a, b, h, p):
    if not a or not b:
        return []
    out = [0]*(len(a)+len(b)-1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i+j] = (out[i+j]+ai*bj) % p
    return poly_rem(out, h, p)


def poly_pow_mod(a, power, h, p):
    out = [1]
    while power:
        if power & 1:
            out = poly_mul_mod(out, a, h, p)
        a = poly_mul_mod(a, a, h, p)
        power >>= 1
    return out


def poly_gcd(a, b, p):
    while b:
        a, b = b, poly_rem(a, b, p)
    if not a:
        return []
    inv = pow(a[-1], -1, p)
    return [inv*x % p for x in a]


def irreducible(h, p):
    s = len(h)-1
    if s < 1 or h[-1] != 1 or any(not 0 <= x < p for x in h):
        return False
    xpower = [0, 1]
    for _ in range(1, s//2+1):
        xpower = poly_pow_mod(xpower, p, h, p)
        if len(poly_gcd(h, poly_sub(xpower, [0, 1], p), p)) > 1:
            return False
    return True


def extension_degree(p, n):
    bound = 64*(n+1)**6
    s, q = 1, p
    while q < bound:
        s += 1
        q *= p
    return s, q


class Field:
    def __init__(self, p, h):
        assert irreducible(h, p)
        self.p, self.h, self.s = p, h[:], len(h)-1
        self.q = p**self.s
        self.multiplications = 0

    @classmethod
    def construct(cls, p, n, rng):
        s, _ = extension_degree(p, n)
        trials = 0
        while True:
            trials += 1
            h = [rng.randrange(p) for _ in range(s)]+[1]
            if irreducible(h, p):
                return cls(p, h), trials

    def digits(self, a):
        out = []
        for _ in range(self.s):
            out.append(a % self.p)
            a //= self.p
        return out

    def encode(self, digits):
        out = 0
        for x in reversed(digits):
            out = out*self.p+x
        return out

    def add(self, a, b):
        if a == 0:
            return b
        if b == 0:
            return a
        return self.encode([(x+y) % self.p
                            for x, y in zip(self.digits(a), self.digits(b))])

    def neg(self, a):
        return self.encode([(-x) % self.p for x in self.digits(a)])

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def scale(self, a, c):
        c %= self.p
        if c == 0 or a == 0:
            return 0
        if c == 1:
            return a
        return self.encode([c*x % self.p for x in self.digits(a)])

    def mul(self, a, b):
        self.multiplications += 1
        if not a or not b:
            return 0
        if a < self.p:
            return self.scale(b, a)
        if b < self.p:
            return self.scale(a, b)
        aa, bb = self.digits(a), self.digits(b)
        out = [0]*(2*self.s-1)
        for i, ai in enumerate(aa):
            if ai:
                for j, bj in enumerate(bb):
                    out[i+j] = (out[i+j]+ai*bj) % self.p
        for j in range(len(out)-1, self.s-1, -1):
            coefficient = out[j]
            if coefficient:
                for i in range(self.s):
                    out[j-self.s+i] = (out[j-self.s+i]
                                        -coefficient*self.h[i]) % self.p
        return self.encode(out[:self.s])

    def power(self, a, exponent):
        out = 1
        while exponent:
            if exponent & 1:
                out = self.mul(out, a)
            a = self.mul(a, a)
            exponent >>= 1
        return out

    def inv(self, a):
        if not a:
            raise ZeroDivisionError
        # Exponentiation is polylogarithmic as well; no inverse oracle.
        return self.power(a, self.q-2)


def bm(seq, F):
    C, B = [1], [1]
    L, shift, last = 0, 1, 1
    for j, sj in enumerate(seq):
        discrepancy = sj
        for i in range(1, L+1):
            if i < len(C):
                discrepancy = F.add(discrepancy, F.mul(C[i], seq[j-i]))
        if discrepancy == 0:
            shift += 1
            continue
        saved = C[:]
        factor = F.mul(discrepancy, F.inv(last))
        C += [0]*max(0, shift+len(B)-len(C))
        for i, bi in enumerate(B):
            C[i+shift] = F.sub(C[i+shift], F.mul(factor, bi))
        if 2*L <= j:
            L = j+1-L
            B, last, shift = saved, discrepancy, 1
        else:
            shift += 1
    C += [0]*max(0, L+1-len(C))
    return L, C[:L+1]


def matvec(rows, x, F):
    out = []
    for row in rows:
        total = 0
        for j, a in row:
            total = F.add(total, F.scale(x[j], a))
        out.append(total)
    return out


def sequence(rows, D, u, v, F):
    n = len(rows)
    def apply(x):
        return [F.mul(di, yi) for di, yi in zip(D, matvec(rows, x, F))]
    current = apply(v)
    seq = []
    for j in range(2*n):
        scalar = 0
        for ui, xi in zip(u, current):
            scalar = F.add(scalar, F.mul(ui, xi))
        seq.append(scalar)
        if j+1 < 2*n:
            current = apply(current)
    return seq, apply


def insert_canonical(y, columns, pivots, F):
    """Keep columns normalized to identity on their pivot rows."""
    y = y[:]
    for column, pivot in zip(columns, pivots):
        coeff = y[pivot]
        if coeff:
            y = [F.sub(a, F.mul(coeff, b)) for a, b in zip(y, column)]
    pivot = next((i for i, a in enumerate(y) if a), None)
    if pivot is None:
        return False
    inv = F.inv(y[pivot])
    y = [F.mul(inv, a) for a in y]
    for j, column in enumerate(columns):
        coeff = column[pivot]
        if coeff:
            columns[j] = [F.sub(a, F.mul(coeff, b)) for a, b in zip(column, y)]
    columns.append(y)
    pivots.append(pivot)
    return True


def check_input(rows, p):
    assert p >= 3 and p % 2 and all(p % j for j in range(3, math.isqrt(p)+1, 2))
    n = len(rows)
    assert n >= 1
    table = [{j: a for j, a in row} for row in rows]
    assert all(len(row) == len(table[i]) for i, row in enumerate(rows))
    assert all(0 <= j < n and 0 < a < p and table[j].get(i, 0) == a
               for i, row in enumerate(rows) for j, a in row)


def kernel_basis(rows, p, seed=None):
    check_input(rows, p)
    n = len(rows)
    rng = random.SystemRandom() if seed is None else random.Random(seed)
    F, field_trials = Field.construct(p, n, rng)
    stats = {"field_degree": F.s, "field_size": F.q,
             "irreducibility_candidates": field_trials,
             "trials": 0, "projection_probes": 0, "trial_lengths": []}
    while True:
        stats["trials"] += 1
        D = [rng.randrange(1, F.q) for _ in range(n)]
        u = [rng.randrange(F.q) for _ in range(n)]
        v = [rng.randrange(F.q) for _ in range(n)]
        seq, apply = sequence(rows, D, u, v, F)
        ell, connection = bm(seq, F)
        if len(stats["trial_lengths"]) < 16:
            stats["trial_lengths"].append(ell)
        if connection[-1] == 0:
            continue
        g = connection[::-1]
        target = n-ell
        columns, pivots = [], []
        for attempt in range(n+2):
            if len(columns) == target:
                # Canonical normalization effects the Frobenius descent.
                assert all(0 <= x < p for col in columns for x in col)
                cert = {"p": p, "h": F.h, "D": D, "u": u, "v": v,
                        "ell": ell, "columns": columns, "pivots": pivots}
                stats["field_multiplications"] = F.multiplications
                return columns, cert, stats
            if attempt == n+1:
                break
            stats["projection_probes"] += 1
            b = [rng.randrange(F.q) for _ in range(n)]
            y = [F.mul(g[-1], a) for a in b]
            for coefficient in reversed(g[:-1]):
                y = [F.add(a, F.mul(coefficient, bi))
                     for a, bi in zip(apply(y), b)]
            if any(matvec(rows, y, F)):
                continue
            insert_canonical(y, columns, pivots, F)


def verify(rows, cert, p):
    """Deterministic complete-kernel verifier; no rank oracle."""
    try:
        if cert["p"] != p:
            return False
        check_input(rows, p)
        n = len(rows)
        s, q = extension_degree(p, n)
        h = cert["h"]
        if len(h) != s+1 or not irreducible(h, p):
            return False
        F = Field(p, h)
        D, u, v = cert["D"], cert["u"], cert["v"]
        if not (len(D) == len(u) == len(v) == n):
            return False
        if not all(0 < x < q for x in D):
            return False
        if not all(0 <= x < q for x in u+v):
            return False
        ell = cert["ell"]
        columns, pivots = cert["columns"], cert["pivots"]
        r = len(columns)
        if not (0 <= ell <= n and r == n-ell and len(pivots) == r):
            return False
        if len(set(pivots)) != r or not all(0 <= i < n for i in pivots):
            return False
        for j, col in enumerate(columns):
            if len(col) != n or not all(0 <= x < p for x in col):
                return False
            if any(col[pivot] != int(i == j) for i, pivot in enumerate(pivots)):
                return False
            if any(sum(a*col[k] for k, a in row) % p for row in rows):
                return False
        seq, _ = sequence(rows, D, u, v, F)
        L, _ = bm(seq, F)
        return L == ell
    except (AssertionError, KeyError, IndexError, ValueError, TypeError, ZeroDivisionError):
        return False


def rows_from_dense(M, p):
    return [[(j, a % p) for j, a in enumerate(row) if a % p]
            for row in M]


def rank_base(M, p):
    A = [[x % p for x in row] for row in M]
    r = 0
    for j in range(len(A[0])):
        pivot = next((i for i in range(r, len(A)) if A[i][j]), None)
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        inv = pow(A[r][j], -1, p)
        A[r] = [inv*x % p for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][j]:
                factor = A[i][j]
                A[i] = [(a-factor*b) % p for a, b in zip(A[i], A[r])]
        r += 1
        if r == len(A):
            break
    return r


def enumerate_kernel(columns, n, p):
    """O(n*p^r) total work; carries cost only a geometric sum."""
    r = len(columns)
    digits, image = [0]*r, [0]*n
    total = p**r
    for step in range(total):
        yield image[:]
        if step+1 == total:
            return
        for j in range(r):
            image = [(a+b) % p for a, b in zip(image, columns[j])]
            digits[j] += 1
            if digits[j] < p:
                break
            digits[j] = 0


def partition_list(columns, adj, lam, p):
    out, n = [], len(adj)
    for image in enumerate_kernel(columns, n, p):
        if image[-1] != 1 or any(x not in (1, p-1) for x in image):
            continue
        sigma = [1 if x == 1 else -1 for x in image]
        if sum(sigma) == 0 and all(sum(sigma[j] for j in row) == lam*sigma[i]
                                   for i, row in enumerate(adj)):
            out.append(sigma)
    return out


def run_checks():
    rng = random.Random(123687)
    counts = {}
    for degree in [2, 3, 4]:
        counts[str(degree)] = sum(irreducible(list(coef)+[1], 3)
                                  for coef in itertools.product(range(3), repeat=degree))
    assert counts == {"2": 3, "3": 8, "4": 18}
    Fsmall = Field(3, [0, 1])
    lower_checks = 0
    for n in range(1, 9):
        for rep in range(20):
            M = [[0]*n for _ in range(n)]
            for i in range(n):
                for j in range(i+1):
                    M[i][j] = M[j][i] = rng.randrange(3)
            rows = rows_from_dense(M, 3)
            D = [rng.randrange(1, 3) for _ in range(n)]
            u = [rng.randrange(3) for _ in range(n)]
            v = [rng.randrange(3) for _ in range(n)]
            seq, _ = sequence(rows, D, u, v, Fsmall)
            ell, _ = bm(seq, Fsmall)
            assert ell <= rank_base(M, 3)
            lower_checks += 1
    cases = {"zero": [[0]*4 for _ in range(4)],
             "identity": [[int(i == j) for j in range(4)] for i in range(4)],
             "corank_one": [[1, 0, 0], [0, 2, 0], [0, 0, 0]],
             "symmetric_nilpotent": [[1]*3 for _ in range(3)],
             "corank_two": [[1, 0, 0, 0], [0, 2, 0, 0],
                            [0, 0, 0, 0], [0, 0, 0, 0]]}
    results = []
    for index, (name, M) in enumerate(cases.items()):
        rows = rows_from_dense(M, 3)
        columns, cert, stats = kernel_basis(rows, 3, seed=9912+index)
        r = len(M)-rank_base(M, 3)
        assert len(columns) == r and verify(rows, cert, 3)
        images = list(enumerate_kernel(columns, len(M), 3))
        assert len({tuple(x) for x in images}) == 3**r
        assert all(all(sum(a*x[j] for j, a in row) % 3 == 0 for row in rows)
                   for x in images)
        bad = copy.deepcopy(cert)
        bad["ell"] = (bad["ell"]+1) % (len(M)+1)
        assert not verify(rows, bad, 3)
        if columns:
            bad = copy.deepcopy(cert)
            bad["columns"][0][0] = 3
            assert not verify(rows, bad, 3)
        bad = copy.deepcopy(cert)
        bad["p"] = 9
        assert not verify(rows, bad, 3)
        bad = copy.deepcopy(cert)
        bad["h"] = [0]*(len(bad["h"])-1)+[1]
        assert not verify(rows, bad, 3)
        results.append({"name": name, "n": len(M), "corank": r,
                        "certified": True, "stats": stats})
    # A nilpotent base matrix with the deliberately bad D=I: g(0)=0.
    rows = rows_from_dense([[1]*3 for _ in range(3)], 3)
    seq, _ = sequence(rows, [1]*3, [1, 0, 0], [1, 0, 0], Fsmall)
    ell, connection = bm(seq, Fsmall)
    assert ell == 1 and connection[-1] == 0
    # Import only the prior packet's graph sampler, preventing cache writes.
    sys.dont_write_bytecode = True
    path = HERE.parent/"rsbm-exact-algorithm"/"certified_recovery.py"
    spec = importlib.util.spec_from_file_location("prior_recovery", path)
    prior = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(prior)
    adj, planted = prior.model_graph(6, 3, 1, seed=512)
    n, lam, p = len(adj), 2, 3
    M = [[int(j in adj[i])-lam*int(i == j) for j in range(n)] for i in range(n)]
    rows = rows_from_dense(M, p)
    columns, cert, stats = kernel_basis(rows, p, seed=741)
    assert len(columns) == n-rank_base(M, p) and verify(rows, cert, p)
    listed = partition_list(columns, adj, lam, p)
    brute = []
    for positive in itertools.combinations(range(n-1), n//2-1):
        sigma = [-1]*(n-1)+[1]
        for i in positive:
            sigma[i] = 1
        if all(sum(sigma[j] for j in row) == lam*sigma[i]
               for i, row in enumerate(adj)):
            brute.append(sigma)
    assert {tuple(x) for x in listed} == {tuple(x) for x in brute}
    planted = [x*planted[-1] for x in planted]
    assert planted in listed
    output = {"irreducible_counts_over_F3": counts,
              "rank_lower_bound_checks": lower_checks,
              "full_kernel_cases": results,
              "bad_nilpotent_preconditioner_rejected": True,
              "rsbm_extra_real_kernel_case": {
                  "n": n, "known_real_nullity_from_previous_packet": 2,
                  "base_field": p, "modular_corank": len(columns),
                  "enumerated_base_kernel_vectors": p**len(columns),
                  "exact_admissible_partitions_up_to_exchange": len(listed),
                  "matches_exhaustive_sign_search": True, "stats": stats}}
    # Deterministic cubic RSBM fixture: unique sign partition, real nullity two.
    N = 8
    unique_adj = [set() for _ in range(2*N)]
    for shift, cycle in [(0, list(range(N))), (N, [5, 6, 7, 0, 4, 1, 2, 3])]:
        for i, a in enumerate(cycle):
            b = cycle[(i+1) % N]
            unique_adj[shift+a].add(shift+b)
            unique_adj[shift+b].add(shift+a)
    for i in range(N):
        unique_adj[i].add(N+i)
        unique_adj[N+i].add(i)
    unique_adj = [sorted(row) for row in unique_adj]
    U = [[int(j in unique_adj[i])-int(i == j) for j in range(2*N)]
         for i in range(2*N)]
    v_int = [-1, 0, -1, -2, -1, 0, 0, -1, 0, 2, 1, 0, 1, 1, 1, 0]
    w_int = [0, -1, 0, 1, 0, -1, -1, 0, 1, -1, 0, 1, 0, 0, 0, 1]
    assert all(sum(a*b for a, b in zip(row, v_int)) == 0 for row in U)
    assert all(sum(a*b for a, b in zip(row, w_int)) == 0 for row in U)
    assert v_int[0] == -1 and w_int[0] == 0 and v_int[1] == 0 and w_int[1] == -1
    unique_rows = rows_from_dense(U, 3)
    unique_columns, unique_cert, unique_stats = kernel_basis(unique_rows, 3, seed=192)
    assert len(unique_columns) == 2 and verify(unique_rows, unique_cert, 3)
    assert rank_base(U, 3) == 2*N-2
    unique_list = partition_list(unique_columns, unique_adj, 1, 3)
    assert unique_list == [[-1]*N+[1]*N]
    output["unique_partition_despite_real_nullity_two"] = {
        "n": 2*N, "d1": 2, "d2": 1, "base_field": 3,
        "exact_real_corank": 2, "exact_modular_corank": 2,
        "enumerated_base_kernel_vectors": 9,
        "exact_admissible_partitions_up_to_exchange": 1,
        "planted_partition_recovered": True, "stats": unique_stats}
    (HERE/"full-kernel-checks.json").write_text(json.dumps(output, indent=2)+"\n")
    (HERE/"full-kernel-example-certificate.json").write_text(
        json.dumps({"integer_matrix": M, "certificate": cert}, indent=2)+"\n")
    (HERE/"unique-degenerate-example-certificate.json").write_text(
        json.dumps({"integer_matrix": U, "certificate": unique_cert,
                    "exact_integer_kernel_witnesses": [v_int, w_int],
                    "partition_list": unique_list}, indent=2)+"\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    run_checks()
