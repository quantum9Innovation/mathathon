#!/usr/bin/env python3
"""Exact certifying recovery prototype; integer and prime-field arithmetic.

The implemented algorithm uses no floating point, eigenvalue routine, or
general matrix-rank oracle. Dense modular rank and SymPy are used only in
the independent test driver below. All output files stay beside this file.
"""
from pathlib import Path
import copy
import json
import math
import random

HERE = Path(__file__).resolve().parent


def is_prime_trial(p):
    if p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    for q in range(3, math.isqrt(p)+1, 2):
        if p % q == 0:
            return False
    return True


def sample_prime(n, degree, rng):
    lo = 128*(degree+1)**2*n*n
    count = 0
    while True:
        p = rng.randrange(lo+1, 2*lo+1)
        count += 1
        if is_prime_trial(p):
            return p, count


def berlekamp_massey(seq, p):
    """Return true shortest-register length L and connection coefficients.

    s[j]+C[1]s[j-1]+...+C[L]s[j-L]=0, j>=L; C[0]=1.
    Keeping L separate from the printed polynomial degree is essential.
    """
    C, B = [1], [1]
    L, shift, last = 0, 1, 1
    for j, sj in enumerate(seq):
        discrepancy = (sj + sum((C[i] if i < len(C) else 0)*seq[j-i]
                                for i in range(1, L+1))) % p
        if discrepancy == 0:
            shift += 1
            continue
        saved = C[:]
        factor = discrepancy*pow(last, -1, p) % p
        needed = shift+len(B)
        C += [0]*max(0, needed-len(C))
        for i, bi in enumerate(B):
            C[i+shift] = (C[i+shift]-factor*bi) % p
        if 2*L <= j:
            L = j+1-L
            B, last, shift = saved, discrepancy, 1
        else:
            shift += 1
    C += [0]*max(0, L+1-len(C))
    C = C[:L+1]
    assert C[0] == 1
    assert all((seq[j]+sum(C[i]*seq[j-i] for i in range(1, L+1))) % p == 0
               for j in range(L, len(seq)))
    return L, C


def sparse_matvec(rows, x, p):
    return [sum(a*x[j] for j, a in row) % p for row in rows]


def shifted_sequence(rows, diagonal, u, v, p):
    m = len(rows)
    def apply(x):
        return [(d*y) % p for d, y in zip(diagonal, sparse_matvec(rows, x, p))]
    current = apply(v)
    seq = []
    for j in range(2*m):
        seq.append(sum(ui*xi for ui, xi in zip(u, current)) % p)
        if j+1 < 2*m:
            current = apply(current)
    return seq, apply


def graph_checks(adj):
    n = len(adj)
    degree = len(adj[0])
    assert n >= 2
    assert all(len(row) == degree and len(set(row)) == degree for row in adj)
    assert all(0 <= j < n and j != i and i in adj[j]
               for i, row in enumerate(adj) for j in row)
    return n, degree


def minor_rows(adj, lam):
    n, degree = graph_checks(adj)
    m = n-1
    rows = []
    rhs = []
    for i in range(m):
        row = [(j, 1) for j in adj[i] if j < m]
        if lam:
            row.append((i, -lam))
        rows.append(row)
        rhs.append(-int(m in adj[i]))
    return rows, rhs


def integer_sign_check(adj, lam, sigma):
    return (len(sigma) == len(adj) and sigma[-1] == 1
            and all(x in (-1, 1) for x in sigma) and sum(sigma) == 0
            and all(sum(sigma[j] for j in row) == lam*sigma[i]
                    for i, row in enumerate(adj)))


def recover(adj, lam, tries, seed=None):
    n, degree = graph_checks(adj)
    assert abs(lam) <= degree
    rows, rhs = minor_rows(adj, lam)
    m = n-1
    # A fixed seed is only for reproducible checks. Production uses fresh bits.
    rng = random.SystemRandom() if seed is None else random.Random(seed)
    stats = {"trials": 0, "primality_candidates": 0,
             "rank_rejections": 0, "sign_rejections": 0}
    for _ in range(tries):
        p, candidates = sample_prime(n, degree, rng)
        stats["trials"] += 1
        stats["primality_candidates"] += candidates
        diagonal = [rng.randrange(1, p) for _ in range(m)]
        u = [rng.randrange(p) for _ in range(m)]
        v = [rng.randrange(p) for _ in range(m)]
        seq, apply = shifted_sequence(rows, diagonal, u, v, p)
        L, connection = berlekamp_massey(seq, p)
        if L != m or connection[-1] == 0:
            stats["rank_rejections"] += 1
            continue
        # Monic annihilator in increasing-power order.
        f = connection[::-1]
        target = [di*ci % p for di, ci in zip(diagonal, rhs)]
        total = target[:]
        for i in range(m-1, 0, -1):
            total = [(a+f[i]*b) % p for a, b in zip(apply(total), target)]
        coeff = -pow(f[0], -1, p) % p
        x = [coeff*yi % p for yi in total]
        if sparse_matvec(rows, x, p) != [ci % p for ci in rhs]:
            raise AssertionError("Certified characteristic recurrence failed to solve")
        if any(xi not in (1, p-1) for xi in x):
            stats["sign_rejections"] += 1
            continue
        sigma = [1 if xi == 1 else -1 for xi in x]+[1]
        if not integer_sign_check(adj, lam, sigma):
            stats["sign_rejections"] += 1
            continue
        cert = {"p": p, "diagonal": diagonal, "u": u, "v": v,
                "sigma": sigma, "lambda": lam}
        return cert, stats
    return None, stats


def verify(adj, cert):
    """Deterministic certificate verification, independently recomputing BM."""
    try:
        n, degree = graph_checks(adj)
        p, lam = cert["p"], cert["lambda"]
        lo = 128*(degree+1)**2*n*n
        if not (lo < p <= 2*lo) or abs(lam) > degree:
            return False
        if not is_prime_trial(p):
            return False
        m = n-1
        diagonal, u, v = cert["diagonal"], cert["u"], cert["v"]
        if not (len(diagonal) == len(u) == len(v) == m):
            return False
        if not (all(0 < x < p for x in diagonal)
                and all(0 <= x < p for x in u+v)):
            return False
        if not integer_sign_check(adj, lam, cert["sigma"]):
            return False
        rows, _ = minor_rows(adj, lam)
        seq, _ = shifted_sequence(rows, diagonal, u, v, p)
        L, connection = berlekamp_massey(seq, p)
        return L == m and connection[-1] != 0
    except (AssertionError, KeyError, ValueError, TypeError, IndexError):
        return False


def sample_simple_regular(block_size, degree, rng):
    # Configuration pairing conditioned on simplicity: genuinely uniform.
    assert block_size*degree % 2 == 0 and 0 <= degree < block_size
    stubs = [i for i in range(block_size) for _ in range(degree)]
    while True:
        rng.shuffle(stubs)
        edges = set()
        for i in range(0, len(stubs), 2):
            p, q = sorted((stubs[i], stubs[i+1]))
            if p == q or (p, q) in edges:
                break
            edges.add((p, q))
        else:
            return edges


def model_graph(N, d1, d2, seed):
    rng = random.Random(seed)
    edges = set(sample_simple_regular(N, d1, rng))
    edges.update((p+N, q+N) for p, q in sample_simple_regular(N, d1, rng))
    # An arbitrary prescribed regular bipartite cross graph is allowed.
    edges.update((i, N+(i+s) % N) for i in range(N) for s in range(d2))
    perm = list(range(2*N))
    rng.shuffle(perm)
    adj = [set() for _ in perm]
    signs = [0]*len(perm)
    for i, pi in enumerate(perm):
        signs[pi] = 1 if i < N else -1
    for i, j in edges:
        u, v = perm[i], perm[j]
        adj[u].add(v)
        adj[v].add(u)
    adj = [sorted(row) for row in adj]
    graph_checks(adj)
    return adj, signs


def rank_mod_dense(matrix, p):
    A = [[a % p for a in row] for row in matrix]
    r = 0
    for j in range(len(A[0])):
        pivot = next((i for i in range(r, len(A)) if A[i][j]), None)
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        inv = pow(A[r][j], -1, p)
        A[r] = [inv*a % p for a in A[r]]
        for i in range(len(A)):
            if i != r and A[i][j]:
                factor = A[i][j]
                A[i] = [(a-factor*b) % p for a, b in zip(A[i], A[r])]
        r += 1
        if r == len(A):
            break
    return r


def run_checks():
    from sympy import Matrix
    rng = random.Random(981723)
    generic = {"matrices": 0, "singular_matrices": 0, "accepted": 0,
               "false_certificates": 0}
    for m in range(1, 11):
        for rep in range(100):
            p = 101
            dense = [[rng.randrange(p) for _ in range(m)] for _ in range(m)]
            if rep % 2 == 0:
                dense[-1] = [0]*m
            rank = rank_mod_dense(dense, p)
            rows = [[(j, a) for j, a in enumerate(row) if a] for row in dense]
            diag = [rng.randrange(1, p) for _ in range(m)]
            u = [rng.randrange(p) for _ in range(m)]
            v = [rng.randrange(p) for _ in range(m)]
            seq, _ = shifted_sequence(rows, diag, u, v, p)
            L, connection = berlekamp_massey(seq, p)
            generic["matrices"] += 1
            generic["singular_matrices"] += rank < m
            generic["accepted"] += L == m
            generic["false_certificates"] += L == m and rank < m
            assert L <= rank
            if L == m:
                assert connection[-1] != 0
    assert generic["false_certificates"] == 0
    models = []
    saved = None
    for i, N in enumerate([6, 8, 10, 12, 16, 20]):
        adj, signs = model_graph(N, 3, 1, seed=512+i)
        n = 2*N
        denseM = [[int(j in adj[i])-2*int(i == j) for j in range(n)]
                  for i in range(n)]
        # Exact domain arithmetic prevents slow generic symbolic zero tests.
        nullity = n-Matrix(denseM).to_DM().rank()
        cert, stats = recover(adj, 2, tries=8, seed=811+i)
        if nullity == 1:
            assert cert is not None
        if cert is not None:
            assert nullity == 1 and verify(adj, cert)
            target = [x*signs[-1] for x in signs]
            assert cert["sigma"] == target
            if saved is None:
                saved = {"adjacency": adj, "certificate": cert}
                bad = copy.deepcopy(cert)
                bad["sigma"][0] *= -1
                assert not verify(adj, bad)
                bad = copy.deepcopy(cert)
                bad["diagonal"][0] = 0
                assert not verify(adj, bad)
                bad = copy.deepcopy(cert)
                bad["u"] = [0]*(n-1)
                assert not verify(adj, bad)
        models.append({"N": N, "n": n, "d1": 3, "d2": 1,
                       "exact_rational_nullity": nullity,
                       "recovered": cert is not None, "stats": stats})
    C4 = [[1, 3], [0, 2], [1, 3], [0, 2]]
    cert, stats = recover(C4, 0, tries=4, seed=19)
    assert cert is None and stats["rank_rejections"] == 4
    nilpotent_rows = [[(1, 1)], []]
    seq, _ = shifted_sequence(nilpotent_rows, [1, 1], [1, 0], [0, 1], 101)
    L, _ = berlekamp_massey(seq, 101)
    assert seq == [1, 0, 0, 0] and L == 1
    results = {"generic_rank_certificates": generic, "rsbm_models": models,
               "singular_C4_rejected": stats,
               "nilpotent_shift_check": {"sequence": seq, "complexity": L},
               "tamper_checks_passed": True}
    (HERE/"recovery-checks.json").write_text(json.dumps(results, indent=2)+"\n")
    (HERE/"example-certificate.json").write_text(json.dumps(saved, indent=2)+"\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    run_checks()
