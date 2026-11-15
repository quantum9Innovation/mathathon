# Extracted executable primitive from the source-bound full_kernel.py.
# The original self-test driver is omitted; check_linear_algebra.py supplies
# independent base-field reference and certificate-forgery checks here.
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


