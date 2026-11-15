"""Exact small rectangular-block check of the unequal moment proof."""
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import numpy as np

N1, N2, A1, A2, B1, B2 = 2, 4, 3, 4, 2, 1
C1 = np.array([[0, A1], [A1, 0]], dtype=np.int64)
B = np.array([[1, 1, 0, 0], [0, 0, 1, 1]], dtype=np.int64)
matchings = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
C2s = []
for selected in product(range(3), repeat=A2):
    c = np.zeros((N2, N2), dtype=np.int64)
    for which in selected:
        for i, j in matchings[which]:
            c[i, j] += 1
            c[j, i] += 1
    C2s.append(c)


def table(n, a, matrices, p):
    x = np.array(list(product(range(p), repeat=n)), dtype=np.int64)
    power = p ** np.arange(n - 1, -1, -1)
    count = np.zeros((len(x), len(x)), dtype=np.int64)
    for matrix in matrices:
        indices = (x @ matrix.T % p) @ power
        count[np.arange(len(x)), indices] += 1
    den = p ** (n - 1)
    ref = np.zeros_like(count)
    constant = np.all(x == x[:, :1], axis=1)
    sums = x.sum(axis=1) % p
    for i, row in enumerate(x):
        if constant[i]:
            ref[i, ((a * row) % p) @ power] = den
        else:
            ref[i, sums == a * sums[i] % p] = 1
    error_num = np.max(abs(count * den - ref * len(matrices)), axis=1)
    error = Fraction(int(error_num.sum()), len(matrices) * den)
    return x, power, count, ref, den, error, constant


def rank_mod(a, p):
    rows = [[int(x) % p for x in row] for row in a]
    rank = 0
    for j in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inv = pow(rows[rank][j], -1, p)
        rows[rank] = [x * inv % p for x in rows[rank]]
        for i in range(rank + 1, len(rows)):
            q = rows[i][j]
            rows[i] = [(x - q * y) % p for x, y in zip(rows[i], rows[rank])]
        rank += 1
        if rank == len(rows):
            break
    return rank


records = []
for p in (3, 5):
    x, xp, pc1, rc1, den1, eps1, const1 = table(N1, A1, [C1], p)
    y, yp, pc2, rc2, den2, eps2, const2 = table(N2, A2, C2s, p)
    for lam in (2, 5):
        c1, c2 = A1 - lam, A2 - lam
        assert c1 * c2 == B1 * B2
        hyper = np.array([[c1, B2], [B1, c2]])
        constants = np.array([[c1, B1], [B2, c2]])
        assert rank_mod(hyper, p) == rank_mod(constants, p) == 1
        ix1 = ((lam * x[:, None, :] - (y @ B.T)[None, :, :]) % p) @ xp
        ix2 = ((lam * y[:, None, :] - (x @ B)[None, :, :]) % p) @ yp
        P1 = pc1[np.arange(len(x))[:, None], ix1]
        P2 = pc2[np.arange(len(y))[:, None], ix2].T
        R1 = rc1[np.arange(len(x))[:, None], ix1]
        R2 = rc2[np.arange(len(y))[:, None], ix2].T
        actual = Fraction(int((P1 * P2).sum()), len(C2s))
        replaced1 = Fraction(int((R1 * P2).sum()), den1 * len(C2s))
        reference_num = R1 * R2
        reference = Fraction(int(reference_num.sum()), den1 * den2)
        assert abs(actual - replaced1) <= (2 + eps2) * eps1
        assert abs(replaced1 - reference) <= 2 * eps2
        classes = {}
        for is_const1, is_const2 in product((False, True), repeat=2):
            select = np.outer(const1 == is_const1, const2 == is_const2)
            classes[f"{is_const1},{is_const2}"] = Fraction(int(reference_num[select].sum()), den1 * den2)
        assert classes["True,True"] == p
        assert classes["False,False"] <= p
        bound_mixed = Fraction(p) ** (2 - rank_mod(B, p))
        assert classes["True,False"] <= bound_mixed
        assert classes["False,True"] <= bound_mixed
        direct = 0
        for C2 in C2s:
            a = np.block([[C1, B], [B.T, C2]]) - lam * np.eye(N1 + N2, dtype=np.int64)
            v = np.r_[np.full(N1, B1), np.full(N2, -c1)]
            assert np.all(a @ v == 0)
            direct += p ** (N1 + N2 - rank_mod(a, p))
        assert actual == Fraction(direct, len(C2s))
        records.append({"p": p, "lambda": lam, "actual": str(actual),
                        "reference": str(reference),
                        "reference_classes": {k: str(v) for k, v in classes.items()},
                        "status": "PASS"})

report = {"parameters": [N1, N2, A1, A2, B1, B2], "records": records,
          "scope": "Exact finite matching-model algebra check; small internal block is multigraph-only."}
target = Path(__file__).resolve().parent / "UNEQUAL_MOMENT_CHECKS.json"
target.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
