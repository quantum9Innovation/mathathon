"""Exhaustive small-N checks of the derived two-block moment argument."""
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import numpy as np

N, internal, cross = 4, 3, 2
matchings = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
matrices = []
for chosen in product(range(3), repeat=internal):
    a = np.zeros((N, N), dtype=np.int64)
    for which in chosen:
        for i, j in matchings[which]:
            a[i, j] += 1
            a[j, i] += 1
    matrices.append(a)


def rank_mod(a, p):
    b = [[int(x) % p for x in row] for row in a]
    rank = 0
    for j in range(len(b[0])):
        pivot = next((i for i in range(rank, len(b)) if b[i][j]), None)
        if pivot is None:
            continue
        b[rank], b[pivot] = b[pivot], b[rank]
        inv = pow(b[rank][j], -1, p)
        b[rank] = [x * inv % p for x in b[rank]]
        for i in range(rank + 1, len(b)):
            q = b[i][j]
            b[i] = [(x - q * y) % p for x, y in zip(b[i], b[rank])]
        rank += 1
        if rank == len(b):
            break
    return rank


records = []
for prime in (3, 5):
    vectors = np.array(list(product(range(prime), repeat=N)), dtype=np.int64)
    qcount = len(vectors)
    powers = prime ** np.arange(N - 1, -1, -1)
    sums = vectors.sum(axis=1) % prime
    constant = np.all(vectors == vectors[:, :1], axis=1)
    ref_den = prime ** (N - 1)
    sample_den = len(matrices)
    count = np.zeros((qcount, qcount), dtype=np.int64)
    for matrix in matrices:
        targets = vectors @ matrix.T % prime
        indices = targets @ powers
        count[np.arange(qcount), indices] += 1
    ref = np.zeros_like(count)
    for i, x in enumerate(vectors):
        if constant[i]:
            ref[i, ((internal * x) % prime) @ powers] = ref_den
        else:
            ref[i, sums == internal * sums[i] % prime] = 1
    errors_num = np.max(abs(count * ref_den - ref * sample_den), axis=1)
    epsilon = Fraction(int(errors_num.sum()), sample_den * ref_den)
    # Every reference affine expectation is <=2, independently of epsilon.
    delta = internal - cross
    for shift in vectors:
        indices = ((delta * vectors + shift) % prime) @ powers
        actual_sum = int(count[np.arange(qcount), indices].sum())
        reference_sum = int(ref[np.arange(qcount), indices].sum())
        assert Fraction(actual_sum, sample_den) <= 2 + epsilon
        assert Fraction(reference_sum, ref_den) <= 2

    for cross in (1, 2):
        delta = internal - cross
        b = np.zeros((N, N), dtype=np.int64)
        for i in range(N):
            for offset in range(cross):
                b[i, (i + offset) % N] = 1
        by = vectors @ b.T
        btx = vectors @ b
        ix1 = ((delta * vectors[:, None, :] - by[None, :, :]) % prime) @ powers
        # Rows y, columns x before transposing.
        ix2 = ((delta * vectors[:, None, :] - btx[None, :, :]) % prime) @ powers
        p1 = count[np.arange(qcount)[:, None], ix1]
        p2 = count[np.arange(qcount)[:, None], ix2].T
        u1 = ref[np.arange(qcount)[:, None], ix1]
        u2 = ref[np.arange(qcount)[:, None], ix2].T
        actual = Fraction(int((p1 * p2).sum()), sample_den ** 2)
        first_replacement = Fraction(int((u1 * p2).sum()), ref_den * sample_den)
        reference = Fraction(int((u1 * u2).sum()), ref_den ** 2)
        assert abs(actual - first_replacement) <= (2 + epsilon) * epsilon
        assert abs(first_replacement - reference) <= (2 + 2 * epsilon) * epsilon
        assert abs(actual - reference) <= 4 * epsilon + 3 * epsilon * epsilon
        rank = rank_mod(b, prime)
        assert reference <= 2 * prime + 2 * Fraction(prime) ** (2 - rank)
        # Independently count actual kernels by rank over every pair of matching unions.
        direct_sum = 0
        for c1, c2 in product(matrices, repeat=2):
            a = np.block([[c1, b], [b.T, c2]]) - delta * np.eye(2 * N, dtype=np.int64)
            direct_sum += prime ** (2 * N - rank_mod(a, prime))
        assert actual == Fraction(direct_sum, sample_den ** 2)
        records.append({
            "prime": prime, "cross_degree": cross, "rank_B": rank,
            "epsilon": str(epsilon), "exact_actual_kernel_expectation": str(actual),
            "exact_reference_sum": str(reference), "status": "PASS",
        })

report = {"block_size": N, "internal_degree": internal,
          "matching_union_samples_with_multiplicity": len(matrices),
          "records": records,
          "scope": "Finite exact diagnostic only; asymptotic mixing is the cited theorem."}
destination = Path(__file__).resolve().parent / "MESZAROS_MOMENT_CHECKS.json"
destination.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
