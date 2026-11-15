#!/usr/bin/env python3
"""Exact twelve-vertex adaptive-cross-matching witness; standard library only."""

from fractions import Fraction
import json
from pathlib import Path


def matmul(a, b):
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def rank_q(a):
    a = [[Fraction(x) for x in row] for row in a]
    row = 0
    for col in range(len(a[0])):
        pivot = next((r for r in range(row, len(a)) if a[r][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        divisor = a[row][col]
        a[row] = [x / divisor for x in a[row]]
        for r in range(row + 1, len(a)):
            factor = a[r][col]
            if factor:
                a[r] = [x - factor * y for x, y in zip(a[r], a[row])]
        row += 1
    return row


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def main():
    n = 12
    edges = set()

    def edge(u, v):
        assert u != v
        e = tuple(sorted((u, v)))
        assert e not in edges
        edges.add(e)

    for start in [0, 3, 6, 9]:
        for i in range(3):
            edge(start + i, start + (i + 1) % 3)
    for i in range(3):
        edge(i, i + 3)
        edge(i + 6, i + 9)
        edge(i, i + 9)
        edge(i + 3, i + 6)

    a = [[0] * n for _ in range(n)]
    for u, v in edges:
        a[u][v] = a[v][u] = 1
    assert len(edges) == 24
    assert all(sum(row) == 4 for row in a)
    sigma = [1 if i < 6 else -1 for i in range(n)]
    sigma_new = [1 if 3 <= i < 9 else -1 for i in range(n)]
    for signs in [sigma, sigma_new]:
        assert sum(signs) == 0
        for i in range(n):
            same = sum(a[i][j] for j in range(n) if signs[j] == signs[i])
            cross = sum(a[i][j] for j in range(n) if signs[j] != signs[i])
            assert (same, cross) == (3, 1)
            assert sum(a[i][j] * signs[j] for j in range(n)) == 2 * signs[i]
    assert sum(x * y for x, y in zip(sigma, sigma_new)) == 0
    shifted = [[a[i][j] - (2 if i == j else 0) for j in range(n)] for i in range(n)]
    nullity = n - rank_q(shifted)
    assert nullity == 2

    # c[k] is the coefficient of z^(n-k). Newton identities are exact here.
    power = [[int(i == j) for j in range(n)] for i in range(n)]
    traces = [0]
    for _ in range(n):
        power = matmul(power, a)
        traces.append(sum(power[i][i] for i in range(n)))
    coeffs = [1]
    for k in range(1, n + 1):
        numerator = -sum(coeffs[k - i] * traces[i] for i in range(1, k + 1))
        assert numerator % k == 0
        coeffs.append(numerator // k)
    spectrum = [(4, 1), (2, 2), (1, 2), (0, 1), (-1, 4), (-3, 2)]
    predicted = [1]
    for eigenvalue, multiplicity in spectrum:
        for _ in range(multiplicity):
            predicted = poly_mul(predicted, [1, -eigenvalue])
    assert coeffs == predicted
    result = {
        "status": "PASS",
        "vertices": n,
        "edges": sorted(edges),
        "degrees": [sum(row) for row in a],
        "original_plus_block": [i for i, s in enumerate(sigma) if s == 1],
        "alternative_plus_block": [i for i, s in enumerate(sigma_new) if s == 1],
        "same_cross_degree_both_partitions": [3, 1],
        "sign_inner_product": sum(x * y for x, y in zip(sigma, sigma_new)),
        "rational_nullity_A_minus_2I": nullity,
        "characteristic_polynomial_descending": coeffs,
        "adjacency_spectrum_eigenvalue_multiplicity": spectrum,
        "uses_floating_point": False,
    }
    output = Path(__file__).with_suffix(".json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
