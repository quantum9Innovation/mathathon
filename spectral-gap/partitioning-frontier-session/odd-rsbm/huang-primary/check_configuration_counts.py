"""Exact small pairing checks; these do not prove asymptotic mixing."""
from collections import Counter
from functools import lru_cache
from itertools import product
from math import factorial
import json


def pairings(items):
    if not items:
        yield ()
        return
    first = items[0]
    for j in range(1, len(items)):
        rest = items[1:j] + items[j + 1:]
        for tail in pairings(rest):
            yield ((first, items[j]),) + tail


def check_case(n, d, p, inputs):
    graphs = Counter()
    total = 0
    for pairs in pairings(tuple(range(n * d))):
        matrix = [0] * (n * n)
        for x, y in pairs:
            a, b = x // d, y // d
            matrix[a * n + b] += 1
            matrix[b * n + a] += 1  # Loops contribute two.
        graphs[tuple(matrix)] += 1
        total += 1
    expected_total = factorial(n * d) // (
        2 ** (n * d // 2) * factorial(n * d // 2))
    assert total == expected_total
    for matrix in graphs:
        assert all(sum(matrix[i * n:(i + 1) * n]) == d for i in range(n))

    row_polynomials = [Counter() for _ in range(p)]
    for labels in product(range(p), repeat=d):
        counts = tuple(labels.count(a) for a in range(p))
        row_polynomials[sum(labels) % p][counts] += 1

    @lru_cache(None)
    def row_product(targets):
        polynomial = Counter({(0,) * p: 1})
        for t in targets:
            next_polynomial = Counter()
            for a, ca in polynomial.items():
                for b, cb in row_polynomials[t].items():
                    next_polynomial[tuple(x + y for x, y in zip(a, b))] += ca * cb
            polynomial = next_polynomial
        return polynomial

    comparisons = 0
    for q in inputs:
        observed = Counter()
        types = set()
        for matrix, multiplicity in graphs.items():
            target = tuple(sum(matrix[i * n + j] * q[j] for j in range(n)) % p
                           for i in range(n))
            color_matrix = [0] * (p * p)
            for i in range(n):
                for j in range(n):
                    color_matrix[q[i] * p + q[j]] += matrix[i * n + j]
            color_matrix = tuple(color_matrix)
            observed[(target, color_matrix)] += multiplicity
            types.add(color_matrix)
            assert sum(target) % p == d * sum(q) % p
        for target in product(range(p), repeat=n):
            polynomials = []
            for a in range(p):
                ts = tuple(sorted(target[v] for v in range(n) if q[v] == a))
                polynomials.append(row_product(ts))
            for matrix in types:
                k_factor = 1
                for a in range(p):
                    diagonal = matrix[a * p + a]
                    assert diagonal % 2 == 0
                    k_factor *= factorial(diagonal) // (
                        2 ** (diagonal // 2) * factorial(diagonal // 2))
                    for b in range(a + 1, p):
                        k_factor *= factorial(matrix[a * p + b])
                predicted = k_factor
                for a in range(p):
                    predicted *= polynomials[a][matrix[a * p:(a + 1) * p]]
                actual = observed[(target, matrix)]
                assert predicted == actual, (n, d, p, q, target, matrix, predicted, actual)
                comparisons += 1
        assert sum(observed.values()) == total
    return {"n": n, "d": d, "p": p, "pairings": total,
            "distinct_adjacencies": len(graphs), "inputs": len(inputs),
            "exact_target_type_comparisons": comparisons}


def main():
    cases = [
        check_case(3, 4, 3, [(0, 0, 0), (1, 1, 1), (0, 0, 1),
                             (0, 1, 1), (0, 1, 2), (1, 1, 2)]),
        check_case(4, 3, 3, [(0, 0, 0, 0), (1, 1, 1, 1), (0, 0, 0, 1),
                             (0, 0, 1, 1), (0, 1, 2, 0), (0, 1, 2, 1)]),
    ]
    print(json.dumps({"status": "PASS", "arithmetic": "exact integers",
                      "scope": "Enumeration identity only; no asymptotic or timing claim",
                      "cases": cases}, indent=2))


if __name__ == "__main__":
    main()
