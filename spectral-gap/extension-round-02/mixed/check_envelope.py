from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, factorial
from pathlib import Path
import json
import random


def falling(n, k):
    result = 1
    for j in range(k):
        result *= n - j
    return result


@lru_cache(None)
def polynomial(n, r, h):
    if h == 0:
        return 1
    return sum(
        comb(h - 1, size - 1)
        * ((size - 1) * n + r)
        * factorial(size - 1)
        * polynomial(n, r, h - size)
        for size in range(1, h + 1)
    )


def mu_polynomial(n, r, h):
    return Fraction(polynomial(n, r, h), falling(n - r, h))


def mu_expansion(n, r, h):
    return sum(
        (
            Fraction(comb(h, j) * (-1) ** (h - j) * n**j, falling(n - r, j))
            for j in range(h + 1)
        ),
        Fraction(0),
    )


def kernel(n, h, r):
    return Fraction(n**r * polynomial(n, r, h), falling(n, h + r))


@lru_cache(None)
def all_permutations(n):
    return list(permutations(range(n)))


def counts(cells, exponents):
    h = 0
    b = 0
    for index, (color, row, column) in enumerate(cells):
        if exponents[index] != (1, 0):
            continue
        consistent = not any(
            other_index != index
            and color == other_color
            and (row == other_row or column == other_column)
            for other_index, (other_color, other_row, other_column) in enumerate(cells)
        )
        h += int(consistent)
        b += int(not consistent)
    return h, b


def expectation(n, cells, exponents):
    by_color = defaultdict(list)
    for cell, exponent in zip(cells, exponents):
        color, row, column = cell
        by_color[color].append((row, column, exponent))
    result = Fraction(1)
    for entries in by_color.values():
        centered_power = sum(exponent[0] for _, _, exponent in entries)
        numerator = 0
        for sigma in all_permutations(n):
            value = 1
            for row, column, (p, q) in entries:
                indicator = int(sigma[row] == column)
                if q and not indicator:
                    value = 0
                    break
                value *= (n * indicator - 1) ** p
            numerator += value
        result *= Fraction(numerator, factorial(n) * n**centered_power)
    return result


def inspect_pattern(n, cells, exponents):
    h, b = counts(cells, exponents)
    a = len(cells)
    observed = abs(expectation(n, cells, exponents))
    bound = Fraction(2**b * polynomial(n, a - h, h), n**h * falling(n, a))
    assert observed <= bound, (n, cells, exponents, observed, bound)
    return a, h, b, observed, bound


checks = {
    "polynomial_identity": 0,
    "moment_monotonicity": 0,
    "kernel_monotonicity": 0,
    "kernel_merging": 0,
    "exhaustive_mixed_patterns": 0,
    "sampled_mixed_patterns": 0,
    "attainment": 0,
}

for n in range(2, 33):
    for r in range(n + 1):
        for h in range(n - r + 1):
            assert mu_polynomial(n, r, h) == mu_expansion(n, r, h)
            checks["polynomial_identity"] += 1
            if r + h < n:
                assert mu_polynomial(n, r, h) <= mu_polynomial(n, r + 1, h)
                checks["moment_monotonicity"] += 1
                assert kernel(n, h, r) <= kernel(n, h, r + 1)
                checks["kernel_monotonicity"] += 1

for n in range(2, 17):
    for a_1 in range(n + 1):
        for h_1 in range(a_1 + 1):
            r_1 = a_1 - h_1
            for a_2 in range(n - a_1 + 1):
                for h_2 in range(a_2 + 1):
                    r_2 = a_2 - h_2
                    assert (
                        kernel(n, h_1, r_1) * kernel(n, h_2, r_2)
                        <= kernel(n, h_1 + h_2, r_1 + r_2)
                    )
                    checks["kernel_merging"] += 1

exponent_choices = [(0, 1), (1, 0), (2, 0), (3, 0), (4, 0), (1, 1), (2, 3)]
for n, color_count in [(2, 1), (2, 2), (3, 1)]:
    universe = list(product(range(color_count), range(n), range(n)))
    for a in range(1, n + 1):
        for cells in combinations(universe, a):
            for exponents in product(exponent_choices, repeat=a):
                inspect_pattern(n, cells, exponents)
                checks["exhaustive_mixed_patterns"] += 1

rng = random.Random(21003)
for n in range(4, 8):
    for color_count in [1, 2, 3]:
        universe = list(product(range(color_count), range(n), range(n)))
        for _ in range(250):
            a = rng.randrange(1, n + 1)
            cells = rng.sample(universe, a)
            exponents = [rng.choice(exponent_choices) for _ in cells]
            inspect_pattern(n, cells, exponents)
            checks["sampled_mixed_patterns"] += 1

for n in range(2, 8):
    for a in range(1, n + 1):
        cells = [(0, i, i) for i in range(a)]
        for h in range(a + 1):
            exponents = [(1, 0)] * h + [(0, 1)] * (a - h)
            _, observed_h, b, observed, bound = inspect_pattern(n, cells, exponents)
            assert observed_h == h and b == 0 and observed == bound
            checks["attainment"] += 1

result = {
    "status": "passed",
    "arithmetic": "exact rational",
    "checks": checks,
    "ranges": {
        "polynomial_and_monotonicity": "2 <= n <= 32, all 0 <= r,h with r+h <= n",
        "merging": "2 <= n <= 16, all nonnegative local indices with total at most n",
        "exhaustive_patterns": [
            "n=2 with one color, support size at most n",
            "n=2 with two colors, support size at most n",
            "n=3 with one color, support size at most n",
        ],
        "sampled_patterns": "4 <= n <= 7, one to three colors, 250 cases for each pair",
        "exponent_choices": exponent_choices,
        "attainment": "2 <= n <= 7, all 1 <= a <= n and 0 <= h <= a",
    },
    "limits": [
        "Finite checks do not prove the general statements",
        "No historical priority conclusion follows from these checks",
        "The scalar corollary and asymptotic statements rely on their written proofs",
    ],
}
destination = Path(__file__).with_name("envelope-checks-v1.json")
destination.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
