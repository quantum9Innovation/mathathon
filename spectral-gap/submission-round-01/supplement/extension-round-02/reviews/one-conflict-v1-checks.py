from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, factorial, prod
from pathlib import Path
import json
import random


ROOT = Path(__file__).resolve().parent


@lru_cache(None)
def permutations_of(n):
    return tuple(permutations(range(n)))


def falling(n, j):
    return factorial(n) // factorial(n - j)


@lru_cache(None)
def positive_polynomial(n, j, s):
    if j == 0:
        return 1
    return sum(
        comb(j - 1, ell - 1)
        * ((ell - 1) * n + s)
        * factorial(ell - 1)
        * positive_polynomial(n, j - ell, s)
        for ell in range(1, j + 1)
    )


def kernel(n, j, s):
    return Fraction(n**s * positive_polynomial(n, j, s), falling(n, j + s))


def direct_expectation(n, pattern):
    colors = sorted({e[0] for e in pattern})
    answer = Fraction(1)
    for color in colors:
        cells = [e for e in pattern if e[0] == color]
        powers = sum(e[3] for e in cells)
        numerator = 0
        for sigma in permutations_of(n):
            value = 1
            for _, row, col, p, q in cells:
                indicator = int(sigma[row] == col)
                if q and not indicator:
                    value = 0
                    break
                value *= (n * indicator - 1) ** p
            numerator += value
        answer *= Fraction(numerator, factorial(n) * n**powers)
    return answer


def classify(pattern):
    h = 0
    b = 0
    for i, (color, row, col, p, q) in enumerate(pattern):
        if (p, q) != (1, 0):
            continue
        conflict = any(
            i != j and other[0] == color and (other[1] == row or other[2] == col)
            for j, other in enumerate(pattern)
        )
        if conflict:
            b += 1
        else:
            h += 1
    return h, b


def envelope(n, a, h, b):
    return Fraction(
        2 ** (b - 1) * positive_polynomial(n, h, a - h - 1),
        n ** (h + 1) * falling(n, a - 1),
    )


counts = Counter()
examples = []


def check(n, pattern, family):
    h, b = classify(pattern)
    if b == 0:
        return
    actual = direct_expectation(n, pattern)
    bound = envelope(n, len(pattern), h, b)
    assert abs(actual) <= bound, (n, pattern, h, b, actual, bound)
    counts[family + ("_b1" if b == 1 else "_b_multiple")] += 1
    if len(pattern) == n:
        counts["full_support"] += 1
    if any(p >= 2 or (p >= 1 and q >= 1) for _, _, _, p, q in pattern):
        counts["repeated_or_mixed_powers"] += 1
    if len({e[0] for e in pattern}) >= 2:
        counts["multiple_colors"] += 1


choices = [(0, 1), (1, 0), (2, 0), (3, 0), (1, 2)]
for n in [2, 3]:
    cells = list(product(range(2), range(n), range(n)))
    for a in range(2, n + 1):
        for support in combinations(cells, a):
            for exponents in product(choices, repeat=a):
                pattern = [(*cell, *exponent) for cell, exponent in zip(support, exponents)]
                check(n, pattern, "exhaustive_two_colors_small")

for n in [4]:
    cells = list(product(range(1), range(n), range(n)))
    for a in range(2, n + 1):
        for support in combinations(cells, a):
            for exponents in product([(0, 1), (1, 0)], repeat=a):
                pattern = [(*cell, *exponent) for cell, exponent in zip(support, exponents)]
                check(n, pattern, "exhaustive_one_color_n4")

rng = random.Random(842019)
rich_choices = choices + [(5, 0), (7, 0), (2, 3), (4, 1), (0, 4)]
for n, trials in [(5, 2000), (6, 1200)]:
    cells = list(product(range(3), range(n), range(n)))
    for _ in range(trials):
        a = rng.randint(2, n)
        support = rng.sample(cells, a)
        exponents = [rng.choice(rich_choices) for _ in range(a)]
        pattern = [(*cell, *exponent) for cell, exponent in zip(support, exponents)]
        check(n, pattern, "sampled_three_colors")

for n in range(2, 9):
    for a in range(2, n + 1):
        for h in range(a - 1):
            r = a - h - 1
            pattern = [(0, 0, a - 1, 1, 0)]
            pattern += [(0, i, i, 0, 1) for i in range(r)]
            pattern += [(0, i, i, 1, 0) for i in range(r, a - 1)]
            assert classify(pattern) == (h, 1)
            actual = direct_expectation(n, pattern)
            bound = envelope(n, a, h, 1)
            assert actual == -bound, (n, a, h, actual, bound)
            counts["attainment"] += 1
            if n <= 4:
                examples.append(
                    {
                        "n": n,
                        "a": a,
                        "h": h,
                        "b": 1,
                        "pattern": pattern,
                        "expectation": str(actual),
                        "bound": str(bound),
                    }
                )

for n in range(2, 16):
    for s in range(n):
        for j in range(n - s):
            assert kernel(n, j + 1, s) == kernel(n, j, s + 1) - kernel(n, j, s)
            counts["kernel_difference"] += 1

for n in range(2, 9):
    for s in range(n + 1):
        dimension = n - s
        for j in range(dimension + 1):
            values = (
                prod(n * int(sigma[i] == i) - 1 for i in range(j))
                for sigma in permutations_of(dimension)
            )
            direct = Fraction(sum(values), factorial(dimension))
            polynomial = Fraction(positive_polynomial(n, j, s), falling(dimension, j))
            assert direct == polynomial, (n, j, s)
            counts["depleted_moment_direct"] += 1

selected_examples = [
    (4, [(0, 0, 3, 1, 0), (0, 1, 1, 1, 0)]),
    (4, [(0, 0, 3, 1, 0), (0, 1, 1, 1, 0), (0, 0, 0, 0, 1)]),
    (4, [(0, 0, 1, 1, 0), (0, 0, 0, 0, 1), (1, 0, 0, 1, 0), (1, 1, 1, 0, 1)]),
    (2, [(0, 0, 0, 1, 0), (0, 0, 1, 1, 0)]),
]
for n, pattern in selected_examples:
    h, b = classify(pattern)
    examples.append(
        {
            "n": n,
            "pattern": pattern,
            "h": h,
            "b": b,
            "expectation": str(direct_expectation(n, pattern)),
            "bound": str(envelope(n, len(pattern), h, b)) if b else None,
        }
    )

result = {
    "method": "Exact original-product evaluation over every permutation in each color, with independent colors multiplied afterward",
    "author_checkers_read_or_imported": False,
    "sample_seed": 842019,
    "counts": dict(counts),
    "examples": examples,
    "status": "all checks passed",
}
(ROOT / "one-conflict-v1-check-results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
