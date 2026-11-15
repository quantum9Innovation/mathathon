from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import factorial
from pathlib import Path
import json
import random


def falling(n, j):
    answer = 1
    for i in range(j):
        answer *= n - i
    return answer


@lru_cache(None)
def coefficient_polynomial(n, s, j):
    coefficients = [Fraction(1)]
    for degree in range(1, j + 1):
        coefficients.append(sum(
            (((ell - 1) * n + s) * coefficients[degree - ell]
             for ell in range(1, degree + 1)), Fraction(0)) / degree)
    answer = factorial(j) * coefficients[j]
    assert answer.denominator == 1
    return answer.numerator


def moment(n, s, j):
    return Fraction(coefficient_polynomial(n, s, j), falling(n - s, j))


def kernel(n, s, j):
    return Fraction(n**s * coefficient_polynomial(n, s, j), falling(n, j + s))


@lru_cache(None)
def permutation_list(n):
    return tuple(permutations(range(n)))


def original_expectation(n, factors):
    result = Fraction(1)
    for color in sorted({c for c, _, _, _, _ in factors}):
        local = [entry for entry in factors if entry[0] == color]
        total = Fraction(0)
        for sigma in permutation_list(n):
            value = Fraction(1)
            for _, row, column, p, q in local:
                indicator = int(sigma[row] == column)
                value *= (Fraction(indicator) - Fraction(1, n))**p * indicator**q
            total += value
        result *= total / factorial(n)
    return result


def pattern_counts(factors):
    h = b = 0
    for index, (color, row, column, p, q) in enumerate(factors):
        if (p, q) != (1, 0):
            continue
        conflict = any(index != other and color == c and (row == r or column == s)
                       for other, (c, r, s, _, _) in enumerate(factors))
        b += int(conflict)
        h += int(not conflict)
    return h, b


counts = {'depleted_moments_by_permutations': 0, 'merges': 0,
          'moment_monotonicity': 0, 'kernel_monotonicity': 0,
          'affine_weights': 0, 'attaining_products': 0,
          'sampled_original_products': 0}

for n in range(2, 9):
    for s in range(n + 1):
        size = n - s
        totals = [0] * (size + 1)
        for sigma in permutation_list(size):
            value = 1
            totals[0] += value
            for j in range(1, size + 1):
                value *= n * int(sigma[j - 1] == j - 1) - 1
                totals[j] += value
        for j, total in enumerate(totals):
            assert Fraction(total, factorial(size)) == moment(n, s, j)
            counts['depleted_moments_by_permutations'] += 1

for n in range(2, 15):
    for j in range(n + 1):
        for s in range(n - j):
            assert moment(n, s, j) <= moment(n, s + 1, j)
            assert kernel(n, s, j) <= kernel(n, s + 1, j)
            counts['moment_monotonicity'] += 1
            counts['kernel_monotonicity'] += 1
    for j1 in range(n + 1):
        for s1 in range(n - j1 + 1):
            for j2 in range(n - j1 - s1 + 1):
                for s2 in range(n - j1 - s1 - j2 + 1):
                    assert kernel(n, s1, j1) * kernel(n, s2, j2) <= kernel(n, s1 + s2, j1 + j2)
                    counts['merges'] += 1

for n in range(2, 41):
    for p in range(41):
        for q in range(4):
            if p + q == 0:
                continue
            c = (-Fraction(1, n))**p if q == 0 else Fraction(0)
            at_one = (1 - Fraction(1, n))**p
            d = at_one - c
            weight = d + n * abs(c)
            assert d >= 0
            if (p, q) == (1, 0):
                assert weight == 2
            else:
                assert weight <= 1
            counts['affine_weights'] += 1

for n in range(2, 7):
    for a in range(1, n + 1):
        for h in range(a + 1):
            factors = [(0, i, i, int(i < h), int(i >= h)) for i in range(a)]
            exact = original_expectation(n, factors)
            target = Fraction(coefficient_polynomial(n, a - h, h), n**h * falling(n, a))
            assert exact == target
            counts['attaining_products'] += 1

rng = random.Random(743812)
exponents = [(0, 1), (1, 0), (2, 0), (3, 0), (8, 0), (11, 0), (2, 3), (5, 2)]
for n in range(2, 6):
    for color_count in [1, 2, 3]:
        cells = [(c, i, j) for c in range(color_count) for i in range(n) for j in range(n)]
        for _ in range(80):
            a = rng.randint(1, n)
            selected = rng.sample(cells, a)
            factors = [(*cell, *rng.choice(exponents)) for cell in selected]
            h, b = pattern_counts(factors)
            bound = Fraction(2**b * coefficient_polynomial(n, a - h, h), n**h * falling(n, a))
            assert abs(original_expectation(n, factors)) <= bound
            counts['sampled_original_products'] += 1

result = {
    'status': 'passed',
    'arithmetic': 'exact rational and integer',
    'method': 'Independent coefficient recurrence and direct evaluation of original factors over permutations',
    'checks': counts,
    'ranges': {
        'depleted_moments': '2<=n<=8, every 0<=s<=n and 0<=j<=n-s, including full depletion',
        'monotonicity_and_merging': '2<=n<=14, every permitted index combination',
        'affine_weights': '2<=n<=40, 0<=p<=40, 0<=q<=3, p+q>=1',
        'attainment': '2<=n<=6, all 1<=a<=n and 0<=h<=a',
        'mixed_products': '2<=n<=5, one to three colors, 80 seeded samples per pair, support at most n',
    },
    'role': 'Finite corroboration only, not a substitute for the audited proofs',
}
Path(__file__).with_name('mixed-by-saddle-check-results-v1.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
