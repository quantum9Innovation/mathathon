from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, factorial
from pathlib import Path
import json
import random


def falling(n, k):
    value = 1
    for j in range(k):
        value *= n - j
    return value


@lru_cache(None)
def polynomial(n, r, h):
    if h == 0:
        return 1
    return sum(
        comb(h - 1, j - 1)
        * ((j - 1) * n + r)
        * factorial(j - 1)
        * polynomial(n, r, h - j)
        for j in range(1, h + 1)
    )


@lru_cache(None)
def permutation_list(n):
    return tuple(permutations(range(n)))


def count_singletons(cells, powers):
    h = b = 0
    for i, ((c, u, v), power) in enumerate(zip(cells, powers)):
        if power != (1, 0):
            continue
        conflict = any(
            j != i and c == c1 and (u == u1 or v == v1)
            for j, (c1, u1, v1) in enumerate(cells)
        )
        if conflict:
            b += 1
        else:
            h += 1
    return h, b


def direct_expectation(n, cells, powers):
    by_color = defaultdict(list)
    for (c, u, v), (p, q) in zip(cells, powers):
        by_color[c].append((u, v, p, q))
    result = Fraction(1)
    for entries in by_color.values():
        total = 0
        degree = sum(p for u, v, p, q in entries)
        for sigma in permutation_list(n):
            value = 1
            for u, v, p, q in entries:
                indicator = int(sigma[u] == v)
                if q and not indicator:
                    value = 0
                    break
                value *= (n * indicator - 1) ** p
            total += value
        result *= Fraction(total, factorial(n) * n**degree)
    return result


counts = defaultdict(int)
ratios = defaultdict(Fraction)


def inspect(n, cells, powers, category):
    h, b = count_singletons(cells, powers)
    if b == 0:
        return
    a = len(cells)
    bound = Fraction(2 ** (b - 1) * polynomial(n, a - h - 1, h), n ** (h + 1) * falling(n, a - 1))
    actual = abs(direct_expectation(n, cells, powers))
    assert actual <= bound, (n, cells, powers, h, b, actual, bound)
    key = category + ('_b1' if b == 1 else '_b_multiple')
    counts[key] += 1
    ratios[key] = max(ratios[key], actual / bound)


choices = [(0, 1), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (1, 1), (2, 3)]
for n, colors in [(2, 1), (2, 2), (3, 1), (3, 2)]:
    universe = list(product(range(colors), range(n), range(n)))
    for a in range(2, n + 1):
        for cells in combinations(universe, a):
            for powers in product(choices, repeat=a):
                inspect(n, cells, powers, 'exhaustive')

rng = random.Random(210032)
for n in range(4, 7):
    for colors in range(1, 4):
        universe = list(product(range(colors), range(n), range(n)))
        for _ in range(400):
            a = rng.randrange(2, n + 1)
            cells = [(0, 0, 0), (0, 0, 1)]
            available = [cell for cell in universe if cell not in cells]
            cells += rng.sample(available, a - 2)
            powers = [(1, 0)] + [rng.choice(choices) for cell in cells[1:]]
            inspect(n, cells, powers, 'sampled')

result = {
    'status': 'passed',
    'arithmetic': 'exact rational',
    'expectation_method': 'Direct enumeration of uniform permutations separately in each independent color',
    'counts': dict(counts),
    'largest_observed_ratio': {key: str(value) for key, value in ratios.items()},
    'ranges': {
        'exhaustive': 'n=2,3 with one or two colors, every support size at most n, every listed power assignment, retaining b>=1',
        'sampled': '4<=n<=6 with one to three colors, 400 forced-conflict patterns for each pair',
        'powers': choices,
    },
    'limitations': ['Finite enumeration is corroboration only'],
}
Path(__file__).with_name('general-checks-v1.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
