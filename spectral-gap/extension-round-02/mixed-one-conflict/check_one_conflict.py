from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import comb, factorial
from pathlib import Path
import json
import random


def falling(n, k):
    value = 1
    for i in range(k):
        value *= n - i
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


def singleton_counts(cells, powers):
    h = b = 0
    for i, ((color, row, column), (p, q)) in enumerate(zip(cells, powers)):
        if (p, q) != (1, 0):
            continue
        conflict = any(
            j != i and color == c and (row == u or column == v)
            for j, (c, u, v) in enumerate(cells)
        )
        h += not conflict
        b += conflict
    return h, b


def expectation(n, cells, powers):
    entries = []
    for cell, (p, q) in zip(cells, powers):
        at_zero = Fraction((-1) ** p, n**p) if q == 0 else Fraction(0)
        at_one = Fraction((n - 1) ** p, n**p)
        entries.append((cell, at_zero, at_one - at_zero))
    value = Fraction(0)
    for chosen in product((False, True), repeat=len(cells)):
        coefficient = Fraction(1)
        rows = defaultdict(set)
        columns = defaultdict(set)
        selected = defaultdict(int)
        valid = True
        for take, (cell, c, d) in zip(chosen, entries):
            coefficient *= d if take else c
            if not coefficient:
                valid = False
                break
            if take:
                color, row, column = cell
                if row in rows[color] or column in columns[color]:
                    valid = False
                    break
                rows[color].add(row)
                columns[color].add(column)
                selected[color] += 1
        if valid:
            for count in selected.values():
                coefficient /= falling(n, count)
            value += coefficient
    return value


counts = defaultdict(int)
largest_ratios = {}
failure = None


def inspect(n, cells, powers, category):
    global failure
    h, b = singleton_counts(cells, powers)
    if b != 1:
        return
    a = len(cells)
    r = a - h - 1
    bound = Fraction(polynomial(n, r, h), n ** (h + 1) * falling(n, a - 1))
    observed = abs(expectation(n, cells, powers))
    counts[category] += 1
    assert bound > 0
    ratio = observed / bound
    largest_ratios[category] = max(largest_ratios.get(category, Fraction(0)), ratio)
    if observed > bound:
        failure = {
            'n': n,
            'cells': cells,
            'powers': powers,
            'h': h,
            'b': b,
            'observed': str(observed),
            'bound': str(bound),
        }
        raise AssertionError(failure)


non_singleton_choices = [(0, 1), (2, 0), (3, 0), (4, 0), (5, 0), (1, 1), (2, 3)]
all_choices = [(1, 0)] + non_singleton_choices
for n, colors in [(2, 1), (2, 2), (3, 1), (3, 2)]:
    universe = list(product(range(colors), range(n), range(n)))
    for a in range(2, n + 1):
        for cells in combinations(universe, a):
            for powers in product(all_choices, repeat=a):
                inspect(n, cells, powers, 'exhaustive')

rng = random.Random(210031)
for n in range(4, 11):
    for colors in range(1, 4):
        for _ in range(800):
            a = rng.randrange(2, n + 1)
            distinguished = (0, 0, 0)
            neighbor = (0, 0, 1)
            universe = list(product(range(colors), range(n), range(n)))
            universe.remove(distinguished)
            universe.remove(neighbor)
            cells = [distinguished, neighbor] + rng.sample(universe, a - 2)
            powers = [(1, 0), rng.choice(non_singleton_choices)]
            for i in range(2, a):
                color, row, column = cells[i]
                consistent = not any(
                    j != i and color == c and (row == u or column == v)
                    for j, (c, u, v) in enumerate(cells)
                )
                choices = all_choices if consistent else non_singleton_choices
                powers.append(rng.choice(choices))
            inspect(n, cells, powers, 'sampled')

for n in range(2, 13):
    for a in range(2, n + 1):
        for h in range(a - 1):
            cells = [(0, 0, a - 1)] + [(0, i, i) for i in range(a - 1)]
            powers = [(1, 0)] + [(0, 1)] * (a - 1 - h) + [(1, 0)] * h
            inspect(n, cells, powers, 'attainment')
            observed_h, observed_b = singleton_counts(cells, powers)
            assert (observed_h, observed_b) == (h, 1)
            bound = Fraction(polynomial(n, a - h - 1, h), n ** (h + 1) * falling(n, a - 1))
            assert abs(expectation(n, cells, powers)) == bound

for n in range(2, 41):
    for h in range(n):
        for r in range(n - h):
            lhs = Fraction(n**r * polynomial(n, r, h + 1), falling(n, h + r + 1))
            rhs = Fraction(n**(r + 1) * polynomial(n, r + 1, h), falling(n, h + r + 1))
            rhs -= Fraction(n**r * polynomial(n, r, h), falling(n, h + r))
            assert lhs == rhs
            counts['kernel_difference_identity'] += 1

result = {
    'status': 'passed',
    'arithmetic': 'exact rational',
    'counts': dict(counts),
    'largest_observed_ratio': {key: str(value) for key, value in largest_ratios.items()},
    'failure': failure,
    'ranges': {
        'exhaustive': 'n=2,3 with one or two colors, every support of size at most n and every listed power assignment, retaining b=1',
        'sampled': '4<=n<=10, one to three colors, 800 forced-conflict patterns for each pair',
        'attainment': '2<=n<=12, every 2<=a<=n and 0<=h<=a-2',
        'kernel_identity': '2<=n<=40, all h,r>=0 with h+r+1<=n',
        'power_choices': all_choices,
    },
    'limitations': ['Finite checks do not prove the candidate inequality or any historical priority claim'],
}
destination = Path(__file__).with_name('checks-v1.json')
destination.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
