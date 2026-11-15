from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, factorial
from pathlib import Path
import json
import random


def falling(n, count):
    answer = 1
    for offset in range(count):
        answer *= n - offset
    return answer


@lru_cache(None)
def polynomial(n, exposure, degree):
    if degree == 0:
        return 1
    return sum(
        comb(degree - 1, size - 1)
        * ((size - 1) * n + exposure)
        * factorial(size - 1)
        * polynomial(n, exposure, degree - size)
        for size in range(1, degree + 1)
    )


def kernel(n, degree, exposure):
    return Fraction(
        n**exposure * polynomial(n, exposure, degree),
        falling(n, degree + exposure),
    )


def envelope(n, support_size, good_count, bad_count=2):
    exposure = support_size - good_count - 2
    return (
        2 ** (bad_count - 2)
        * (2 * kernel(n, good_count, exposure + 1) - kernel(n, good_count, exposure))
        / n**support_size
    )


def inconsistent_indices(cells):
    return {
        first
        for first, (color, row, column) in enumerate(cells)
        if any(
            first != second
            and color == other_color
            and (row == other_row or column == other_column)
            for second, (other_color, other_row, other_column) in enumerate(cells)
        )
    }


def counts(cells, powers):
    bad_indices = inconsistent_indices(cells)
    good = bad = 0
    for index, power in enumerate(powers):
        if power == (1, 0):
            if index in bad_indices:
                bad += 1
            else:
                good += 1
    return good, bad


@lru_cache(None)
def permutation_list(n):
    return tuple(permutations(range(n)))


@lru_cache(None)
def direct_color_moment(n, entries):
    total = 0
    degree = sum(p for row, column, p, q in entries)
    for sigma in permutation_list(n):
        term = 1
        for row, column, p, q in entries:
            indicator = int(sigma[row] == column)
            if q and not indicator:
                term = 0
                break
            term *= (n * indicator - 1) ** p
        total += term
    return Fraction(total, factorial(n) * n**degree)


def direct_moment(n, cells, powers):
    by_color = defaultdict(list)
    for (color, row, column), (p, q) in zip(cells, powers):
        by_color[color].append((row, column, p, q))
    answer = Fraction(1)
    for entries in by_color.values():
        answer *= direct_color_moment(n, tuple(sorted(entries)))
    return answer


def exact_indicator_expansion(n, cells, powers):
    coefficients = []
    degree = sum(p for p, q in powers)
    for p, q in powers:
        if q:
            coefficients.append((0, (n - 1) ** p))
        else:
            constant = (-1) ** p
            coefficients.append((constant, (n - 1) ** p - constant))
    answer = Fraction(0)
    for mask in range(1 << len(cells)):
        factor = 1
        rows = defaultdict(set)
        columns = defaultdict(set)
        compatible = True
        for index, ((color, row, column), (constant, linear)) in enumerate(zip(cells, coefficients)):
            selected = bool(mask & (1 << index))
            factor *= linear if selected else constant
            if not factor:
                break
            if selected:
                if row in rows[color] or column in columns[color]:
                    compatible = False
                    break
                rows[color].add(row)
                columns[color].add(column)
        if factor and compatible:
            denominator = 1
            for used in rows.values():
                denominator *= falling(n, len(used))
            answer += Fraction(factor, denominator)
    return answer / n**degree


statistics = defaultdict(int)
maximum_ratios = defaultdict(Fraction)
selected_classes = defaultdict(int)


def inspect(n, cells, powers, category, method):
    good, bad = counts(cells, powers)
    assert bad >= 2
    actual = abs(method(n, cells, powers))
    bound = envelope(n, len(cells), good, bad)
    assert actual <= bound, (n, cells, powers, good, bad, actual, bound)
    statistics[category] += 1
    maximum_ratios[category] = max(maximum_ratios[category], actual / bound)


power_choices = [(0, 1), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (1, 1), (2, 3)]
other_powers = [power for power in power_choices if power != (1, 0)]

for n, colors in [(2, 1), (2, 2), (3, 1), (3, 2)]:
    universe = list(product(range(colors), range(n), range(n)))
    for size in range(2, n + 1):
        for cells in combinations(universe, size):
            bad_indices = inconsistent_indices(cells)
            for retained in combinations(sorted(bad_indices), 2):
                remaining = [index for index in range(size) if index not in retained]
                choices = [other_powers if index in bad_indices else power_choices for index in remaining]
                for assignment in product(*choices):
                    powers = [(1, 0)] * size
                    for index, power in zip(remaining, assignment):
                        powers[index] = power
                    inspect(n, cells, powers, 'exhaustive_direct_b2', direct_moment)


def conflict(first, second):
    return first[0] == second[0] and (first[1] == second[1] or first[2] == second[2])


for n, colors in [(2, 1), (2, 2), (3, 1), (3, 2), (4, 1)]:
    universe = list(product(range(colors), range(n), range(n)))
    for size in range(2, n + 1):
        for cells in combinations(universe, size):
            bad_indices = inconsistent_indices(cells)
            good_indices = [index for index in range(size) if index not in bad_indices]
            for retained in combinations(sorted(bad_indices), 2):
                for good_mask in range(1 << len(good_indices)):
                    good = [index for offset, index in enumerate(good_indices) if good_mask & (1 << offset)]
                    rest = [index for index in range(size) if index not in retained and index not in good]
                    h = len(good)
                    exposure = len(rest)
                    base = 2 * kernel(n, h, exposure + 1) - kernel(n, h, exposure)
                    for mask in range(1 << len(rest)):
                        selected = [index for offset, index in enumerate(rest) if mask & (1 << offset)]
                        incompatible = any(conflict(cells[i], cells[j]) for i, j in combinations(selected, 2))
                        forced = [any(conflict(cells[index], cells[j]) for j in selected) for index in retained]
                        if incompatible:
                            category = 'incompatible_selected_set'
                        elif all(forced):
                            category = 'both_forced'
                        elif any(forced):
                            category = 'one_forced'
                        elif conflict(cells[retained[0]], cells[retained[1]]):
                            category = 'unforced_conflicting_pair'
                        else:
                            category = 'unforced_compatible_pair'
                        active = list(retained) + good + selected
                        active_cells = [cells[index] for index in active]
                        powers = [(1, 0)] * (2 + h) + [(0, 1)] * len(selected)
                        actual = abs(direct_moment(n, active_cells, powers))
                        bound = base / n ** (h + 2 + len(selected))
                        assert actual <= bound, (n, cells, retained, good, selected, category, actual, bound)
                        selected_classes[category] += 1
                        statistics['exhaustive_selected_supports'] += 1

rng = random.Random(210052)
large_other_powers = other_powers + [(17, 0), (32, 0), (101, 0), (17, 4)]
for n in range(4, 11):
    for colors in range(1, 4):
        universe = list(product(range(colors), range(n), range(n)))
        for trial in range(120):
            size = rng.randrange(2, n + 1)
            cells = [(0, 0, 0), (0, 0, 1)]
            available = [cell for cell in universe if cell not in cells]
            cells += rng.sample(available, size - 2)
            bad_indices = inconsistent_indices(cells)
            powers = [(1, 0), (1, 0)]
            for index in range(2, size):
                if index not in bad_indices and rng.random() < 0.5:
                    powers.append((1, 0))
                else:
                    powers.append(rng.choice(large_other_powers))
            inspect(n, cells, powers, 'sampled_exact_b2', exact_indicator_expansion)
            general_powers = [power if index < 2 or rng.random() < 0.55 else (1, 0) for index, power in enumerate(powers)]
            inspect(n, cells, general_powers, 'sampled_exact_general', exact_indicator_expansion)
            if n <= 6 and trial < 12:
                direct = direct_moment(n, cells, powers)
                expanded = exact_indicator_expansion(n, cells, powers)
                assert direct == expanded
                statistics['independent_method_comparisons'] += 1

for n in range(2, 23):
    for size in range(2, n + 1):
        for h in range(size - 1):
            exposure = size - h - 2
            actual = sum(
                Fraction(comb(h, chosen) * (-1) ** (h - chosen), n ** (h - chosen))
                * (
                    Fraction(1, n**2 * falling(n, exposure + chosen))
                    - Fraction(2, n * falling(n, exposure + chosen + 1))
                )
                for chosen in range(h + 1)
            )
            assert actual == -envelope(n, size, h)
            statistics['attainment_triples'] += 1

result = {
    'status': 'passed',
    'arithmetic': 'exact rational',
    'counts': dict(statistics),
    'selected_support_classes': dict(selected_classes),
    'largest_observed_ratio': {key: str(value) for key, value in maximum_ratios.items()},
    'ranges': {
        'exhaustive_direct_b2': 'n=2,3, one or two colors, every support of size at most n and every listed power assignment with exactly two inconsistent centered singletons',
        'exhaustive_selected_supports': 'n=2,3 with one or two colors and n=4 with one color, every support, every pair of inconsistent cells, every subset of good centered cells and every selected subset of the other cells',
        'sampled_exact': '4<=n<=10, one to three colors, 120 fixed-seed patterns for each pair, b=2 and a separate b>=2 assignment',
        'attainment': 'Every 2<=n<=22, 2<=a<=n and 0<=h<=a-2',
        'powers_exhaustive': power_choices,
        'additional_sampled_powers': large_other_powers[len(other_powers):],
        'random_seed': 210052,
    },
    'methods': {
        'small': 'Direct enumeration of all uniform permutations independently in each color',
        'sampled': 'Exact expansion into compatible indicator subsets',
        'attainment': 'Independent binomial expansion of all good centered factors and the mutually exclusive retained pair',
    },
    'limitations': ['Finite checks are corroboration only', 'The sampled tests are not exhaustive over their parameter ranges'],
}
Path(__file__).with_name('checks-v1.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
