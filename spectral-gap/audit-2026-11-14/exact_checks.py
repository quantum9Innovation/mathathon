"""Bounded exact checks of the permutation product argument."""

from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial, isqrt
from pathlib import Path
import json


def falling(n, length):
    value = 1
    for j in range(length):
        value *= n - j
    return value


def finite_difference(n, r, h):
    return sum(
        (
            Fraction((-1) ** (h - j) * comb(h, j) * n**j, falling(n - r, j))
            for j in range(h + 1)
        ),
        Fraction(0),
    )


def recurrence(n, r, h):
    values = [Fraction(1)]
    if h:
        values.append(Fraction(r, n - r))
    for j in range(2, h + 1):
        values.append(
            ((r + 2 * j - 2) * values[-1] + (j - 1) * values[-2])
            / (n - r - j + 1)
        )
    return values[h]


def exact_product_by_subset(n, cells, powers):
    total = Fraction(0)
    count = len(cells)
    for bits in product((0, 1), repeat=count):
        coefficient = Fraction(1)
        chosen = []
        for cell, (p, q), bit in zip(cells, powers, bits):
            if q:
                constant = Fraction(0)
                linear = Fraction(n - 1, n) ** p
            else:
                constant = Fraction(-1, n) ** p
                linear = Fraction(n - 1, n) ** p - constant
            coefficient *= linear if bit else constant
            if bit:
                chosen.append(cell)
        if not coefficient:
            continue
        colors = {cell[0] for cell in chosen}
        probability = Fraction(1)
        for color in colors:
            block = [cell for cell in chosen if cell[0] == color]
            if len({cell[1] for cell in block}) != len(block):
                probability = Fraction(0)
                break
            if len({cell[2] for cell in block}) != len(block):
                probability = Fraction(0)
                break
            probability /= falling(n, len(block))
        total += coefficient * probability
    return total


def direct_permutation_average(n, cells, powers, ensemble):
    total = Fraction(0)
    for sigma in ensemble:
        value = Fraction(1)
        for (_, row, column), (p, q) in zip(cells, powers):
            indicator = int(sigma[row] == column)
            value *= (indicator - Fraction(1, n)) ** p * indicator**q
        total += value
    return total / factorial(n)


def counts(cells, powers):
    good = 0
    bad = 0
    for index, (cell, power) in enumerate(zip(cells, powers)):
        if power != (1, 0):
            continue
        color, row, column = cell
        conflict = any(
            other_index != index
            and other[0] == color
            and (other[1] == row or other[2] == column)
            for other_index, other in enumerate(cells)
        )
        if conflict:
            bad += 1
        else:
            good += 1
    return good, bad


def rational_bound_check(n, cells, powers, value):
    a = len(cells)
    h, b = counts(cells, powers)
    squared_upper = Fraction(9 * 4**b, n ** (2 * a)) * Fraction(4 * a, n) ** h
    assert value * value <= squared_upper, (n, cells, powers, value)


def partitions(length):
    if length == 0:
        yield ()
        return
    for prefix in partitions(length - 1):
        for label in range(max(prefix, default=-1) + 2):
            yield prefix + (label,)


def run():
    report = {}
    recurrence_checks = 0
    for n in range(4, 257):
        a = isqrt(n)
        for r in range(a + 1):
            for h in range(a - r + 1):
                value = finite_difference(n, r, h)
                assert value == recurrence(n, r, h), (n, r, h)
                assert value >= 0, (n, r, h)
                assert value * value <= Fraction(4 * a, n) ** h, (n, r, h)
                recurrence_checks += 1
    report["finite_difference_recurrence_checks"] = recurrence_checks

    ensemble = list(permutations(range(4)))
    all_cells = [(0, row, column) for row in range(4) for column in range(4)]
    power_types = [(1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (0, 2)]
    exhaustive_checks = 0
    for a in (1, 2):
        for cells in combinations(all_cells, a):
            for powers in product(power_types, repeat=a):
                exact = direct_permutation_average(4, cells, powers, ensemble)
                assert exact == exact_product_by_subset(4, cells, powers)
                rational_bound_check(4, cells, powers, exact)
                exhaustive_checks += 1
    report["n4_direct_permutation_product_checks"] = exhaustive_checks

    pattern_checks = 0
    for a in (2, 3, 4):
        n = a * a
        for rows in partitions(a):
            for columns in partitions(a):
                cells = tuple((0, row, column) for row, column in zip(rows, columns))
                if len(set(cells)) != a:
                    continue
                for powers in product(((1, 0), (2, 0), (0, 1)), repeat=a):
                    value = exact_product_by_subset(n, cells, powers)
                    rational_bound_check(n, cells, powers, value)
                    pattern_checks += 1
    report["canonical_incidence_pattern_checks"] = pattern_checks

    multicolor_checks = 0
    for colors in partitions(4):
        for rows, columns in (
            ((0, 1, 2, 3), (0, 1, 2, 3)),
            ((0, 0, 1, 2), (0, 1, 1, 2)),
            ((0, 1, 0, 1), (0, 1, 1, 0)),
        ):
            cells = tuple(zip(colors, rows, columns))
            if len(set(cells)) != 4:
                continue
            for powers in product(((1, 0), (2, 0), (0, 1)), repeat=4):
                value = exact_product_by_subset(16, cells, powers)
                rational_bound_check(16, cells, powers, value)
                multicolor_checks += 1
    report["multicolor_product_checks"] = multicolor_checks

    shared = [sigma for sigma in ensemble if sigma[0] == 0]
    disjoint = [sigma for sigma in ensemble if sigma[1] == 2 and sigma[3] == 1]
    shared_probability = Fraction(sum(sigma[0] == 0 for sigma in shared), len(shared))
    disjoint_probability = Fraction(sum(sigma[0] == 0 for sigma in disjoint), len(disjoint))
    assert shared_probability == 1
    assert disjoint_probability == Fraction(1, 2)
    report["source_equation_62_counterexamples"] = {
        "shared_row_actual": str(shared_probability),
        "shared_row_printed": "0",
        "shared_row_event_probability": str(Fraction(len(shared), len(ensemble))),
        "disjoint_actual": str(disjoint_probability),
        "disjoint_printed": "1/3",
        "disjoint_event_probability": str(Fraction(len(disjoint), len(ensemble))),
    }

    report["scope"] = (
        "Finite exact checks only. The checked product bound uses 3 in place of e "
        "so that its square is rational. The general theorem is supported by its proof."
    )
    report["status"] = "passed"
    output = Path(__file__).with_name("exact-checks-v1.json")
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    run()
