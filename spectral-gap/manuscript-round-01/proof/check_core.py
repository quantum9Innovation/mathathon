"""Exact finite corroboration of the reconstructed moment arguments."""

from fractions import Fraction
from math import comb
from pathlib import Path
import hashlib
import json


def falling(n, k):
    answer = 1
    for j in range(k):
        answer *= n - j
    return answer


def depleted_moments(n, r):
    answer = [Fraction(1)]
    if n > r:
        answer.append(Fraction(r, n - r))
    for h in range(2, n - r + 1):
        answer.append(((r + 2 * h - 2) * answer[-1] + (h - 1) * answer[-2]) / (n - r - h + 1))
    return answer


def expanded_moment(n, r, h):
    return sum((Fraction(comb(h, j) * (-1) ** (h - j) * n ** j, falling(n - r, j)) for j in range(h + 1)), Fraction(0))


def leading_normalized(n, k, moment):
    if k % 2 == 0:
        m = k // 2
        odd_factorial = 1
        for j in range(1, 2 * m, 2):
            odd_factorial *= j
        return moment * Fraction(n ** m, odd_factorial)
    m = (k - 1) // 2
    odd_factorial = 1
    for j in range(1, 2 * m + 2, 2):
        odd_factorial *= j
    return moment * Fraction(3 * n ** (m + 1), 4 * m * odd_factorial)


def run():
    counts = {}
    count = 0
    for n in range(1, 33):
        for r in range(n + 1):
            for h, value in enumerate(depleted_moments(n, r)):
                assert value == expanded_moment(n, r, h)
                assert value >= 0
                count += 1
    counts['exact_depleted_recurrence_identities'] = count

    count = 0
    for n in range(2, 65):
        for p in range(2, 65):
            constant = Fraction(-1, n) ** p
            coefficient = Fraction(n - 1, n) ** p - constant
            assert 0 <= coefficient <= 1
            assert coefficient + n * abs(constant) <= Fraction(n - 1, n)
            count += 1
    counts['sharpened_repeated_cell_inequalities'] = count

    count = 0
    for n in range(1, 65):
        for r in range(n + 1):
            for s in range(n - r + 1):
                assert falling(n, r) * falling(n, s) >= falling(n, r + s)
                count += 1
    counts['factorial_correction_merging_inequalities'] = count

    count = 0
    upper_count = 0
    for n in range(2, 161):
        moments = depleted_moments(n, 0)
        max_ratio = Fraction(1)
        upper_product = Fraction(1)
        for k in range(2, n + 1):
            ratio = leading_normalized(n, k, moments[k])
            m = k // 2
            if k % 2 == 0:
                lower_coefficient = Fraction(m * (16 * m * m - 3 * m - 4), 9)
            else:
                lower_coefficient = Fraction(80 * m ** 3 + 195 * m * m + 124 * m + 6, 135)
            assert ratio - 1 >= lower_coefficient / n
            assert ratio - 1 >= Fraction(2 * k ** 3, 27 * n)
            count += 1
            if 2 * k <= n:
                upper_product *= 1 + Fraction(3 * k * k, n)
                max_ratio = max(max_ratio, ratio)
                assert max_ratio <= upper_product
                upper_count += 1
    counts['sharp_lower_bound_checks'] = count
    counts['rational_upper_product_checks'] = upper_count

    folder = Path(__file__).resolve().parent
    inputs = folder.parent / 'inputs'
    hashes = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs.glob('*.md')}
    report = {'status': 'passed', 'counts': counts, 'input_hashes': hashes,
              'scope': 'Exact rational finite checks of identities, coefficient bounds and lower bounds. General statements rely on the written proofs. No floating point tests or kernel verification are used.'}
    (folder / 'core-checks-v1.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    run()
