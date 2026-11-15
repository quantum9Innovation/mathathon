"""Independent finite corroboration for the frozen hyperbolic-window proof."""

from fractions import Fraction
from math import comb, factorial, isqrt
from pathlib import Path
import hashlib
import json
import mpmath as mp


def falling(n, k):
    answer = 1
    for j in range(k):
        answer *= n - j
    return answer


def by_recurrence(n, top):
    values = [1, 0]
    for k in range(2, top + 1):
        values.append(2 * (k - 1) * values[-1] + (k - 1) * (n - k + 2) * values[-2])
    return values


def by_distinguished_block(n, top):
    values = [1, 0]
    for k in range(2, top + 1):
        values.append(sum(comb(k - 1, j - 1) * n * (j - 1) * factorial(j - 1) * values[k - j] for j in range(2, k + 1)))
    return values


def moment_inclusion_exclusion(n, k):
    return sum(comb(k, j) * (-1) ** (k - j) * n ** j * falling(n - j, k - j) for j in range(k + 1))


def partitions_without_singletons(k, minimum=2):
    if k == 0:
        yield ()
    for j in range(minimum, k + 1):
        for tail in partitions_without_singletons(k - j, j):
            yield (j,) + tail


def leading_q(n, k):
    m = k // 2
    if k % 2 == 0:
        return factorial(k) * Fraction(n, 2) ** m / factorial(m)
    return factorial(k) * Fraction(n, 2) ** (m - 1) * Fraction(2 * n, 3) / factorial(m - 1)


def exact_partition_term(n, k, blocks):
    counts = {j: blocks.count(j) for j in set(blocks)}
    answer = Fraction(factorial(k))
    for j, count in counts.items():
        answer *= Fraction(n * (j - 1), j) ** count / factorial(count)
    return answer


def availability_term(n, k, blocks):
    m = k // 2
    K = 2 * m
    counts = {j: blocks.count(j) for j in set(blocks) if j >= 3}
    S = sum(j * count for j, count in counts.items())
    answer = Fraction(1)
    for j, count in counts.items():
        answer *= Fraction(n * (j - 1), j) ** count / factorial(count)
    if k % 2 == 0:
        s = S // 2
        answer *= Fraction(K, n) ** s * Fraction(falling(m, s), m ** s)
    else:
        s = (S - 3) // 2
        answer *= Fraction(3, 2 * n) * Fraction(K, n) ** s * Fraction(falling(m - 1, s), m ** s)
    return answer


def mp_ratios(n, max_k):
    even = mp.mpf(1)
    odd = mp.mpf(1)
    values = {}
    for m in range(1, max_k // 2 + 1):
        even = (mp.mpf(n) * even + mp.mpf(4 * (2 * m - 1) * (2 * m - 2)) * odd / 3) / (n - 2 * m + 1)
        values[2 * m] = even
        if 2 * m + 1 <= max_k:
            odd = (mp.mpf(3 * n) * even + mp.mpf((2 * m - 2) * n) * odd) / ((n - 2 * m) * (2 * m + 1))
            values[2 * m + 1] = odd
    return values


def H(n, k):
    K = 2 * (k // 2)
    lam = mp.mpf(2) * mp.sqrt(mp.mpf(K) ** 3 / n) / 3
    if k % 2 == 0:
        return mp.cosh(lam)
    return mp.sinh(lam) / lam


def run():
    mp.mp.dps = 70
    counts = {}
    exact_count = 0
    partition_count = 0
    for n in range(2, 65):
        top = min(n, 24)
        one = by_recurrence(n, top)
        two = by_distinguished_block(n, top)
        for k in range(2, top + 1):
            assert one[k] == two[k] == moment_inclusion_exclusion(n, k)
            exact_count += 1
        for k in range(2, min(n, 14) + 1):
            for blocks in partitions_without_singletons(k):
                ratio = exact_partition_term(n, k, blocks) / leading_q(n, k)
                assert ratio == availability_term(n, k, blocks)
                partition_count += 1
    counts['three_way_integer_polynomial_checks'] = exact_count
    counts['exact_even_odd_availability_checks'] = partition_count

    envelope_count = 0
    for n in range(8, 257):
        values = mp_ratios(n, n // 4)
        for k, ratio in values.items():
            normalized = ratio / H(n, k)
            u = mp.mpf(k) ** 2 / n
            assert normalized >= 1 - 4 * u / 3
            assert mp.log(normalized) <= 4 * u
            if 4 * k * k <= n:
                assert mp.log(normalized) >= -2 * u
            envelope_count += 1
    counts['high_precision_finite_envelope_checks'] = envelope_count

    boundary = []
    for n in (10_000, 1_000_000, 100_000_000):
        for scale in (Fraction(1, 2), Fraction(1), Fraction(2)):
            base = int(scale * isqrt(n))
            even_k = base - base % 2
            values = mp_ratios(n, even_k + 1)
            for k in (even_k, even_k + 1):
                uncorrected = values[k] / H(n, k)
                d = mp.mpf(k) ** 2 / n
                corrected = uncorrected / mp.exp(d / 4)
                boundary.append({'N': n, 'k': k, 'd': mp.nstr(d, 12),
                                 'R_over_H': mp.nstr(uncorrected, 18),
                                 'corrected_ratio': mp.nstr(corrected, 18)})
    source = Path(__file__).resolve().parents[1] / 'extensions/hyperbolic-window-v1.md'
    report = {'status': 'passed', 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'counts': counts, 'boundary_examples': boundary,
              'scope': 'Integer and rational checks certify the recorded finite identities only. Floating point checks use 70 decimal digits and corroborate the finite envelope and square-root examples. General claims rely on the written proof.'}
    output = Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    run()
