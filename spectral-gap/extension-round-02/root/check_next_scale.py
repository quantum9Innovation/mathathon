"""Corroborate the proposed next scale and single positive saddle."""

import hashlib
import json
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parent
mp.mp.dps = 60


def normalized_moments(n, wanted):
    result = {}
    even = odd = mp.mpf(1)
    for m in range(1, max(wanted) // 2 + 1):
        even = (n * even + mp.mpf(4) * (2 * m - 1) * (2 * m - 2) * odd / 3) / (n - 2 * m + 1)
        if 2 * m in wanted:
            result[2 * m] = even
        if 2 * m + 1 <= n:
            odd = (3 * n * even + (2 * m - 2) * n * odd) / ((n - 2 * m) * (2 * m + 1))
            if 2 * m + 1 in wanted:
                result[2 * m + 1] = odd
    return result


def log_h(n, k):
    big_k = 2 * (k // 2)
    lam = mp.mpf(2) / 3 * mp.sqrt(mp.mpf(big_k) ** 3 / n)
    return mp.log(mp.cosh(lam)) if k % 2 == 0 else mp.log(mp.sinh(lam) / lam)


def log_saddle_ratio(n, k):
    t = mp.sqrt(mp.mpf(k) / n)
    action = n * (t + (t * t - 1) * mp.log1p(t)) - k * mp.log(t)
    log_coefficient = action - mp.log(4 * mp.pi * k * (1 + t)) / 2
    log_moment = mp.loggamma(k + 1) + log_coefficient - mp.loggamma(n + 1) + mp.loggamma(n - k + 1) - k * mp.log(n)
    m = k // 2
    if k % 2 == 0:
        log_leading = mp.loggamma(2 * m + 1) - m * mp.log(2) - mp.loggamma(m + 1) - 3 * m * mp.log(n)
    else:
        log_leading = mp.log(mp.mpf(4) * m / 3) + mp.loggamma(2 * m + 2) - m * mp.log(2) - mp.loggamma(m + 1) - (3 * m + 2) * mp.log(n)
    return log_moment - log_leading


def main():
    boundary = []
    for n in [10_000, 1_000_000, 100_000_000]:
        wanted = set()
        for scale in [mp.mpf('0.5'), mp.mpf(1), mp.mpf(2)]:
            k = 2 * int(scale * mp.power(n, mp.mpf(3) / 5) / 2)
            wanted.update([k, k + 1])
        values = normalized_moments(n, wanted)
        for k in sorted(wanted):
            corrected = mp.exp(mp.log(values[k]) - log_h(n, k) - mp.mpf(k) ** 2 / (4 * n))
            proposed = mp.exp(mp.mpf(2) / 15 * mp.power(k, mp.mpf(5) / 2) / mp.power(n, mp.mpf(3) / 2))
            saddle_relative = mp.exp(mp.log(values[k]) - log_saddle_ratio(n, k)) - 1
            boundary.append({'N': n, 'k': k, 'corrected_ratio': mp.nstr(corrected, 24),
                             'proposed_next_factor': mp.nstr(proposed, 24),
                             'ratio_to_next_factor': mp.nstr(corrected / proposed, 24),
                             'relative_error_against_positive_saddle': mp.nstr(saddle_relative, 24)})
        print('Completed next-scale samples for N =', n, flush=True)
    endpoints = []
    for n in [100, 1000, 10000]:
        wanted = {n // 2, n // 2 + 1, n - 1, n}
        values = normalized_moments(n, wanted)
        for k in sorted(wanted):
            error = mp.exp(mp.log(values[k]) - log_saddle_ratio(n, k)) - 1
            endpoints.append({'N': n, 'k': k, 'relative_error_against_positive_saddle': mp.nstr(error, 24)})
    source = ROOT.parents[1] / 'manuscript-round-01/extensions/hyperbolic-window-v1.md'
    report = {'scope': 'High-precision numerical corroboration only. No general theorem is inferred.',
              'decimal_precision': mp.mp.dps, 'accepted_base_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'next_scale_samples': boundary, 'large_order_samples': endpoints}
    (ROOT / 'next-scale-checks.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(boundary[-6:], indent=2))


if __name__ == '__main__':
    main()
