import hashlib
import json
import math
from pathlib import Path

import mpmath as mp


mp.mp.dps = 80
HERE = Path(__file__).resolve().parent
BASE = HERE.parent


def moments(n, last):
    a, b = 1, 0
    yield 0, a
    yield 1, b
    for k in range(2, last + 1):
        q = 2 * (k - 1) * b + (k - 1) * (n - k + 2) * a
        yield k, q
        a, b = b, q


def exact_inclusion(n, k):
    denominator = math.factorial(n - k)
    return sum(
        math.comb(k, j)
        * (-1) ** (k - j)
        * n**j
        * (math.factorial(n - j) // denominator)
        for j in range(k + 1)
    )


def exact_blocks(n, last):
    values = [1, 0]
    for k in range(2, last + 1):
        values.append(
            n
            * sum(
                (j - 1)
                * (math.factorial(k - 1) // math.factorial(k - j))
                * values[k - j]
                for j in range(2, k + 1)
            )
        )
    return values


def profile(c, odd):
    ell = mp.mpf(2) * c ** mp.mpf('1.5') / 3
    if odd:
        return -mp.mpf(3) / (4 * c) * (1 - 2 * ell / mp.expm1(2 * ell))
    return mp.mpf(3) / (4 * c) * 2 * ell / (mp.exp(2 * ell) + 1)


def error(n, k, q):
    odd = k % 2
    K = k - odd
    m = K // 2
    x = mp.sqrt(mp.mpf(K) / n)
    lam = mp.mpf(2) * K * x / 3
    log_l = (
        mp.loggamma(k + 1)
        - m * mp.log(2)
        - mp.loggamma(m + 1)
        + m * mp.log(n)
    )
    if odd:
        log_l += mp.log(mp.mpf(4) * m / 3)
        parity_log = mp.log(-mp.expm1(-2 * lam))
    else:
        parity_log = mp.log1p(mp.exp(-2 * lam))
    log_h = lam - mp.log(2) + parity_log - odd * mp.log(lam)
    action = x + (x * x - 1) * mp.log1p(x) - x * x / 2 - mp.mpf(2) * x**3 / 3
    log_ratio = mp.log(q) - log_l - log_h - n * action - (mp.mpf(odd) - mp.mpf('.5')) * mp.log1p(x)
    return mp.expm1(log_ratio)


def record(n, k, q):
    scale = mp.root(n, 3)
    c = mp.mpf(k) / scale
    err = error(n, k, q)
    target = profile(c, k % 2)
    return {
        'N': n,
        'k': k,
        'parity': k % 2,
        'critical_scale': mp.nstr(c, 30),
        'error': mp.nstr(err, 30),
        'scaled_error': mp.nstr(scale * err, 30),
        'profile': mp.nstr(target, 30),
        'profile_gap': mp.nstr(abs(scale * err - target), 30),
    }


def main():
    expected = {
        'global-sharp-rate/proof-v1.md': 'c3f5bd362a005688d28a6ac1f5440188aa0b8f4a802de269b17c7d4e08e96fcf',
        'global-sharp-rate/MANIFEST-v1.json': 'a67784bed544f88c670b000bda04ec700d257a98c14ffd33d77ea5958314e268',
    }
    for name, digest in expected.items():
        assert hashlib.sha256((BASE / name).read_bytes()).hexdigest() == digest

    exact_cases = 0
    for n in range(2, 33):
        for k, q in moments(n, n):
            assert q == exact_inclusion(n, k)
            exact_cases += 1

    blocks = exact_blocks(37, 37)
    assert all(q == blocks[k] for k, q in moments(37, 37))

    h = lambda z: 2 * mp.exp(2 * z) - (3 * z * z - z + 4) * mp.exp(z) - z + 2
    zstar = mp.findroot(h, (mp.mpf('1.3'), mp.mpf('2.1')))
    cstar = (3 * zstar / 4) ** (mp.mpf(2) / 3)
    constant = abs(profile(cstar, 1))
    scans = []
    for n in [257, 2048, 15625]:
        best = None
        biggest_gap = None
        for k, q in moments(n, n):
            if k < 2:
                continue
            row = record(n, k, q)
            if best is None or abs(mp.mpf(row['error'])) > abs(mp.mpf(best['error'])):
                best = row
            if biggest_gap is None or mp.mpf(row['profile_gap']) > mp.mpf(biggest_gap['profile_gap']):
                biggest_gap = row
        scans.append({'N': n, 'max_absolute_error': best, 'max_profile_gap': biggest_gap})
        print('full_scan', n, best['k'], best['scaled_error'], 'gap', biggest_gap['profile_gap'], flush=True)

    samples = []
    for n in [10**6, 10**9]:
        scale = mp.root(n, 3)
        orders = {2, 3}
        for c in [mp.mpf('.125'), mp.mpf('.5'), mp.mpf(1), cstar, mp.mpf(2), mp.mpf(4), mp.mpf(8)]:
            even = 2 * int(c * scale / 2)
            orders.update([max(2, even), max(3, even + 1)])
        orders.update([math.isqrt(n), math.isqrt(n) + 1])
        for k, q in moments(n, max(orders)):
            if k in orders:
                samples.append(record(n, k, q))
        print('sampled', n, len(orders), flush=True)

    output = {
        'task': 'GSR-1 independent finite checks',
        'precision_decimal_digits': mp.mp.dps,
        'implementation': 'Exact integer two-step recurrence, separately verified against the exact alternating moment sum and positive block recurrence',
        'proof_inputs': expected,
        'exact_inclusion_cases': exact_cases,
        'exact_block_cases': len(blocks),
        'positive_root': mp.nstr(zstar, 60),
        'maximizing_scale': mp.nstr(cstar, 60),
        'sharp_constant': mp.nstr(constant, 60),
        'full_scans': scans,
        'samples': samples,
        'role': 'Corroboration only. The written review supplies the uniform arguments.',
    }
    (HERE / 'global-sharp-v1-checks.json').write_text(json.dumps(output, indent=2) + '\n')


if __name__ == '__main__':
    main()
