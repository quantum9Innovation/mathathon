from pathlib import Path
import json
import mpmath as mp


mp.mp.dps = 60


def critical_equation(z):
    return 2 * mp.exp(2 * z) - (3 * z**2 - z + 4) * mp.exp(z) - z + 2


z_star = mp.findroot(critical_equation, (mp.mpf('1.5'), mp.mpf('2')))
c_star = (3 * z_star / 4) ** (mp.mpf(2) / 3)
sharp_constant = 3 / (4 * c_star) * (1 - z_star / mp.expm1(z_star))


def profile(c, parity):
    lam = mp.mpf(2) / 3 * c ** mp.mpf('1.5')
    if parity == 0:
        return 3 / (4 * c) * (2 * lam / (mp.exp(2 * lam) + 1))
    return -3 / (4 * c) * (1 - 2 * lam / mp.expm1(2 * lam))


def error_from_q(N, k, q_value):
    parity = k % 2
    K = k - parity
    m = K // 2
    x = mp.sqrt(mp.mpf(K) / N)
    lam = mp.mpf(2) / 3 * K * x
    log_l = (
        mp.loggamma(k + 1)
        - m * mp.log(2)
        - mp.loggamma(m + 1)
        + m * mp.log(N)
    )
    if parity:
        log_l += mp.log(mp.mpf(2) * K / 3)
    parity_term = (
        mp.log(-mp.expm1(-2 * lam))
        if parity
        else mp.log1p(mp.exp(-2 * lam))
    )
    log_h = lam - mp.log(2) - parity * mp.log(lam) + parity_term
    q_action = (
        x + (x**2 - 1) * mp.log1p(x) - x**2 / 2 - mp.mpf(2) / 3 * x**3
    )
    log_ratio = (
        mp.log(q_value)
        - log_l
        - log_h
        - N * q_action
        - (parity - mp.mpf('0.5')) * mp.log1p(x)
    )
    return mp.expm1(log_ratio)


full_scans = []
for N in (512, 4096, 32768):
    scale = mp.root(N, 3)
    previous = mp.mpf(1)
    current = mp.mpf(0)
    best = (mp.mpf(0), 0, mp.mpf(0))
    for k in range(2, N + 1):
        following = 2 * (k - 1) * current + (k - 1) * (N - k + 2) * previous
        previous, current = current, following
        error = error_from_q(N, k, current)
        if abs(error) > best[0]:
            best = (abs(error), k, error)
    full_scans.append({
        'N': N,
        'maximizing_k': best[1],
        'critical_location': mp.nstr(best[1] / scale, 18),
        'signed_scaled_error': mp.nstr(scale * best[2], 18),
        'scaled_supremum': mp.nstr(scale * best[0], 18),
    })

profile_checks = []
for N in (10**3, 10**6, 10**9):
    scale = mp.root(N, 3)
    selected = set()
    for c in (mp.mpf('0.5'), mp.mpf(1), c_star, mp.mpf(2)):
        base = int(mp.nint(c * scale))
        selected.update((base - base % 2, base - base % 2 + 1))
    selected = {k for k in selected if 2 <= k <= N}
    previous = mp.mpf(1)
    current = mp.mpf(0)
    for k in range(2, max(selected) + 1):
        following = 2 * (k - 1) * current + (k - 1) * (N - k + 2) * previous
        previous, current = current, following
        if k not in selected:
            continue
        scaled = scale * error_from_q(N, k, current)
        predicted = profile(k / scale, k % 2)
        profile_checks.append({
            'N': N,
            'k': k,
            'parity': k % 2,
            'scaled_error': mp.nstr(scaled, 18),
            'profile': mp.nstr(predicted, 18),
            'difference': mp.nstr(scaled - predicted, 18),
        })

record = {
    'precision_decimal_digits': mp.mp.dps,
    'mpmath_version': mp.__version__,
    'unique_positive_root': mp.nstr(z_star, 35),
    'maximizing_scale': mp.nstr(c_star, 35),
    'sharp_constant': mp.nstr(sharp_constant, 35),
    'root_residual': mp.nstr(critical_equation(z_star), 8),
    'full_scans': full_scans,
    'profile_checks': profile_checks,
    'role': 'Finite corroboration only. The proof does not use these checks.',
}
Path(__file__).with_name('checks-v1.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({
    'maximizing_scale': record['maximizing_scale'],
    'sharp_constant': record['sharp_constant'],
    'full_scans': full_scans,
    'profile_checks_count': len(profile_checks),
}, indent=2))
