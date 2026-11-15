from fractions import Fraction
from math import comb, factorial, isqrt
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps = 90


def q_polynomials(n):
    values = [1, 0]
    for k in range(2, n + 1):
        values.append(2 * (k - 1) * values[-1] + (k - 1) * (n - k + 2) * values[-2])
    return values


def falling(n, k):
    value = 1
    for j in range(k):
        value *= n - j
    return value


def direct_moment(n, k):
    return sum((Fraction(comb(k, j) * (-1)**(k - j), n**(k - j) * falling(n, j))
                for j in range(k + 1)), Fraction(0))


def terms(n, k, qk):
    epsilon = k % 2
    big_k = k - epsilon
    m = big_k // 2
    x = mp.sqrt(mp.mpf(big_k) / n)
    lam = mp.mpf(2) * n * x**3 / 3
    q = x + (x*x - 1) * mp.log1p(x) - x*x/2 - mp.mpf(2)*x**3/3
    log_h = lam + mp.log1p((-1)**epsilon * mp.exp(-2*lam)) - mp.log(2) - epsilon*mp.log(lam)
    log_d = k*mp.log(n) - mp.loggamma(n + 1) + mp.loggamma(n - k + 1)
    log_l = mp.loggamma(k + 1) - m*mp.log(2) - mp.loggamma(m + 1) + m*mp.log(n)
    if epsilon:
        log_l += mp.log(mp.mpf(4)*m/3)
    polynomial_ratio = mp.log(qk) - log_l
    local_approximation = log_h + n*q + (mp.mpf(epsilon)-mp.mpf('0.5'))*mp.log1p(x)
    log_r = log_d + polynomial_ratio
    log_a = log_d + local_approximation
    residual = polynomial_ratio - local_approximation
    assert abs((log_r-log_a)-residual) < mp.mpf('1e-75')
    return residual, log_r, log_a-log_h-mp.mpf(k*k)/(4*n)


identity_count = 0
for n in range(2, 37):
    values = q_polynomials(n)
    for k in range(2, n + 1):
        exact = direct_moment(n, k)
        assert exact == Fraction(values[k], falling(n, k)*n**k)
        identity_count += 1

range_results = []
endpoint_results = []
patch_count = 0
evaluation_count = 0
for n in [16, 17, 40, 41, 100, 101, 400, 401, 1600, 1601, 6400, 6401]:
    values = q_polynomials(n)
    all_max = (mp.mpf(0), 0)
    large_max = (mp.mpf(0), 0)
    r_bound = mp.mpf(19)/30*n**(-mp.mpf(1)/4) + mp.mpf(5)/6*n**(-mp.mpf(1)/2)
    for k in range(2, n + 1):
        residual, log_r, j_value = terms(n, k, values[k])
        error = abs(mp.expm1(residual))
        if error > all_max[0]:
            all_max = (error, k)
        if k*k >= n and error > large_max[0]:
            large_max = (error, k)
        if k <= isqrt(n):
            assert abs(j_value) <= r_bound
            patch_count += 1
        evaluation_count += 1
    endpoint_r = terms(n, n, values[n])[1]
    if n % 2:
        target = mp.mpf(3)*n/2 + mp.log(3) - mp.log(8) - mp.log(mp.pi)/2 - mp.mpf('1.5')*mp.log(n)
    else:
        target = mp.mpf(3)*n/2 - mp.log(4) - mp.log(mp.pi*n)/2
    unnormalized = Fraction(2*values[n], n**n)
    endpoint_results.append({
        'N': n,
        'parity': 'odd' if n % 2 else 'even',
        'relative_error_in_stated_R_endpoint': mp.nstr(mp.expm1(endpoint_r-target), 24),
        'two_factorial_times_original_moment': mp.nstr(mp.mpf(unnormalized.numerator)/unnormalized.denominator, 24),
    })
    range_results.append({
        'N': n,
        'orders_checked': n-1,
        'maximum_relative_error': mp.nstr(all_max[0], 24),
        'maximizing_order': all_max[1],
        'maximum_above_sqrt_N': mp.nstr(large_max[0], 24),
        'maximizing_large_order': large_max[1],
    })

record = {
    'exact_identity_checks': identity_count,
    'full_formula_evaluations': evaluation_count,
    'lower_patch_checks': patch_count,
    'exact_D_cancellation_numeric_checks': evaluation_count,
    'decimal_precision': mp.mp.dps,
    'coefficient_calculation': 'Exact integer recurrence for Q, separately checked against original inclusion-exclusion moments',
    'range_results': range_results,
    'endpoint_results': endpoint_results,
    'scope': 'Exact finite normalization checks and high precision numerical corroboration. No interval certificate or numerical proof of the uniform constants.',
}
Path(__file__).with_name('global-by-saddle-check-results-v1.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['exact_identity_checks','full_formula_evaluations','lower_patch_checks','decimal_precision']}, indent=2))
print(json.dumps(endpoint_results[-2:], indent=2))
