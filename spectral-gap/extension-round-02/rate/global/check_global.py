from pathlib import Path
from fractions import Fraction
from math import comb, prod, isqrt
import hashlib
import json
import mpmath as mp

ROOT = Path(__file__).resolve().parent
mp.mp.dps = 80


def exact_ratio(n, k):
    falling = 1
    mu = Fraction(0)
    for j in range(k + 1):
        if j:
            falling *= n - j + 1
        mu += Fraction((-1)**(k - j)*comb(k, j)*n**j, falling)
    moment = mu/n**k
    m = k//2
    if k % 2 == 0:
        leading = Fraction(prod(range(1, k, 2)), n**(3*m))
    else:
        leading = Fraction(4*m*prod(range(1, k + 1, 2)), 3*n**(3*m + 2))
    return moment/leading


def ratios(n, selected):
    even = mp.mpf(1)
    odd = mp.mpf(1)
    values = {}
    for m in range(1, max(selected)//2 + 1):
        even = mp.mpf(n)/(n - 2*m + 1)*even + mp.mpf(4*(2*m - 1)*(2*m - 2))/(3*(n - 2*m + 1))*odd
        if 2*m in selected:
            values[2*m] = even
        if 2*m + 1 <= n:
            odd = mp.mpf(3*n)/((n - 2*m)*(2*m + 1))*even + mp.mpf((2*m - 2)*n)/((n - 2*m)*(2*m + 1))*odd
            if 2*m + 1 in selected:
                values[2*m + 1] = odd
    return values


def log_approximation(n, k):
    epsilon = k % 2
    base = k - epsilon
    x = mp.sqrt(mp.mpf(base)/n)
    lam = mp.mpf(2)/3*n*x**3
    q = x + (x*x - 1)*mp.log1p(x) - x*x/2 - mp.mpf(2)/3*x**3
    h = mp.cosh(lam) if epsilon == 0 else mp.sinh(lam)/lam
    log_d = k*mp.log(n) - mp.loggamma(n + 1) + mp.loggamma(n - k + 1)
    return log_d + mp.log(h) + n*q + (mp.mpf(epsilon) - mp.mpf('0.5'))*mp.log1p(x)


exact_checks = 0
for n in range(2, 31):
    values = ratios(n, set(range(2, n + 1)))
    for k, value in values.items():
        exact = exact_ratio(n, k)
        converted = mp.mpf(exact.numerator)/exact.denominator
        assert abs(value/converted - 1) < mp.mpf('1e-70'), (n, k)
        exact_checks += 1

range_results = []
endpoint_results = []
for n in [16, 17, 32, 33, 64, 65, 128, 129, 256, 257, 512, 513, 1024, 1025, 4096, 4097, 10000, 10001, 100000, 100001]:
    if n <= 4097:
        selected = set(range(2, n + 1))
        coverage = 'all orders'
    else:
        selected = {2, 3, 4, 5, 10, 11, n, n - 1, n - 2}
        for center in [isqrt(n), n//10, n//2, 3*n//4]:
            selected.update([center - 1, center, center + 1])
        selected = {k for k in selected if 2 <= k <= n}
        coverage = 'selected orders including both endpoints and the crossover'
    values = ratios(n, selected)
    worst = (mp.mpf(0), None)
    worst_large = (mp.mpf(0), None)
    for k, ratio in values.items():
        error = mp.expm1(mp.log(ratio) - log_approximation(n, k))
        if abs(error) > worst[0]:
            worst = (abs(error), k)
        if k >= mp.sqrt(n) and abs(error) > worst_large[0]:
            worst_large = (abs(error), k)
    range_results.append({'N': n, 'coverage': coverage, 'checked_orders': len(selected), 'maximum_absolute_relative_error': mp.nstr(worst[0], 22), 'maximizing_order': worst[1], 'maximum_above_sqrt_N': mp.nstr(worst_large[0], 22), 'maximizing_large_order': worst_large[1]})
    ratio = values[n]
    if n % 2 == 0:
        endpoint_log = mp.mpf(3)*n/2 - mp.log(4) - mp.log(mp.pi*n)/2
    else:
        endpoint_log = mp.mpf(3)*n/2 + mp.log(3) - mp.log(8) - mp.log(mp.pi)/2 - mp.mpf('1.5')*mp.log(n)
    endpoint_results.append({'N': n, 'parity': 'even' if n % 2 == 0 else 'odd', 'relative_error_of_endpoint_formula': mp.nstr(mp.expm1(mp.log(ratio) - endpoint_log), 22)})

proof = ROOT/'proof-v1.md'
result = {'proof': proof.name, 'proof_sha256': hashlib.sha256(proof.read_bytes()).hexdigest(), 'exact_inclusion_exclusion_comparisons': exact_checks, 'numeric_precision_decimal_digits': mp.mp.dps, 'range_results': range_results, 'endpoint_results': endpoint_results, 'scope': 'Exact finite normalization checks and numerical corroboration across the full range. The uniform theorem and rates depend on the written proof.'}
(ROOT/'checks-v1.json').write_text(json.dumps(result, indent=2) + '\n')
print('Exact normalization comparisons passed:', exact_checks)
print('Total global approximation evaluations:', sum(x['checked_orders'] for x in range_results))
for x in range_results[-4:]:
    print(x)
for x in endpoint_results[-2:]:
    print(x)
