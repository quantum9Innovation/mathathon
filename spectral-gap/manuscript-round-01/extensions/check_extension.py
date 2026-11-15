from fractions import Fraction
from itertools import permutations
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import mpmath as mp


ROOT = Path(__file__).resolve().parent
mp.mp.dps = 80


def falling(n, k):
    value = 1
    for j in range(k):
        value *= n - j
    return value


def positive_coefficients(n, limit):
    coefficients = [Fraction(1)]
    for k in range(1, limit + 1):
        value = sum((j - 1) * coefficients[k - j] for j in range(2, k + 1))
        coefficients.append(Fraction(n, k) * value)
    return [factorial(k) * coefficients[k] for k in range(limit + 1)]


def polynomial_recurrence(n, limit):
    values = [1, 0]
    for k in range(2, limit + 1):
        values.append(2 * (k - 1) * values[k - 1] + (k - 1) * (n - k + 2) * values[k - 2])
    return values[:limit + 1]


def inclusion_exclusion(n, k):
    mu = sum(Fraction((-1) ** (k - j) * comb(k, j) * n ** j, falling(n, j)) for j in range(k + 1))
    return mu * falling(n, k)


def ratios(n, limit):
    values = {2: mp.mpf(n) / (n - 1)}
    even = mp.mpf(1)
    odd = mp.mpf(1)
    for m in range(1, (limit + 1) // 2 + 1):
        even = mp.mpf(n) / (n - 2 * m + 1) * even + mp.mpf(4 * (2 * m - 1) * (2 * m - 2)) / (3 * (n - 2 * m + 1)) * odd
        if 2 * m <= limit:
            values[2 * m] = even
        if 2 * m + 1 <= min(limit, n):
            odd = mp.mpf(3 * n) / ((n - 2 * m) * (2 * m + 1)) * even + mp.mpf((2 * m - 2) * n) / ((n - 2 * m) * (2 * m + 1)) * odd
            values[2 * m + 1] = odd
    return values


def comparison(n, k):
    base = 2 * (k // 2)
    lam = mp.mpf(2) / 3 * mp.sqrt(mp.mpf(base) ** 3 / n)
    return mp.cosh(lam) if k % 2 == 0 else mp.sinh(lam) / lam


exact_count = 0
for n in range(2, 65):
    limit = min(n, 18)
    positive = positive_coefficients(n, limit)
    recurrence = polynomial_recurrence(n, limit)
    for k in range(limit + 1):
        assert positive[k] == recurrence[k] == inclusion_exclusion(n, k), (n, k)
        exact_count += 1

permutation_cases = 0
permutation_count = 0
for n in range(2, 8):
    totals = [0] * (n + 1)
    for permutation in permutations(range(n)):
        permutation_count += 1
        product = 1
        totals[0] += product
        for k in range(1, n + 1):
            product *= n * int(permutation[k - 1] == k - 1) - 1
            totals[k] += product
    positive = positive_coefficients(n, n)
    for k in range(n + 1):
        assert Fraction(totals[k], factorial(n)) == positive[k] / falling(n, k), (n, k)
        permutation_cases += 1

bound_count = 0
log_count = 0
max_scaled_log_error = mp.mpf(0)
for n in list(range(8, 161)) + [256, 512, 1024, 4096]:
    for k, ratio in ratios(n, n // 4).items():
        delta = mp.mpf(k) ** 2 / n
        normalized = ratio / comparison(n, k)
        assert normalized >= 1 - 4 * delta / 3 - mp.mpf('1e-65'), (n, k, 'lower')
        assert normalized <= mp.exp(4 * delta) * (1 + mp.mpf('1e-65')), (n, k, 'upper')
        bound_count += 1
        if 4 * k * k <= n:
            log_error = mp.log(normalized)
            assert -2 * delta - mp.mpf('1e-65') <= log_error <= 4 * delta + mp.mpf('1e-65')
            max_scaled_log_error = max(max_scaled_log_error, abs(log_error) / delta)
            log_count += 1

boundary = []
for n in [10**4, 10**6, 10**8]:
    target_orders = []
    for target in [mp.mpf('0.25'), mp.mpf(1), mp.mpf(4)]:
        even_k = 2 * int(mp.sqrt(target * n) / 2)
        target_orders.append((target, even_k))
        target_orders.append((target, even_k + 1))
    computed = ratios(n, max(k for _, k in target_orders))
    for target, k in target_orders:
        ratio_to_h = computed[k] / comparison(n, k)
        delta = mp.mpf(k) ** 2 / n
        boundary.append({
            'N': n,
            'k': k,
            'parity': 'even' if k % 2 == 0 else 'odd',
            'target_d': str(target),
            'actual_k_squared_over_N': mp.nstr(delta, 20),
            'R_over_H': mp.nstr(ratio_to_h, 20),
            'predicted_exp_actual_delta_over_4': mp.nstr(mp.exp(delta / 4), 20),
            'relative_corrected_error': mp.nstr(ratio_to_h / mp.exp(delta / 4) - 1, 20)
        })

proof = ROOT / 'hyperbolic-window-v1.md'
result = {
    'proof': proof.name,
    'proof_sha256': hashlib.sha256(proof.read_bytes()).hexdigest(),
    'exact_formula_cases': exact_count,
    'enumerated_permutations': permutation_count,
    'enumerated_moment_cases': permutation_cases,
    'finite_envelope_cases': bound_count,
    'finite_log_envelope_cases': log_count,
    'maximum_observed_abs_log_error_divided_by_delta': mp.nstr(max_scaled_log_error, 20),
    'numeric_precision_decimal_digits': mp.mp.dps,
    'boundary_examples': boundary,
    'scope': 'Exact finite identities and high-precision numerical corroboration. General claims depend on the written proof, not these checks.'
}
output = ROOT / 'extension-checks-v1.json'
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({key: value for key, value in result.items() if key != 'boundary_examples'}, indent=2))
print('Boundary examples saved:', len(boundary))
