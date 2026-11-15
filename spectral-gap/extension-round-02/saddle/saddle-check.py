import json
import math
from pathlib import Path


def logadd(a, b):
    if a == -math.inf:
        return b
    if b == -math.inf:
        return a
    if a < b:
        a, b = b, a
    return a + math.log1p(math.exp(b - a))


def normalized_logs(n, targets):
    answers = {}
    old_even = 0.0
    old_odd = 0.0
    for m in range(1, max(targets) // 2 + 1):
        a = n / (n - 2 * m + 1)
        b = 4 * (2 * m - 1) * (2 * m - 2) / (3 * (n - 2 * m + 1))
        even = logadd(math.log(a) + old_even, math.log(b) + old_odd if b else -math.inf)
        c = 3 * n / ((n - 2 * m) * (2 * m + 1))
        d = (2 * m - 2) * n / ((n - 2 * m) * (2 * m + 1))
        odd = logadd(math.log(c) + even, math.log(d) + old_odd if d else -math.inf)
        if 2 * m in targets:
            answers[2 * m] = even
        if 2 * m + 1 in targets:
            answers[2 * m + 1] = odd
        old_even, old_odd = even, odd
    return answers


def log_hyperbolic(n, k):
    big_k = k - k % 2
    lam = 2 * big_k ** 1.5 / (3 * math.sqrt(n))
    if k % 2 == 0:
        return lam + math.log1p(math.exp(-2 * lam)) - math.log(2)
    return lam + math.log(-math.expm1(-2 * lam)) - math.log(2 * lam)


def exponent(n, k):
    t = math.sqrt(k / n)
    return n * math.fsum(2 * t**j / (j * (j - 2)) for j in range(4, 101))


rows = []
for n in [10**4, 10**5, 10**6, 10**7, 10**8]:
    targets = set()
    for scale in [0.4, 0.6, 2 / 3, 0.75]:
        k = max(2, 2 * (int(n**scale) // 2))
        targets.update([k, k + 1])
    logs = normalized_logs(n, targets)
    for k in sorted(targets):
        actual = logs[k] - log_hyperbolic(n, k)
        fourth = k * k / (4 * n)
        fifth = 2 * k**2.5 / (15 * n**1.5)
        sixth = k**3 / (12 * n * n)
        t = math.sqrt((k - k % 2) / n)
        parity_prefactor = (1 if k % 2 else -1) * math.log1p(t) / 2
        rows.append({
            'N': n,
            'k': k,
            'parity': 'odd' if k % 2 else 'even',
            'log_R_over_H': actual,
            'after_quartic': actual - fourth,
            'predicted_quintic': fifth,
            'after_quintic': actual - fourth - fifth,
            'predicted_sextic': sixth,
            'full_exponent_error': actual - exponent(n, k),
            'parity_prefactor': parity_prefactor,
            'after_parity_prefactor': actual - exponent(n, k) - parity_prefactor,
        })

out = Path(__file__).with_name('saddle-check-results.json')
out.write_text(json.dumps({
    'method': 'Floating point evaluation of the exact positive two-component recurrence',
    'role': 'Corroboration only, not a proof or interval certificate',
    'rows': rows,
}, indent=2) + '\n')

for row in rows:
    if abs(row['k'] / row['N']**0.6 - 1) < 0.005:
        print(row['N'], row['k'], row['parity'], row['after_quartic'], row['predicted_quintic'], row['full_exponent_error'])
