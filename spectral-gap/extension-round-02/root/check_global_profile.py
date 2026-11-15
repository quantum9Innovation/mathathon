"""Compare the candidate global error profile with the positive recurrence."""

import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 65


def ratios(n, targets):
    answers = {}
    even = mp.mpf(1)
    odd = mp.mpf(1)
    for m in range(1, max(targets) // 2 + 1):
        even = mp.mpf(n) / (n - 2*m + 1) * even + mp.mpf(4*(2*m - 1)*(2*m - 2)) / (3*(n - 2*m + 1)) * odd
        if 2*m in targets:
            answers[2*m] = even
        if 2*m + 1 <= n:
            odd = mp.mpf(3*n) / ((n - 2*m)*(2*m + 1)) * even + mp.mpf((2*m - 2)*n) / ((n - 2*m)*(2*m + 1)) * odd
            if 2*m + 1 in targets:
                answers[2*m + 1] = odd
    return answers


def scaled_error(n, k, ratio):
    base = k - k % 2
    x = mp.sqrt(mp.mpf(base) / n)
    lam = mp.mpf(2) * base * x / 3
    q = x + (x*x - 1)*mp.log1p(x) - x*x/2 - 2*x**3/3
    log_d = k*mp.log(n) - mp.loggamma(n+1) + mp.loggamma(n-k+1)
    hyperbolic = mp.cosh(lam) if k % 2 == 0 else mp.sinh(lam)/lam
    log_a = log_d + mp.log(hyperbolic) + n*q + (k % 2 - mp.mpf('0.5'))*mp.log1p(x)
    return mp.root(n, 3)*mp.expm1(mp.log(ratio)-log_a)


def profile(c, parity):
    lam = mp.mpf(2)*c**mp.mpf('1.5')/3
    p = lam*mp.tanh(lam) if parity == 0 else lam*mp.coth(lam)-1
    return 3*(2*parity-1)*(p-lam)/(4*c)


rows = []
for n in [10**4, 10**6, 10**8, 10**10]:
    targets = set()
    for c in map(mp.mpf, ['0.1', '0.25', '0.5', '0.75', '1', '1.5', '2', '4', '8']):
        even = max(2, 2*int(c*mp.root(n, 3)/2))
        targets.update([even, even+1])
    for k, ratio in ratios(n, targets).items():
        c = mp.mpf(k)/mp.root(n, 3)
        actual = scaled_error(n, k, ratio)
        predicted = profile(c, k % 2)
        rows.append({'N': n, 'k': k, 'c': mp.nstr(c, 18),
                     'scaled_error': mp.nstr(actual, 24),
                     'predicted_profile': mp.nstr(predicted, 24),
                     'difference': mp.nstr(actual-predicted, 18)})

maximizing_c = mp.findroot(lambda c: mp.diff(lambda y: -profile(y, 1), c), (mp.mpf('0.8'), mp.mpf('1.2')))
record = {'status': 'exploratory', 'precision_decimal_digits': mp.mp.dps,
          'candidate_maximizing_c': mp.nstr(maximizing_c, 30),
          'candidate_maximum_absolute_profile': mp.nstr(-profile(maximizing_c, 1), 30),
          'rows': rows,
          'scope': 'Finite numerical diagnostics of a proposed theorem. No proof or uniqueness certificate.'}
Path(__file__).with_name('global-profile-checks.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps({key: value for key, value in record.items() if key != 'rows'}, indent=2))
print('Checked profiles:', len(rows))
print('Largest discrepancy at final dimension:', max(abs(mp.mpf(row['difference'])) for row in rows if row['N'] == 10**10))
