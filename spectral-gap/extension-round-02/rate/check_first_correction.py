from pathlib import Path
import hashlib
import json
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent
mp.mp.dps = 80
j, ell, z, eta, eps, m = sp.symbols('J L lambda eta epsilon m')
a = sp.Rational(3, 2)
s = a*j + 2*ell - a*eps
quadratic = s*(s - 1 + 2*eps)/(2*m)
delta = sp.Rational(9, 8)*z*z/m


def poisson_raw(order, mean):
    return sum(sp.functions.combinatorial.numbers.stirling(order, r, kind=2)*mean**r for r in range(order + 1))


def expect(poly):
    result = 0
    for powers, coeff in sp.Poly(sp.expand(poly), j, ell).terms():
        result += coeff*poisson_raw(powers[0], z)*poisson_raw(powers[1], eta)
    return sp.expand(result)

mean_shift = expect(quadratic - delta)
assert sp.simplify(sp.expand(mean_shift).coeff(z, 1) - (3*eta + sp.Rational(3, 8)*(1 - 2*eps))/m) == 0
second_shift = expect((quadratic - delta)**2)
assert sp.expand(second_shift).coeff(z, 4) == 0
assert sp.expand(second_shift).coeff(z, 3) == sp.Rational(81, 16)/m**2
assert a**4/2 - a**3/6 == sp.Rational(63, 32)
assert -3 + sp.Rational(7, 3) + sp.Rational(4, 5) == sp.Rational(2, 15)
assert -sp.Rational(1, 2) + sp.Rational(2, 15) == -sp.Rational(11, 30)
assert sp.Rational(1, 2) + sp.Rational(2, 15) == sp.Rational(19, 30)


def ratios(n, limit):
    values = {}
    even = mp.mpf(1)
    odd = mp.mpf(1)
    for mm in range(1, (limit + 1)//2 + 1):
        even = mp.mpf(n)/(n - 2*mm + 1)*even + mp.mpf(4*(2*mm - 1)*(2*mm - 2))/(3*(n - 2*mm + 1))*odd
        if 2*mm <= limit:
            values[2*mm] = even
        if 2*mm + 1 <= limit:
            odd = mp.mpf(3*n)/((n - 2*mm)*(2*mm + 1))*even + mp.mpf((2*mm - 2)*n)/((n - 2*mm)*(2*mm + 1))*odd
            values[2*mm + 1] = odd
    return values


examples = []
for n in [10**4, 10**6, 10**8, 10**10]:
    cases = []
    for c in [mp.mpf('0.5'), mp.mpf(1), mp.mpf(2)]:
        even_k = 2*int(c*mp.sqrt(n)/2)
        cases.extend([(c, even_k), (c, even_k + 1)])
    values = ratios(n, max(k for _, k in cases))
    for c, k in cases:
        base = 2*(k//2)
        lam = mp.mpf(2)/3*mp.sqrt(mp.mpf(base)**3/n)
        h = mp.cosh(lam) if k % 2 == 0 else mp.sinh(lam)/lam
        w = values[k]/(mp.exp(mp.mpf(k*k)/(4*n))*h)
        scaled = (w - 1)*mp.root(n, 4)
        parity = 2*(k % 2) - 1
        limiting = parity*mp.sqrt(c)/2 + mp.mpf(2)/15*c**mp.mpf('2.5')
        finite_prediction = parity*mp.sqrt(mp.mpf(base)/n)/2 + mp.mpf(2)/15*mp.mpf(base)**mp.mpf('2.5')/mp.mpf(n)**mp.mpf('1.5')
        examples.append({
            'N': n,
            'k': k,
            'parity': 'even' if k % 2 == 0 else 'odd',
            'target_c': mp.nstr(c, 20),
            'scaled_corrected_error': mp.nstr(scaled, 24),
            'predicted_limit': mp.nstr(limiting, 24),
            'difference_from_limit': mp.nstr(scaled - limiting, 24),
            'scaled_residual_after_finite_correction': mp.nstr(mp.root(n, 4)*(w - 1 - finite_prediction), 24)
        })

for row in examples:
    if row['N'] == 10**10:
        assert abs(mp.mpf(row['difference_from_limit'])) < mp.mpf('0.01')

proof = ROOT/'first-correction-v1.md'
result = {
    'proof': proof.name,
    'proof_sha256': hashlib.sha256(proof.read_bytes()).hexdigest(),
    'symbolic_coefficient_identities': 7,
    'numerical_precision_decimal_digits': mp.mp.dps,
    'examples': examples,
    'scope': 'Exact symbolic coefficient checks and finite numerical corroboration. The general signed limits and rate optimality depend on the written proof.'
}
(ROOT/'first-correction-checks-v1.json').write_text(json.dumps(result, indent=2) + '\n')
print('Seven symbolic identities passed')
for row in examples:
    if row['N'] == 10**10:
        print(row['k'], row['parity'], row['scaled_corrected_error'], row['predicted_limit'])
