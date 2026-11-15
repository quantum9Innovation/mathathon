from pathlib import Path
from math import isqrt
import hashlib
import json
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent
mp.mp.dps = 80

lam, h = sp.symbols('lambda h')
raw = {}
for degree in range(5):
    raw[degree] = sum(sp.functions.combinatorial.numbers.stirling(degree, r, kind=2) * lam**r * (1 if r % 2 == 0 else h) for r in range(degree + 1))
even_centered = sp.expand(raw[4] - 2 * lam**2 * raw[2] + lam**4)
assert sp.expand(even_centered - (4 * lam**3 * h + 7 * lam**2 + lam * h)) == 0
odd_shifted = {}
for degree in range(5):
    odd_shifted[degree] = sp.expand(sum(sp.binomial(degree, r) * (-1)**(degree-r) * raw[r] for r in range(degree + 1)))
q = lam * h - 1
assert sp.expand(odd_shifted[1] - q) == 0
assert sp.expand(odd_shifted[2] - (lam**2 - q)) == 0
assert sp.expand(odd_shifted[3] - (lam**2 + lam**2 * q + q)) == 0
assert sp.expand(odd_shifted[4] - 2 * lam**2 * odd_shifted[2] + lam**4 - (3 * lam**2 + (4 * lam**2 - 1) * q)) == 0

moment_checks = 0
for value in ['0.00000001', '0.0001', '0.01', '0.1', '0.5', '1', '2', '5', '10', '100']:
    z = mp.mpf(value)
    b = min(z, z*z)
    for epsilon in [0, 1]:
        t = mp.tanh(z) if epsilon == 0 else mp.coth(z)
        raw_moments = [mp.mpf(str(raw[r].subs({lam: sp.Float(value, 100), h: sp.Float(str(t), 100)}).evalf(90))) for r in range(5)]
        shifted = [sum(mp.mpf(int(sp.binomial(d, r))) * (-epsilon)**(d-r) * raw_moments[r] for r in range(d + 1)) for d in range(5)]
        first, second, third, fourth = shifted[1:]
        slack = mp.mpf('1e-65')
        assert first <= b + slack
        assert abs(second - z*z) <= b + slack
        assert second <= 2*z*z + slack
        assert third <= z**3 + 4*z*z + slack
        assert fourth - 2*z*z*second + z**4 <= 4*z**3 + 8*z*z + slack
        moment_checks += 5

availability_checks = 0
for m in range(1, 81):
    for epsilon in [0, 1]:
        for s in range(2*m + 6):
            w = mp.mpf(1)
            if s > m - epsilon:
                w = mp.mpf(0)
            else:
                for j in range(s):
                    w *= mp.mpf(m - epsilon - j) / m
            a = mp.mpf(s) * (s - 1 + 2*epsilon) / (2*m)
            gap = mp.exp(-a) - w
            assert gap >= -mp.mpf('1e-65')
            assert gap <= mp.mpf(4)*s**3/m**2 + mp.mpf('1e-65')
            availability_checks += 1


def ratios(n, limit):
    values = {}
    even = mp.mpf(1)
    odd = mp.mpf(1)
    for m in range(1, (limit + 1)//2 + 1):
        even = mp.mpf(n)/(n - 2*m + 1)*even + mp.mpf(4*(2*m - 1)*(2*m - 2))/(3*(n - 2*m + 1))*odd
        if 2*m <= limit:
            values[2*m] = even
        if 2*m + 1 <= limit:
            odd = mp.mpf(3*n)/((n - 2*m)*(2*m + 1))*even + mp.mpf((2*m - 2)*n)/((n - 2*m)*(2*m + 1))*odd
            values[2*m + 1] = odd
    return values


def parameters(n, k):
    m = k//2
    base = 2*m
    z = mp.mpf(2)/3 * mp.sqrt(mp.mpf(base)**3/n)
    eta = mp.mpf(3)*base**2/(4*n)
    comparison = mp.cosh(z) if k % 2 == 0 else mp.sinh(z)/z
    return m, base, z, eta, comparison


def local_bound(n, k, log_d):
    m, base, z, eta, _ = parameters(n, k)
    b = min(z, z*z)
    big_b = ((2 + 3*eta)*b + 2*eta**2 + 3*eta)/m
    big_b += (67*z**3 + (245 + 45*eta + 45*eta**2)*z*z + 10*eta**4 + 188*eta**3 + 457*eta*eta + 141*eta)/m**2
    r = mp.mpf(k)/(2*n) + mp.mpf(k)**3/(3*n*n)
    tau = mp.mpf(2)*base**mp.mpf('2.5')/mp.mpf(n)**mp.mpf('1.5')
    zeta = mp.mpf(2)*base/n
    return mp.expm1(r) + mp.exp(log_d - mp.mpf(k*k)/(4*n) + eta)*(big_b + (1 + zeta)*mp.exp(tau) - 1)


def uniform_constants(c):
    c = mp.mpf(c)
    a = 3*c*c/4
    b1 = mp.mpf(4)/3*(2 + 3*a)*mp.sqrt(c) + mp.mpf(2144)/27*c**mp.mpf('2.5')
    b2 = mp.mpf(3)/2*(2*a + 3)*c + mp.mpf(16)/9*(245 + 45*a + 45*a*a)*c
    b3 = 3*(10*a**3 + 188*a*a + 457*a + 141)
    a1 = mp.exp(7*c*c/4)*b1 + 2*mp.exp(11*c*c/4)*c**mp.mpf('2.5')
    a2 = mp.exp(7*c*c/4)*b2 + 2*mp.exp(11*c*c/4)*c + mp.exp(c*c/3)*(c/2 + c**3/3)
    a3 = mp.exp(7*c*c/4)*b3
    return a1, a2, a3

finite_checks = 0
uniform_checks = 0
examples = []
for n in list(range(16, 257)) + [1024, 10000, 10**6, 10**8]:
    limit = min(n//4, 3*isqrt(n) + 1)
    computed = ratios(n, limit)
    if n <= 1024:
        selected = set(computed)
    else:
        selected = {2, 3, 4, 5, 10, 11}
        for c in [mp.mpf('0.25'), mp.mpf('0.5'), mp.mpf(1), mp.mpf(2), mp.mpf(3)]:
            even = 2*int(c*mp.sqrt(n)/2)
            selected.update([even, even + 1])
        selected = {k for k in selected if 2 <= k <= limit}
    log_d = mp.mpf(0)
    for k in range(1, limit + 1):
        log_d -= mp.log1p(-mp.mpf(k - 1)/n)
        if k not in selected:
            continue
        _, _, _, _, comparison = parameters(n, k)
        actual = computed[k]/(mp.exp(mp.mpf(k*k)/(4*n))*comparison) - 1
        bound = local_bound(n, k, log_d)
        assert abs(actual) <= bound + mp.mpf('1e-60'), (n, k)
        finite_checks += 1
        for c in [1, 2, 3]:
            if n >= 16*c*c and k <= c*mp.sqrt(n):
                constants = uniform_constants(c)
                rate_bound = constants[0]/mp.root(n, 4) + constants[1]/mp.sqrt(n) + constants[2]/n
                assert abs(actual) <= rate_bound + mp.mpf('1e-60'), (n, k, c)
                uniform_checks += 1
        if n in [10000, 10**6, 10**8] and k in [isqrt(n), isqrt(n) + 1, 2*isqrt(n), 2*isqrt(n) + 1]:
            examples.append({'N': n, 'k': k, 'corrected_relative_error': mp.nstr(actual, 20), 'N_quarter_scaled_error': mp.nstr(actual*mp.root(n, 4), 20), 'local_bound': mp.nstr(bound, 20)})

proof = ROOT/'square-root-rate-v1.md'
result = {
    'proof': proof.name,
    'proof_sha256': hashlib.sha256(proof.read_bytes()).hexdigest(),
    'symbolic_conditioned_moment_identities': 5,
    'conditioned_moment_inequality_cases': moment_checks,
    'pointwise_availability_cases': availability_checks,
    'finite_corrected_bound_cases': finite_checks,
    'uniform_rate_bound_cases': uniform_checks,
    'numeric_precision_decimal_digits': mp.mp.dps,
    'boundary_examples': examples,
    'scope': 'Exact symbolic moment identities and finite numerical corroboration. The general rate is proved in the frozen note, not inferred from these checks.'
}
(ROOT/'rate-checks-v1.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k:v for k,v in result.items() if k != 'boundary_examples'}, indent=2))
print('Boundary examples:', len(examples))
