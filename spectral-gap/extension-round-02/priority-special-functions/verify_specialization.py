from pathlib import Path
import json
import mpmath as mp


mp.mp.dps = 70
connection_rows = []
for N, k in [(3, 2), (3, 3), (8, 3), (8, 4), (12, 11), (12, 12)]:
    b = mp.mpf(N) / 2 - k
    mu = mp.mpf(N + 1) / 2
    exact = mp.factorial(k) * mp.laguerre(k, -N - 1, -N)
    first = mp.whitm(b, mu, N) / mp.factorial(N + 1)
    second = mp.whitw(b, mu, N) / mp.factorial(N - k)
    value = (
        mp.factorial(k)
        * mp.exp(-mp.mpf(N) / 2)
        * mp.power(N, mp.mpf(N) / 2)
        * (first + (-1) ** k * second)
    )
    discrepancy = abs(value / exact - 1)
    assert discrepancy < mp.mpf('1e-65')
    connection_rows.append({
        'N': N,
        'k': k,
        'Q': mp.nstr(exact, 25),
        'relative_discrepancy': mp.nstr(discrepancy, 12),
        'condition_number': mp.nstr(
            (first + second) / abs(first + (-1) ** k * second), 15
        ),
    })

proxy_rows = []
for N, k in [(100, 3), (1000, 3), (100, 10), (10000, 100), (10000, 101)]:
    mu = mp.mpf(N + 1) / 2
    b = mp.mpf(N) / 2 - k
    a = mu - b
    discriminant = mp.sqrt(4 * mu**2 - 4 * b * N + N**2)
    root = mp.sqrt(mu**2 - b**2)
    action = (
        discriminant / 2
        - b * mp.log((discriminant + N - 2 * b) / (2 * root))
        - mu * mp.log(
            (mu * discriminant + 2 * mu**2 - b * N) / (N * root)
        )
    )

    def equation(tau):
        return (
            tau * mp.sqrt(tau**2 + 4 * a) / 4
            + a * mp.asinh(tau / (2 * mp.sqrt(a)))
            - action
        )

    tau = mp.findroot(equation, action / mp.sqrt(a))
    phi = (
        ((mu / 2) * (tau**2 + 4 * a) / discriminant**2)
        ** mp.mpf('0.25')
        * mp.sqrt(N)
    )
    c_w = (
        (mu / 2) ** mp.mpf('-0.25')
        * ((b + mu) / mp.e) ** ((b + mu) / 2)
        / mp.factorial(N - k)
    )
    c_m = (
        (8 * mu) ** mp.mpf('0.25')
        * (2 * mu / mp.e) ** (2 * mu)
        * (mp.e / (b + mu)) ** ((b + mu) / 2)
        / mp.factorial(N + 1)
    )
    prefactor = (
        mp.factorial(k)
        * mp.exp(-mp.mpf(N) / 2)
        * mp.power(N, mp.mpf(N) / 2)
        * phi
    )
    proxy = prefactor * (
        c_m * mp.pcfd(-a - mp.mpf('0.5'), -tau)
        + (-1) ** k * c_w * mp.pcfd(-a - mp.mpf('0.5'), tau)
    )
    exact = mp.factorial(k) * mp.laguerre(k, -N - 1, -N)
    proxy_rows.append({
        'N': N,
        'k': k,
        'action': mp.nstr(action, 18),
        'tau': mp.nstr(tau, 18),
        'relative_error': mp.nstr(proxy / exact - 1, 18),
        'prefactor_ratio_minus_one': mp.nstr(c_m / c_w - 1, 18),
    })

record = {
    'precision_decimal_digits': mp.mp.dps,
    'mpmath_version': mp.__version__,
    'connection': connection_rows,
    'olver_proxy': proxy_rows,
    'role': 'Finite corroboration only. No numerical result is a proof premise.',
}
target = Path(__file__).with_name('FINITE_CHECKS-v1.json')
target.write_text(json.dumps(record, indent=2) + '\n')
print('Six exact connection checks passed. Five proxy values recorded.')
