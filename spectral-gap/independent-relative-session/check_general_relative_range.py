"""High-precision diagnostics for the general relative spectral range.

This is independent of the root scripts. It checks arbitrary SPD scaling,
signed input spectra, Araki prefix inequalities, and compact-family rank-one
limits. It is not a proof, novelty certificate, or stable floating-point
implementation for arbitrarily ill-conditioned inputs.
"""

import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 320


def diagonal(values):
    return mp.diag([mp.mpf(x) for x in values])


def power(matrix, exponent):
    values, vectors = mp.eigsy(matrix)
    assert values[0] > 0
    return vectors * mp.diag([x ** exponent for x in values]) * vectors.T


def symmetric(matrix):
    return (matrix + matrix.T) / 2


def relative(s, alpha, delta):
    n = s.rows
    a = [delta ** (n - 1 - i) for i in range(n)]
    root_a = diagonal([mp.sqrt(x) for x in a])
    inv_a = diagonal([x ** (-alpha / 2) for x in a])
    b = root_a * s * root_a
    return symmetric(inv_a * power(b, alpha) * inv_a)


def reverse_pivots(s):
    determinants = [mp.det(s[i:s.rows, i:s.rows]) for i in range(s.rows)]
    determinants.append(mp.mpf(1))
    return [determinants[i] / determinants[i + 1] for i in range(s.rows)]


def rank_one_s(x):
    r = [mp.exp(t) for t in x]
    z = [(r[i] - 1) * mp.fprod(r[i + 1:]) for i in range(len(r))]
    v = mp.matrix([mp.sqrt(t) for t in z])
    return mp.eye(len(r)) + v * v.T


def main():
    triangular = mp.matrix([[mp.mpf('.7'), mp.mpf('.3'), mp.mpf('-.2'), mp.mpf('.1')],
                            [0, mp.mpf('1.1'), mp.mpf('.5'), mp.mpf('-.2')],
                            [0, 0, mp.mpf('1.5'), mp.mpf('.4')],
                            [0, 0, 0, mp.mpf('2')]])
    signed = triangular * triangular.T
    v = mp.matrix([mp.mpf('.2'), mp.mpf('.7'), mp.mpf('1.1')])
    w = mp.matrix([mp.mpf('.5'), mp.mpf('-.3'), mp.mpf('.4')])
    positive = mp.eye(3) + v * v.T + w * w.T
    examples = [('signed_general', signed), ('rank_two_positive', positive),
                ('rank_one_unequal', rank_one_s([mp.mpf('.6'), mp.mpf('.3'), mp.mpf('.1')])),
                ('rank_one_collision', rank_one_s([mp.mpf('.3')] * 3))]
    alphas = [mp.mpf('.2'), mp.mpf('.5'), mp.mpf('.8')]
    deltas = [mp.mpf('.1'), mp.mpf('1e-5'), mp.mpf('1e-20'), mp.mpf('1e-50')]
    records = []
    max_araki_violation = mp.mpf(0)
    max_logdet_error = mp.mpf(0)
    for label, s in examples:
        input_values = sorted(mp.eigsy(s, eigvals_only=True), reverse=True)
        pivots = reverse_pivots(s)
        for alpha in alphas:
            target = diagonal([d ** alpha for d in pivots])
            rows = []
            for delta in deltas:
                q_matrix = relative(s, alpha, delta)
                q = sorted(mp.eigsy(q_matrix, eigvals_only=True), reverse=True)
                x = [mp.log(t) for t in q]
                y = [alpha * mp.log(t) for t in input_values]
                violations = [mp.fsum(x[:k]) - mp.fsum(y[:k])
                              for k in range(1, s.rows)]
                violation = max([mp.mpf(0)] + violations)
                determinant_error = abs(mp.fsum(x) - mp.fsum(y))
                max_araki_violation = max(max_araki_violation, violation)
                max_logdet_error = max(max_logdet_error, determinant_error)
                assert violation < mp.mpf('1e-100')
                assert determinant_error < mp.mpf('1e-100')
                distance = max(abs(t) for t in mp.eigsy(symmetric(q_matrix - target), eigvals_only=True))
                rows.append({'delta': str(delta), 'operator_error': float(distance),
                             'spectrum': [float(t) for t in q],
                             'logdet_error': float(determinant_error)})
            assert rows[-1]['operator_error'] < 3e-4
            assert rows[-1]['operator_error'] < rows[0]['operator_error'] / 1000
            records.append({'case': label, 'alpha': float(alpha),
                            'input_spectrum': [float(t) for t in input_values],
                            'reverse_pivots': [float(t) for t in pivots], 'rows': rows})

    output = {'precision_decimal_digits': mp.mp.dps, 'matrix_cases': len(examples),
              'total_evaluations': len(examples) * len(alphas) * len(deltas),
              'maximum_araki_prefix_violation': float(max_araki_violation),
              'maximum_logdet_error': float(max_logdet_error), 'records': records,
              'scope': 'High-precision diagnostics; proofs and historical priority are separate.'}
    destination = Path(__file__).with_suffix('.json')
    destination.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({key: output[key] for key in ('precision_decimal_digits', 'matrix_cases',
                     'total_evaluations', 'maximum_araki_prefix_violation', 'maximum_logdet_error')}))


if __name__ == '__main__':
    main()
