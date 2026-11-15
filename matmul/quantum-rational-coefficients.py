"""Certify explicit rational coefficients for a 25-pole entropy rule.

This supplements quantum-product-certificate.py.  It encloses a reduced
Hermite interpolation problem, isolates its twelve real roots using
directed interval arithmetic, and rounds the resulting positive Stieltjes
residues DOWN and positive pole magnitudes UP.  The exported coefficients
are exact rational numbers.  See quantum-rational-coefficient-search.txt
for the reduction and error transfer; no numerical SDP solver is used.

Run with assertions enabled.  Only Python's standard library is required.
"""

import argparse
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN
from fractions import Fraction
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
_product_spec = importlib.util.spec_from_file_location(
    'quantum_product_certificate', Path(__file__).with_name('quantum-product-certificate.py'))
assert _product_spec is not None and _product_spec.loader is not None
product = importlib.util.module_from_spec(_product_spec)
_product_spec.loader.exec_module(product)


D = Decimal
PRECISION = 512
DOWN = Context(prec=PRECISION, rounding=ROUND_FLOOR)
UP = Context(prec=PRECISION, rounding=ROUND_CEILING)
NEAR = Context(prec=PRECISION, rounding=ROUND_HALF_EVEN)
EXPORT_DOWN = Context(prec=60, rounding=ROUND_FLOOR)
EXPORT_UP = Context(prec=60, rounding=ROUND_CEILING)
ZERO, ONE, TWO = D(0), D(1), D(2)


def point(x):
    return D(x), D(x)


def rational(x):
    x = Fraction(x)
    return DOWN.divide(D(x.numerator), D(x.denominator)), UP.divide(D(x.numerator), D(x.denominator))


def add(x, y):
    return DOWN.add(x[0], y[0]), UP.add(x[1], y[1])


def neg(x):
    return x[1].copy_negate(), x[0].copy_negate()


def sub(x, y):
    return add(x, neg(y))


def mul(x, y):
    return min(DOWN.multiply(a, b) for a in x for b in y), max(UP.multiply(a, b) for a in x for b in y)


def div(x, y):
    assert y[0] > 0 or y[1] < 0, 'Interval division includes zero.'
    return mul(x, (DOWN.divide(ONE, y[1]), UP.divide(ONE, y[0])))


def sqrt(x):
    assert x[0] >= 0
    return max(ZERO, NEAR.next_minus(NEAR.sqrt(x[0]))), NEAR.next_plus(NEAR.sqrt(x[1]))


def ln(x):
    assert x[0] > 0
    return NEAR.next_minus(NEAR.ln(x[0])), NEAR.next_plus(NEAR.ln(x[1]))


def midpoint(x):
    return NEAR.divide(NEAR.add(x[0], x[1]), TWO)


def sign(x):
    if x[0] > 0:
        return 1
    if x[1] < 0:
        return -1
    return 0


def polynomial(coefficients, x):
    result = point(0)
    for c in reversed(coefficients):
        result = add(mul(result, x), c)
    return result


def derivative(coefficients):
    return [mul(point(k), coefficients[k]) for k in range(1, len(coefficients))]


def interval_solve(matrix):
    """Enclose the exact solution of a nonsingular interval-enclosed system."""
    a = [[entry for entry in row] for row in matrix]
    n = len(a)
    assert all(len(row) == n+1 for row in a)
    pivot_relative_width = ZERO
    for k in range(n):
        pivot_row = max(range(k, n), key=lambda i: midpoint(a[i][k]).copy_abs())
        a[k], a[pivot_row] = a[pivot_row], a[k]
        pivot = a[k][k]
        assert sign(pivot), f'Uncertified pivot {k}.'
        pivot_relative_width = max(pivot_relative_width,
            UP.divide(UP.subtract(pivot[1], pivot[0]), midpoint(pivot).copy_abs()))
        for i in range(k+1, n):
            factor = div(a[i][k], pivot)
            for j in range(k+1, n+1):
                a[i][j] = sub(a[i][j], mul(factor, a[k][j]))
            a[i][k] = point(0)  # The exact eliminated entry is zero.
    solution = [point(0) for _ in range(n)]
    for i in reversed(range(n)):
        rhs = a[i][n]
        for j in range(i+1, n):
            rhs = sub(rhs, mul(a[i][j], solution[j]))
        solution[i] = div(rhs, a[i][i])
    return solution, pivot_relative_width


def rational_nodes():
    """Fix rational interpolation nodes; certify THEIR product directly."""
    logarithms, n0 = product.ganelius_log_nodes(12, product.pi_bounds())
    # The exact rational midpoint exponentials, rather than the original
    # transcendental Ganelius nodes, define this construction.
    values = []
    for interval in logarithms:
        center = product.NEAR.divide(product.NEAR.add(*interval), D(2))
        values.append(Fraction(product.NEAR.exp(center)))
    assert len(values) == len(set(values)) == 12
    return values, n0


def certify_product(nodes):
    logarithms = [product.ln(product.rational(node)) for node in nodes]
    constant = product.add(product.mul(product.exact(2), product.pi_bounds()), product.exact(4))[1]
    target = D('0.0000005')
    tail = product.UP.multiply(constant, product.exp_upper(D(-30)))
    assert tail < target
    pending = [(D(-30), D(0), 0)]
    accepted, visited, maximum_depth = 0, 0, 0
    maximum = D(0)
    partition = sha256()
    while pending:
        lo, hi, depth = pending.pop()
        visited += 1
        bound_d = product.cell_d_upper(lo, hi, logarithms)
        bound_e = product.UP.multiply(constant, product.UP.multiply(bound_d, bound_d))
        if bound_e <= target:
            accepted += 1
            maximum = max(maximum, bound_e)
            partition.update(f'{lo}\t{hi}\t{bound_e}\n'.encode())
            continue
        assert depth < 64 and visited < 1000000
        mid = product.NEAR.divide(product.NEAR.add(lo, hi), D(2))
        assert lo < mid < hi
        maximum_depth = max(maximum_depth, depth+1)
        pending.extend(((mid, hi, depth+1), (lo, mid, depth+1)))
    return {'visited': visited, 'accepted': accepted, 'max_depth': maximum_depth,
            'largest_cell_error': str(maximum), 'tail_error': str(tail),
            'partition_sha256': partition.hexdigest()}


def reduced_interpolant(nodes):
    """Enclose P/Q for A(y)=atanh(sqrt(y))/sqrt(y), type [12/12]."""
    n = len(nodes)
    rows = []
    # P(0)=Q(0), with Q monic of degree n.
    rows.append([point(1)] + [point(0)]*n + [point(-1)] + [point(0)]*(n-1) + [point(0)])
    for a in nodes:
        z_rational = (1-a)/(1+a)
        y_rational = z_rational*z_rational
        z, y = rational(z_rational), rational(y_rational)
        value = div(neg(ln(rational(a))), mul(point(2), z))
        slope = div(sub(div(point(1), sub(point(1), y)), value), mul(point(2), y))
        powers = [point(1)]
        for k in range(n):
            powers.append(mul(powers[-1], y))
        rows.append(powers + [neg(mul(value, powers[k])) for k in range(n)]
                    + [mul(value, powers[n])])
        p_derivatives = [point(0)] + [mul(point(k), powers[k-1]) for k in range(1, n+1)]
        q_derivatives = []
        for k in range(n):
            q_derivatives.append(neg(add(mul(slope, powers[k]),
                mul(value, p_derivatives[k]))))
        rhs = add(mul(slope, powers[n]), mul(value, p_derivatives[n]))
        rows.append(p_derivatives + q_derivatives + [rhs])
    solution, pivot_width = interval_solve(rows)
    return solution[:n+1], solution[n+1:]+[point(1)], pivot_width


def isolate_unit_roots(coefficients, width=D('1e-85')):
    """Bracket all roots, using real-rootedness and derivative interlacing.

    We certify one sign change for each degree, not a floating root count.
    Endpoints of every returned bracket are exact finite decimals.
    """
    degree = len(coefficients)-1
    if degree == 1:
        enclosure = div(neg(coefficients[0]), coefficients[1])
        assert ZERO < enclosure[0] <= enclosure[1] < ONE
        # Widen for strict signs at the endpoints.
        lo = DOWN.subtract(enclosure[0], width)
        hi = UP.add(enclosure[1], width)
        assert 0 < lo < hi < 1
        assert sign(polynomial(coefficients, point(lo))) * sign(polynomial(coefficients, point(hi))) == -1
        return [(lo, hi)]
    critical = isolate_unit_roots(derivative(coefficients), width)
    separators = [ZERO] + [midpoint(c) for c in critical] + [ONE]
    values = [sign(polynomial(coefficients, point(x))) for x in separators]
    assert all(values)
    assert all(a*b == -1 for a, b in zip(values, values[1:])), 'Root separation failed.'
    brackets = []
    for a, b, left_sign in zip(separators, separators[1:], values):
        lo, hi = a, b
        while UP.subtract(hi, lo) > width:
            mid = NEAR.divide(NEAR.add(lo, hi), TWO)
            mid_sign = sign(polynomial(coefficients, point(mid)))
            if mid_sign == 0:
                left = DOWN.subtract(mid, DOWN.divide(width, D(4)))
                right = UP.add(mid, DOWN.divide(width, D(4)))
                assert lo < left < right < hi
                assert sign(polynomial(coefficients, point(left))) == left_sign
                assert sign(polynomial(coefficients, point(right))) == -left_sign
                lo, hi = left, right
                break
            if mid_sign == left_sign:
                lo = mid
            else:
                hi = mid
        assert sign(polynomial(coefficients, point(lo))) == left_sign
        assert sign(polynomial(coefficients, point(hi))) == -left_sign
        brackets.append((lo, hi))
    assert len(brackets) == degree
    assert all(a[1] < b[0] for a, b in zip(brackets, brackets[1:]))
    return brackets


def fraction_json(value):
    value = Fraction(value)
    return [str(value.numerator), str(value.denominator)]


def build_rule(nodes):
    p, q, pivot_width = reduced_interpolant(nodes)
    p_reverse, q_reverse = list(reversed(p)), list(reversed(q))
    roots = isolate_unit_roots(q_reverse)
    pole_residue_intervals = [(point(1), p[-1])]
    weights = []
    q_prime = derivative(q_reverse)
    for root in roots:
        weight = div(polynomial(p_reverse, root), mul(root, polynomial(q_prime, root)))
        assert weight[0] > 0
        weights.append(weight)
        z = sqrt(root)
        t = div(sub(point(1), z), add(point(1), z))
        inverse_t = div(point(1), t)
        assert t[0] > 0
        for pole in (t, inverse_t):
            residue = div(mul(weight, pole), point(2))
            pole_residue_intervals.append((pole, residue))
    assert p[-1][0] > 0
    total_mass = p[-1]
    for weight in weights:
        total_mass = add(total_mass, weight)
    assert total_mass[0] <= 1 <= total_mass[1]
    assert len(pole_residue_intervals) == 25
    output = []
    kappa = Fraction(1)
    for pole, residue in pole_residue_intervals:
        pole_up = Fraction(EXPORT_UP.plus(pole[1]))
        residue_down = Fraction(EXPORT_DOWN.plus(residue[0]))
        assert pole_up > 0 and residue_down > 0
        # Uniform for x>0: residue_down/(x+pole_up) is between
        # this ratio times the ideal term, and the ideal term itself.
        ratio = residue_down/Fraction(residue[1]) * Fraction(pole[0])/pole_up
        assert 0 < ratio <= 1
        kappa = min(kappa, ratio)
        T = 1/(1+pole_up)
        u = residue_down/(1+pole_up)
        output.append({'pole_magnitude': fraction_json(pole_up),
                       'residue': fraction_json(residue_down),
                       'T': fraction_json(T), 'u': fraction_json(u)})
    return output, kappa, pivot_width, total_mass


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
        default=Path(__file__).with_name('quantum-entropy-rational-rule.json'))
    args = parser.parse_args()
    started = time.monotonic()
    nodes, n0 = rational_nodes()
    product_result = certify_product(nodes)
    coefficients, kappa, pivot_width, total_mass = build_rule(nodes)
    e = Fraction(1, 2000000)
    eta = 2*e/(1+e) + 2*(1-kappa)
    assert eta < Fraction(1, 1000000)
    payload = {'description': '25 positive rational Stieltjes terms: R0(x)=sum c/(x+t)',
               'normalization': 'f_lower(x)=(x-1)^2 R0(x)/(1+e)',
               'upper': 'f_upper(x)=f_lower(x)+eta*(x-1)^2/2',
               'e': fraction_json(e), 'eta': fraction_json(eta),
               'uniform_ideal_ratio_lower': fraction_json(kappa),
               'interpolation_nodes': [fraction_json(a) for a in nodes],
               'coefficients': coefficients,
               'product_certificate': product_result,
               'precision_decimal_digits': PRECISION,
               'export_significant_digits': 60}
    serialized = json.dumps(payload, indent=2)+'\n'
    args.output.write_text(serialized)
    print('CERTIFIED: 25 distinct positive ideal poles; 25 positive rational exported terms.')
    print('Product certificate:', json.dumps(product_result, sort_keys=True))
    print('Maximum relative interval pivot width (rounded display):', f'{pivot_width:.6E}')
    print('Ideal weight sum encloses one:', total_mass[0] <= 1 <= total_mass[1])
    print('1-kappa upper bound (rounded display):', f'{rational(1-kappa)[1]:.12E}')
    print('eta upper bound (rounded display):', f'{rational(eta)[1]:.12E}')
    print('CERTIFIED: f_lower <= x*log(x)-x+1 <= f_upper for every x>0.')
    print('CERTIFIED: entropy SDP bracket width = eta*chi_P^2/2, eta < 1e-6.')
    print('Exact rational JSON:', args.output)
    print('JSON SHA256:', sha256(serialized.encode()).hexdigest())
    print('Seconds:', round(time.monotonic()-started, 3))


if __name__ == '__main__':
    main()
