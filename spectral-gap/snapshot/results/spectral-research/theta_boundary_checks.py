import json
from pathlib import Path

import sympy as sp

z, x = sp.symbols('z x')
cavity = 3*z*x**2 + (z*z+1)*x + z

# Symmetric left mode with two external branches at each right vertex.
secular = sp.factor(sp.cancel(cavity.subs(x, (6-z**2)/(2*z))).as_numer_denom()[0])
roots = sp.nroots(secular)
checks = []
for value in (sp.Rational(1,100), sp.Rational(1,20), sp.Rational(1,10), sp.Rational(1,5), sp.Rational(3,10)):
    discriminant = value**4 - 10*value**2 + 1
    branch = (-(value**2+1) - sp.sqrt(discriminant))/(6*value)
    residual = value*(value+2*branch)-6
    residual_by_complex_sqrt = complex(residual.evalf())
    assert abs(residual_by_complex_sqrt) > 1
    checks.append({'z': str(value), 'branch': [complex(branch.evalf()).real, complex(branch.evalf()).imag],
                   'symmetric_mode_residual': [residual_by_complex_sqrt.real, residual_by_complex_sqrt.imag]})

out = {
    'cavity_polynomial_in_x': str(cavity),
    'symmetric_mode_eliminant': str(secular),
    'roots': [str(root) for root in roots],
    'inner_edge': 3**.5-2**.5,
    'positive_roots_below_inner_edge': [str(root) for root in roots
        if abs(float(sp.im(root))) < 1.e-8 and 0 < float(sp.re(root)) < 3**.5-2**.5],
    'samples': checks,
}
assert secular == (z**2-12)*(z**2-10)
assert not out['positive_roots_below_inner_edge']
path = Path(__file__).with_suffix('.json')
path.write_text(json.dumps(out, indent=2) + '\n')
print(path)
print('The checked symmetric mode eliminant is', secular)
