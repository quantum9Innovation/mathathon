"""Independent review of Proposition 3 in the revised d4 dossier.

This does not import any member code.  It constructs the half-line Jacobi
operator directly from the sphere sizes of the stated tree, checks the exact
recursion, and checks the weighted l2 tail needed on the full tree.
"""
import json
from pathlib import Path

import sympy as sp

K = 80
lam = sp.sqrt(6)
u = [sp.Integer(1), sp.sqrt(2), sp.sqrt(sp.Rational(3, 2)),
     sp.Integer(1), sp.sqrt(3) / 2]
for k in range(5, K + 1):
    u.append(sp.simplify(u[k - 2] / sp.sqrt(2)))


def children(k):
    return 3 if k == 0 else (2 if k % 2 else 1)


def jacobi_entry(k):
    return sp.sqrt(children(k))


spheres = [sp.Integer(1)]
for k in range(K + 1):
    spheres.append(spheres[-1] * children(k))
assert all(jacobi_entry(k) ** 2 == spheres[k + 1] / spheres[k]
           for k in range(K + 1))

root_residual = sp.simplify(jacobi_entry(0) * u[1] - lam * u[0])
residuals = [sp.simplify(jacobi_entry(k - 1) * u[k - 1]
                         + jacobi_entry(k) * u[k + 1] - lam * u[k])
             for k in range(1, K)]
assert root_residual == 0
assert all(r == 0 for r in residuals)
assert all(sp.simplify(u[k + 2] * sp.sqrt(2) - u[k]) == 0
           for k in range(3, K - 1))

# A radial lift takes value u[k]/sqrt(|S_k|) on each vertex of S_k.
# Its squared norm is sum(u[k]^2).  The two blocks after the initial terms
# make this sum particularly simple.
initial_norm = sp.simplify(sum(x * x for x in u[:5]))
odd_tail = sp.simplify(sum(u[k] ** 2 for k in range(5, K + 1, 2)))
even_tail = sp.simplify(sum(u[k] ** 2 for k in range(6, K + 1, 2)))
assert initial_norm == sp.Rational(25, 4)
assert odd_tail == 1 - sp.Rational(1, 2) ** ((K - 3) // 2)
assert even_tail == sp.Rational(3, 4) * odd_tail

# The full-tree radial lift is f(x) = u[k]/sqrt(|S_k|) for x in S_k.
# Hence the squared mass of S_k is exactly u[k]^2, with no further
# sphere-growth factor.  This distinction is essential for the l2 check.
shell_masses = [sp.simplify(spheres[k] * (u[k] / sp.sqrt(spheres[k])) ** 2)
                for k in range(K + 1)]
assert all(m == sp.simplify(u[k] ** 2) for k, m in enumerate(shell_masses))
assert all(sp.simplify(shell_masses[k + 2] / shell_masses[k])
           == sp.Rational(1, 2) for k in range(3, K - 1))

x = sp.symbols('x', real=True)
floquet_margin = sp.expand((x ** 2 - 3) ** 2 - 8)
assert floquet_margin.subs(x, lam) == 1
assert sp.simplify(lam - (sp.sqrt(2) + 1)) == sp.sqrt(6) - sp.sqrt(2) - 1
assert sp.sqrt(6) > sp.sqrt(2) + 1

report = {
    'independent_member_code_used': False,
    'root_residual': str(root_residual),
    'exact_inner_residuals_checked': len(residuals),
    'all_exact_residuals_zero': True,
    'jacobi_coefficients_squared_match_sphere_growth': True,
    'unnormalised_radial_l2_sum': '8',
    'initial_five_squared_terms': str(initial_norm),
    'odd_tail_at_K': str(odd_tail),
    'even_tail_at_K': str(even_tail),
    'normalised_full_tree_shell_masses': 'u[k]^2 for every checked shell',
    'two_step_normalised_shell_mass_ratios': '1/2 for every checked tail index',
    'floquet_polynomial_at_lambda': str(floquet_margin),
    'floquet_margin_at_sqrt6': str(floquet_margin.subs(x, lam)),
    'strict_excess_over_band_top': str(sp.sqrt(6) - sp.sqrt(2) - 1),
    'status': 'passed',
}
path = Path(__file__).with_suffix('.json')
path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
