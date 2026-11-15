import json
import math
from pathlib import Path
import sys

import numpy as np

sys.path.insert(0, '.ultramath/smwgfcleu/m2/experiments')
from lib import hashimoto

checks = {}

# Direct counterexample to the stated complex equivalence.
lam = 2j
roots = np.roots([1, -lam, 1])
checks['proposition_4_complex_counterexample'] = {
    'k': 1,
    'lambda': str(lam),
    'root_moduli': sorted(np.abs(roots).tolist()),
}
assert not np.allclose(np.abs(roots), 1)
assert np.allclose(roots ** 2 - lam * roots + 1, 0, atol=1e-12)

# Actual cycle-index calculation on all lengths of nontrivial closed walks.
def period(a, limit=None):
    n = a.shape[0]
    if limit is None:
        limit = 5 * n
    p = np.eye(n, dtype=bool)
    a = a.astype(bool)
    value = 0
    for length in range(1, limit + 1):
        p = (p @ a).astype(bool)
        if np.any(np.diag(p)):
            value = math.gcd(value, length)
            if value == 1:
                break
    return value

G = [(i, 3+j) for i in range(3) for j in range(3)]
line, arcs = hashimoto(G)
p3 = np.array([[0,1,0],[0,0,1],[1,0,0]])
constructed = np.kron(p3, line)
source_period = period(line)
actual_period = period(constructed)
checks['period_lifting_counterexample'] = {
    'source': 'line digraph of K3,3',
    'claimed_lift_period': 3,
    'source_period': source_period,
    'actual_period_with_P3_tensor_product': actual_period,
    'expected_lcm': math.lcm(2,3),
    'regular_degrees': sorted(set(constructed.sum(axis=0).tolist())),
    'top_eigenvalue_moduli': [float(x) for x in sorted(np.abs(np.linalg.eigvals(constructed)), reverse=True)[:8]],
}
assert source_period == 2
assert constructed.sum(axis=0).min() == constructed.sum(axis=0).max() == 2
assert actual_period == 6

# Symmetric adjacency does not change the signed second eigenvalue into a singular value.
k4 = np.ones((4,4)) - np.eye(4)
eigenvalues = np.linalg.eigvalsh(k4)
singular = np.linalg.svd(k4, compute_uv=False)
checks['symmetric_sigma_two_counterexample'] = {
    'eigenvalues': eigenvalues.tolist(),
    'lambda_2': float(eigenvalues[-2]),
    'sigma_2': float(singular[1]),
}
assert abs(eigenvalues[-2] - singular[1]) > 1

# The claimed regular-tree walk count omits the root degree.
t = 1
claimed = (2-1)**t * 1
actual = 2
checks['tree_walk_count_k_2_t_1'] = {'claimed': claimed, 'actual_closed_length_2_walks_from_root': actual}
assert claimed != actual

path = Path(__file__).with_suffix('.json')
path.write_text(json.dumps(checks, indent=2) + '\n')
print(path)
print(json.dumps(checks, indent=2))
