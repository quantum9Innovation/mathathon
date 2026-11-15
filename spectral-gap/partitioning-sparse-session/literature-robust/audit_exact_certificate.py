"""Independent integer checks; writes only in this audit directory."""
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True
import numpy as np

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
SOURCE = PARENT / "exact_kernel_certificate.py"
spec = importlib.util.spec_from_file_location("audited_certificate", SOURCE)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def det_bareiss(matrix):
    """Exact integer determinant using fraction-free condensation."""
    a = [[int(x) for x in row] for row in matrix]
    n = len(a)
    if not n:
        return 1
    previous, sign = 1, 1
    for k in range(n - 1):
        if a[k][k] == 0:
            candidate = next((j for j in range(k + 1, n) if a[j][k]), None)
            if candidate is None:
                return 0
            a[k], a[candidate] = a[candidate], a[k]
            sign *= -1
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
        for i in range(k + 1, n):
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def integer_residual(matrix, vector):
    return [sum(int(x) * int(y) for x, y in zip(row, vector)) for row in matrix]


rng = random.Random(880133)
checks = []
for n in (0, 1, 2, 3, 5, 10, 20):
    for trial in range(10):
        a = np.array([[rng.randint(-7, 7) for _ in range(n)] for _ in range(n)], dtype=np.int64).reshape(n, n)
        rhs = np.array([rng.randint(-7, 7) for _ in range(n)], dtype=np.int64)
        det = det_bareiss(a)
        for prime in (1009, 1013, 1019):
            result = mod.solve_mod(a, rhs, prime)
            assert (result is None) == (det % prime == 0)
            if result is not None:
                solution, actual_det = result
                assert actual_det == det % prime
                res = integer_residual(a, solution)
                assert all((r - int(s)) % prime == 0 for r, s in zip(res, rhs))
            checks.append({"size": n, "trial": trial, "prime": prime, "singular_mod_p": det % prime == 0})

# Explicit pivot swap, modular singularity without real singularity, and real singularity.
for a in (
    np.array([[0, 1], [1, 0]], dtype=np.int64),
    np.array([[1009, 0], [0, 1]], dtype=np.int64),
    np.array([[1, 2], [2, 4]], dtype=np.int64),
):
    for prime in (1009, 1013, 1019):
        result = mod.solve_mod(a, np.ones(2, dtype=np.int64), prime)
        assert (result is None) == (det_bareiss(a) % prime == 0)

example = json.loads((PARENT / "example-certificate.json").read_text())
n = example["vertices"]
a = [[0] * n for _ in range(n)]
for i, j in example["edges"]:
    assert i != j and a[i][j] == 0
    a[i][j] = a[j][i] = 1
cert = example["certificate"]
lam = cert["eigenvalue"]
m = [row.copy() for row in a]
for i in range(n):
    m[i][i] -= lam
labels = cert["labels"]
assert len(labels) == n and set(labels) == {-1, 1} and sum(labels) == 0
assert all(x == 0 for x in integer_residual(m, labels))
cofactor = det_bareiss([row[1:] for row in m[1:]])
assert cofactor != 0
assert cofactor % cert["prime"] == cert["cofactor_determinant_mod_prime"]
again = mod.certify(np.array(a, dtype=np.int64), lam)
assert again == cert
degree = sum(a[0])
for i in range(n):
    assert sum(a[i]) == degree
    same = sum(a[i][j] for j in range(n) if labels[i] == labels[j])
    cross = degree - same
    assert (same, cross) == (4, 3)

# Exhaustive regular graphs through six vertices and all feasible eigenvalues.
# Whenever the API accepts, count every balanced sign eigenvector independently.
small_graphs, small_accepts = 0, 0
for size in (2, 4, 6):
    edges = [(i, j) for i in range(size) for j in range(i + 1, size)]
    for bits in range(1 << len(edges)):
        a = np.zeros((size, size), dtype=np.int64)
        for k, (i, j) in enumerate(edges):
            if bits & (1 << k):
                a[i, j] = a[j, i] = 1
        degrees = list(map(int, a.sum(axis=1)))
        if len(set(degrees)) != 1:
            continue
        small_graphs += 1
        for lam in range(-degrees[0], degrees[0] + 1):
            cert = mod.certify(a, lam)
            if not cert["status"].startswith("CERTIFIED"):
                continue
            count = 0
            for signbits in range(1 << size):
                signs = [1 if signbits & (1 << i) else -1 for i in range(size)]
                if sum(signs):
                    continue
                residual = integer_residual(a, signs)
                if all(r == lam * s for r, s in zip(residual, signs)):
                    count += 1
            assert count == 2
            small_accepts += 1

report = {
    "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    "modular_random_system_checks": len(checks),
    "explicit_special_matrices": 3,
    "example_vertices": n,
    "example_exact_integer_cofactor": str(cofactor),
    "example_cofactor_mod_prime": cofactor % example["certificate"]["prime"],
    "small_regular_graphs_exhaustively_checked": small_graphs,
    "accepted_small_graph_eigenvalue_pairs": small_accepts,
    "status": "PASS",
}
(HERE / "EXACT_CERTIFICATE_CHECKS.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
