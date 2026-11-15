"""Reproduce unequal diagnostics and check an odd-block irrational example."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import numpy as np

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
sys.path.insert(0, str(PARENT))
SOURCE = PARENT / "check_unequal_blocks.py"
spec = importlib.util.spec_from_file_location("unequal_diagnostics_audited", SOURCE)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
destination = HERE / "reproduced-unequal"
destination.mkdir(exist_ok=True)
# Only the output destination is redirected. Implementation stays unmodified.
mod.__file__ = str(destination / SOURCE.name)
mod.main()
identical = {}
for name in ("unequal-block-checks.json", "unequal-block-example.json"):
    identical[name] = (destination / name).read_bytes() == (PARENT / name).read_bytes()
    assert identical[name]

# C_14(+/-1,+/-2), C_7(+/-1,+/-2), with14crossstubs split2per rightvertex.
# Q=[[4,1],[2,4]] has irreducible quotient polynomial(t-4)^2-2.
n1, n2 = 14, 7
a = np.zeros((n1 + n2, n1 + n2), dtype=object)
for offset, size in ((0, n1), (n1, n2)):
    for i in range(size):
        for step in (1, 2):
            j = (i + step) % size
            a[offset + i, offset + j] = a[offset + j, offset + i] = 1
for i in range(n1):
    a[i, n1 + i % n2] = a[n1 + i % n2, i] = 1
assert all(sum(a[i, :n1]) == 4 and sum(a[i, n1:]) == 1 for i in range(n1))
assert all(sum(a[i, :n1]) == 2 and sum(a[i, n1:]) == 4 for i in range(n1, n1 + n2))
reached = {0}
frontier = [0]
while frontier:
    i = frontier.pop()
    for j in range(len(a)):
        if a[i, j] and j not in reached:
            reached.add(j)
            frontier.append(j)
assert len(reached) == len(a)

# Faddeev--LeVerrier with Python integers, exact divisibility every step.
size = len(a)
eye = np.eye(size, dtype=object)
work = eye.copy()
characteristic = [1]
for k in range(1, size + 1):
    product = a @ work
    tr = sum(product[i, i] for i in range(size))
    assert tr % k == 0
    ck = -tr // k
    characteristic.append(int(ck))
    work = product + ck * eye
assert np.all(work == 0)


def divide_monic(coefficients, divisor):
    rest = list(coefficients)
    quotient = []
    for i in range(len(coefficients) - len(divisor) + 1):
        term = rest[i]
        quotient.append(term)
        for j, d in enumerate(divisor):
            rest[i + j] -= term * d
    return quotient, rest[-len(divisor) + 1 :]


f = [1, -8, 14]
quotient, remainder = divide_monic(characteristic, f)
assert all(x == 0 for x in remainder)
_, second_remainder = divide_monic(quotient, f)
assert any(x != 0 for x in second_remainder)
report = {
    "unequal_source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    "rerun_samples": 48,
    "json_byte_identical": identical,
    "irrational_example": {
        "vertices": size, "block_sizes": [n1, n2], "connected": True,
        "quotient": [[4, 1], [2, 4]],
        "characteristic_polynomial_coefficients_descending": characteristic,
        "irreducible_quotient_polynomial_descending": f,
        "quotient_polynomial_multiplicity": 1,
        "after_first_division_remainder": remainder,
        "after_second_division_remainder": second_remainder,
    },
    "status": "PASS",
}
(HERE / "SUPPLEMENT_CHECKS.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"status": report["status"], "rerun_samples": 48,
                  "json_byte_identical": identical, "irrational_example_vertices": size}))
