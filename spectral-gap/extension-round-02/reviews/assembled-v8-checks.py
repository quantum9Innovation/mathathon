import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp


parser = argparse.ArgumentParser()
root = Path(__file__).resolve().parents[2]
parser.add_argument(
    "--snapshot",
    type=Path,
    default=root / "manuscript-round-01" / "frozen-manuscript-v8",
)
parser.add_argument(
    "--output",
    type=Path,
    default=Path(__file__).with_name("assembled-v8-check-results.json"),
)
args = parser.parse_args()
mp.mp.dps = 90
data = json.loads((args.snapshot / "figures/global-error-data.json").read_text())
manifest = json.loads((args.snapshot / "MANIFEST.json").read_text())
entry_checks = [
    {
        "path": row["path"],
        "expected": row["sha256"],
        "actual": hashlib.sha256((args.snapshot / row["path"]).read_bytes()).hexdigest(),
    }
    for row in manifest
]
assert all(row["expected"] == row["actual"] for row in entry_checks)

orders = {}
for row in data["critical_profile_samples"]:
    orders.setdefault(row["N"], set()).add(row["k"])

all_q = {}
for n, requested in orders.items():
    values = [1, 0]
    for k in range(2, max(requested) + 1):
        values.append(
            2 * (k - 1) * values[-1]
            + (k - 1) * (n - k + 2) * values[-2]
        )
    all_q[n] = values

checks = []
for row in data["critical_profile_samples"]:
    n, k = row["N"], row["k"]
    epsilon = k % 2
    base = k - epsilon
    m = base // 2
    leading = mp.mpf(math.factorial(k) * n**m) / (2**m * math.factorial(m))
    if epsilon:
        leading *= mp.mpf(4 * m) / 3
    x = mp.sqrt(mp.mpf(base) / n)
    lam = mp.mpf(2) * base * x / 3
    hyperbolic = mp.sinh(lam) / lam if epsilon else mp.cosh(lam)
    q = x + (x * x - 1) * mp.log1p(x) - x * x / 2 - 2 * x**3 / 3
    ratio = mp.mpf(all_q[n][k]) / leading
    scaled = mp.root(n, 3) * mp.expm1(
        mp.log(ratio)
        - mp.log(hyperbolic)
        - n * q
        - (epsilon - mp.mpf("0.5")) * mp.log1p(x)
    )
    actual_scale = mp.mpf(k) / mp.root(n, 3)
    discrepancy = abs(scaled - mp.mpf(row["scaled_error"]))
    scale_discrepancy = abs(actual_scale - mp.mpf(row["scale"]))
    assert discrepancy < mp.mpf("1e-13"), (n, k, scaled, row)
    assert scale_discrepancy < mp.mpf("1e-13")
    checks.append(
        {
            "N": n,
            "k": k,
            "scaled_error_recomputed": mp.nstr(scaled, 50),
            "absolute_discrepancy": mp.nstr(discrepancy, 8),
            "scale_discrepancy": mp.nstr(scale_discrepancy, 8),
        }
    )


def signed_derivative_factor(z):
    y = mp.expm1(z)
    return (
        -mp.mpf(2) / 3 * (1 - z / y)
        + z * (-1 / y + z * mp.exp(z) / y**2)
    )


left = mp.mpf(1)
right = mp.mpf(2)
assert signed_derivative_factor(left) > 0
assert signed_derivative_factor(right) < 0
for _ in range(280):
    midpoint = (left + right) / 2
    if signed_derivative_factor(midpoint) > 0:
        left = midpoint
    else:
        right = midpoint
z_star = (left + right) / 2
c_star = (3 * z_star / 4) ** (mp.mpf(2) / 3)
constant = 3 / (4 * c_star) * (1 - z_star / mp.expm1(z_star))
assert abs(c_star - mp.mpf(data["maximizing_scale_numeric"])) < mp.mpf("1e-28")
assert abs(constant - mp.mpf(data["maximum_absolute_profile_numeric"])) < mp.mpf("1e-28")

result = {
    "status": "all checks passed",
    "precision_digits": mp.mp.dps,
    "method": "Exact integer Q recurrence followed by direct polynomial normalization. The permutation denominator cancels before numerical evaluation.",
    "point_count": len(checks),
    "max_absolute_discrepancy": max(float(row["absolute_discrepancy"]) for row in checks),
    "points": checks,
    "maximizer_method": "Bisection of the derivative of the odd absolute profile",
    "z_star": mp.nstr(z_star, 70),
    "c_star": mp.nstr(c_star, 70),
    "C_star": mp.nstr(constant, 70),
    "manifest_checks": entry_checks,
    "scope": "Finite numerical verification, not a proof of uniform limits or a formal interval certificate",
}
args.output.write_text(json.dumps(result, indent=2) + "\n")
print(
    json.dumps(
        {key: value for key, value in result.items() if key not in ["points", "manifest_checks"]},
        indent=2,
    )
)
