from pathlib import Path
import json

import sympy as sp


n, s = sp.symbols("n s")
polynomials = [sp.Integer(1), s]
for h in range(1, 12):
    polynomials.append(sp.expand((s + 2 * h) * polynomials[h] + h * (n - s - h + 1) * polynomials[h - 1]))

records = []
for h in range(13):
    order = n - s - h + 1
    derangement = sp.expand(sum(
        sp.binomial(h, j) * (-n) ** j * sp.rf(order, h - j)
        for j in range(h + 1)
    ))
    difference = sp.expand(polynomials[h] - (-1) ** h * derangement)
    assert difference == 0
    records.append({
        "h": h,
        "difference": str(difference),
        "polynomial": str(polynomials[h]),
    })

result = {
    "identity": "P_h(n,s) = (-1)^h d_h^(n-s-h+1)(-n)",
    "source_definition": "(1-t)^(-r) exp(x t) = sum_j d_j^(r)(x) t^j/j!",
    "method": "Compare the recurrence derived from the depleted generating function with the finite coefficient sum from the published higher-order derangement definition",
    "symbolic_variables": ["n", "s"],
    "orders_checked": list(range(13)),
    "all_differences_zero": True,
    "sympy_version": sp.__version__,
    "records": records,
    "scope": "These finite symbolic checks corroborate the separate general coefficient proof",
}
destination = Path(__file__).with_name("DERANGEMENT_CHECKS-v1.json")
destination.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"checked_orders": len(records), "all_differences_zero": True}))
