"""Exact rational checks of the normalized-cut/kernel-cost shift obstruction."""
from fractions import Fraction
import json


def run():
    rows = []
    for n in (6, 10, 20, 100, 1000, 10000):
        good_nc = Fraction(2, n)
        bad_nc = Fraction(1)
        c = 2 * n - 6
        good_j = 2 * good_nc + c
        bad_j = 2 * bad_nc + c
        j_ratio = bad_j / good_j
        nc_ratio = bad_nc / good_nc
        assert j_ratio == Fraction(n, n - 1)
        assert nc_ratio == Fraction(n, 2)
        # Explicit trace identity: the good partition retains within-part
        # adjacency trace 2-4/n; the parity partition retains zero.
        good_trace = 2 - Fraction(4, n)
        assert good_j == 2 * n - good_trace - 4
        assert bad_j == 2 * n - 4
        rows.append({"n": n, "good_nc": str(good_nc),
                     "bad_nc": str(bad_nc), "kernel_cost_ratio": str(j_ratio),
                     "nc_ratio": str(nc_ratio)})
    print(json.dumps({"status": "PASS", "exact_arithmetic": True,
                      "cycle_examples": rows}, indent=2))


if __name__ == "__main__":
    run()
