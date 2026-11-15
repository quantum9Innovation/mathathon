"""Exact finite corroboration of marked-pair counting, not an asymptotic proof."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json
import math

ROOT = Path(__file__).resolve().parent


def marked_pair_check(a, b):
    # N=2. For each known left fiber, a graph specifies which b of the
    # 2b right vertices connect to its first left vertex.
    size = 2*b
    choices = []
    for subset in combinations(range(size), b):
        mask = sum(1 << j for j in subset)
        choices.append(mask)
    histogram = Counter()
    for maps in product(choices, repeat=a):
        types = Counter(sum(((maps[i] >> v) & 1) << i for i in range(a))
                        for v in range(size))
        w = 1
        for t in range(1 << (a-1)):
            complement = t ^ ((1 << a)-1)
            if types[t] != types[complement]:
                w = 0
                break
            w *= math.factorial(types[t])
        histogram[w] += 1
    total_graphs = math.comb(2*b, b)**a
    total_marked = math.factorial(2*b)*2**((a-1)*b)
    ordered_compatible = math.factorial(b)*sum(w*count for w, count in histogram.items())
    support = total_graphs-histogram[0]
    assert sum(histogram.values()) == total_graphs
    assert ordered_compatible == total_marked
    success = Fraction(math.factorial(b)*support, total_marked)
    bound = Fraction(math.factorial(b)*total_graphs, total_marked)
    assert success <= bound
    return {"a": a, "b": b, "N": 2, "observations_U": total_graphs,
            "marked_pairs_T": total_marked, "support_size": support,
            "W_histogram_over_all_observations": dict(sorted(histogram.items())),
            "optimal_success_exact": str(success), "counting_bound_exact": str(bound)}


thresholds = {}
for a in (3, 4, 5, 6):
    first = next(b for b in range(a, 10000)
                 if math.factorial(b)**a > b**((a-1)*b))
    thresholds[a] = first
assert thresholds == {3: 12, 4: 42, 5: 131, 6: 380}
ratio = Fraction(math.factorial(12)**3, 12**24)
assert ratio == Fraction(7133328125, 5159780352) > 1
gamma = math.log(float(ratio))
log_bounds = {}
for n in (1, 2, 10, 100, 1000):
    a, b = 3, 12
    numerator = math.factorial(b)*math.factorial(b*n)**(a-1)
    denominator = math.factorial(b)**(a*n)*math.factorial(n)**((a-1)*b)
    bound = Fraction(numerator, denominator)
    assert bound <= 1
    log_bounds[n] = math.log(bound.numerator)-math.log(bound.denominator)

report = {"status": "PASS", "scope": "exact finite count checks only",
          "first_positive_b": thresholds, "exp_gamma_3_12_exact": str(ratio),
          "gamma_3_12": gamma, "log_recovery_bounds_K3_12": log_bounds,
          "enumerated_marked_pair_cases": [marked_pair_check(3, 3), marked_pair_check(3, 4)]}
(ROOT / "fiber-count-checks.json").write_text(json.dumps(report, indent=2)+"\n")
print("PASS: two exhaustive N=2 marked-pair counts; exact factorial thresholds and K3,12 bound")
