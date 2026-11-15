"""Exact checks of two intermediate assertions in the 2004 Friedman source."""

from fractions import Fraction
from hashlib import sha256
import json
from math import factorial
from pathlib import Path


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / "snapshot/reading-sources/alon-second-eigenvalue/source/all.tex"


def falling(n, k):
    return factorial(n) // factorial(n - k)


def common_fixed_point_probability(n, colors=2):
    return sum(
        ((-1) ** (k + 1) * Fraction(falling(n, k), factorial(k) * falling(n, k) ** colors)
         for k in range(1, n + 1)),
        Fraction(0),
    )


def exact_pair_enumeration_n4():
    from itertools import permutations

    ps = list(permutations(range(4)))
    occupied = sum(
        any(p[i] == i and q[i] == i for i in range(4))
        for p in ps for q in ps
    )
    return Fraction(occupied, len(ps) ** 2)


def main():
    source_bytes = SOURCE.read_bytes()
    glossary = SOURCE.with_name("all.ind")
    glossary_bytes = glossary.read_bytes()
    coverage = {
        "source": str(SOURCE),
        "source_sha256": sha256(source_bytes).hexdigest(),
        "source_lines": len(source_bytes.splitlines()),
        "source_bytes": len(source_bytes),
        "newly_read_inclusive_intervals": [
            [1, 800], [801, 1600], [1601, 2400], [2401, 3200],
            [3201, 4000], [4001, 4800], [4801, 5600],
            [5601, 6400], [6401, 7220],
        ],
        "all_main_source_lines_read": True,
        "glossary": str(glossary),
        "glossary_sha256": sha256(glossary_bytes).hexdigest(),
        "glossary_lines": len(glossary_bytes.splitlines()),
        "newly_read_glossary_inclusive_intervals": [[1, 116]],
        "eps_images_independently_viewed": False,
        "publisher_pdf_fully_read": False,
        "external_bibliography_papers_counted_as_read": False,
        "full_read_is_formal_verification": False,
    }
    (HERE / "coverage.json").write_text(json.dumps(coverage, indent=2) + "\n")
    rows = []
    for n in range(2, 15):
        actual = common_fixed_point_probability(n)
        claimed_event_bound = Fraction(1, n) - Fraction(1, 2 * n * n)
        exact_bonferroni = Fraction(1, n) - Fraction(1, 2 * n * (n - 1))
        assert actual >= exact_bonferroni
        rows.append({
            "n": n,
            "exact_common_fixed_point_probability": str(actual),
            "printed_simplified_event_bound": str(claimed_event_bound),
            "printed_bound_exceeds_actual": claimed_event_bound > actual,
            "correct_Bonferroni_lower_bound": str(exact_bonferroni),
        })

    assert exact_pair_enumeration_n4() == common_fixed_point_probability(4)
    assert common_fixed_point_probability(4) == Fraction(41, 192)
    assert Fraction(1, 4) - Fraction(1, 32) == Fraction(42, 192)

    output = {
        "source_sha256": sha256(SOURCE.read_bytes()).hexdigest(),
        "method": "Exact rational inclusion-exclusion, plus exhaustive enumeration of 24 squared permutation pairs at n=4",
        "common_fixed_point_results": rows,
        "Moebius_remainder_counterexample": {
            "model": "G_n,4 with both permutations the identity",
            "Psi": "One vertex with two distinctly labelled whole-loops",
            "cutoff_r": 2,
            "N_Psi_G": "n",
            "mu_Psi": 1,
            "indicator": 1,
            "h_G": "1-n",
            "absolute_value_uniformly_bounded": False,
        },
        "limits": "These checks concern source proof steps. They do not refute the main spectral theorem.",
    }
    destination = HERE / "source-step-checks.json"
    destination.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"output": str(destination), "n4_probability": "41/192", "permutation_pairs_enumerated": 576}))


if __name__ == "__main__":
    main()
