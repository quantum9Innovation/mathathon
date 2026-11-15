from collections import defaultdict
from fractions import Fraction
from itertools import permutations
import json
from pathlib import Path


def inverse(sigma):
    return {value: index + 1 for index, value in enumerate(sigma)}


def inspect(cells, event):
    n = 4
    tested = 0
    atoms = defaultdict(list)
    all_permutations = list(permutations(range(1, n + 1)))
    for sigma in all_permutations:
        sigma_inverse = inverse(sigma)
        key = tuple(
            (sigma[row - 1], sigma_inverse[column])
            for index, (row, column) in enumerate(cells)
            if index != tested
        )
        atoms[key].append(sigma)

    records = []
    selected = 0
    tested_row, tested_column = cells[tested]
    for key, atom in sorted(atoms.items()):
        selected_flags = [event(sigma, inverse(sigma)) for sigma in atom]
        assert len(set(selected_flags)) == 1
        if not selected_flags[0]:
            continue
        selected += len(atom)
        omega = any(
            image == tested_column or preimage == tested_row
            for image, preimage in key
        )
        n_t = n - len({image for image, _ in key})
        actual = Fraction(
            sum(sigma[tested_row - 1] == tested_column for sigma in atom),
            len(atom),
        )
        claimed = Fraction(int(not omega), n_t)
        bound = Fraction(1, n - len(cells) + 1)
        assert actual != claimed
        assert actual > bound
        records.append(
            {
                "conditioning_atom": key,
                "permutation_count": len(atom),
                "actual_conditional_probability": str(actual),
                "omega": omega,
                "source_n_t": n_t,
                "claimed_conditional_probability": str(claimed),
                "claimed_upper_bound": str(bound),
                "permutations": atom,
            }
        )
    return {
        "n": n,
        "a": len(cells),
        "k": 2,
        "k_0_for_raw_tested_cell_realization": 1,
        "cells": cells,
        "tested_cell": cells[tested],
        "event_probability": str(Fraction(selected, len(all_permutations))),
        "selected_permutation_count": selected,
        "total_permutation_count": len(all_permutations),
        "conditioning_atoms": records,
    }


result = {
    "shared_row": inspect(
        [(1, 1), (1, 2)],
        lambda sigma, sigma_inverse: sigma[0] == 1,
    ),
    "two_exposed_arrows": inspect(
        [(1, 1), (2, 2)],
        lambda sigma, sigma_inverse: sigma[1] == 3 and sigma_inverse[2] == 4,
    ),
}
assert result["shared_row"]["event_probability"] == "1/4"
assert result["two_exposed_arrows"]["event_probability"] == "1/12"
assert len(result["shared_row"]["conditioning_atoms"]) == 3
assert len(result["two_exposed_arrows"]["conditioning_atoms"]) == 1
destination = Path(__file__).with_name("conditioning_enumeration.json")
destination.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({key: value["event_probability"] for key, value in result.items()}))
