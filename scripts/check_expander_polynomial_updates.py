#!/usr/bin/env python3
"""Check the factor identity and tail bound in expander-polynomial-updates.txt.

These small dense floating calculations check algebra and the error bound;
they do not implement a sparse performance experiment or prove the theorem.
Requires NumPy.  The input graph pairs include additions and deletions.
"""

import json

import numpy as np


SEED = 20261115


def psd_square_root(matrix):
    """Use a diagnostic eigendecomposition, retaining the known zero mode."""
    values, vectors = np.linalg.eigh(matrix)
    assert values[0] >= -1e-10
    assert abs(values[0]) < 1e-10
    values[0] = 0.0
    return (vectors * np.sqrt(np.maximum(0.0, values))) @ vectors.T


def main():
    rng = np.random.default_rng(SEED)
    max_identity_error = 0.0
    max_tail_ratio = 0.0
    checked_cases = 0
    graph_pairs = 0
    additions = 0
    deletions = 0

    for n in range(4, 13):
        for trial in range(5):
            weights = rng.uniform(0.2, 1.0, (n, n))
            weights = np.triu(weights, 1)
            weights += weights.T
            base = np.diag(weights.sum(axis=1)) - weights
            update_columns = np.zeros((n, 3))
            update_weights = np.zeros_like(weights)
            signs = []
            for column in range(3):
                i, j = rng.choice(n, 2, replace=False)
                weight = rng.uniform(0.01, 0.15)
                sign = 1 if trial % 2 else -1
                update_columns[i, column] = np.sqrt(weight)
                update_columns[j, column] = -np.sqrt(weight)
                update_weights[i, j] += sign * weight
                update_weights[j, i] += sign * weight
                signs.append(sign)
            signature = np.diag(signs)
            perturbation = update_columns @ signature @ update_columns.T
            changed = base + perturbation
            final_weights = weights + update_weights
            # Duplicate random edges are possible.  Verify that both actual
            # endpoint matrices still are admissible graph Laplacians.
            assert np.min(final_weights) >= -1e-12
            assert np.linalg.norm(changed.sum(axis=1), np.inf) < 1e-10
            changed_from_weights = (
                np.diag(final_weights.sum(axis=1)) - final_weights
            )
            assert np.linalg.norm(changed_from_weights - changed, 2) < 1e-10

            base_spectrum = np.linalg.eigvalsh(base)
            changed_spectrum = np.linalg.eigvalsh(changed)
            gamma = 0.9 * min(base_spectrum[1], changed_spectrum[1])
            upper = 1.1 * max(base_spectrum[-1], changed_spectrum[-1])
            assert 0 < gamma < upper
            center = (upper + gamma) / 2
            radius = (upper - gamma) / (upper + gamma)
            x_action = base / center - np.eye(n)
            y_action = changed / center - np.eye(n)
            target = psd_square_root(changed) - psd_square_root(base)
            graph_pairs += 1
            additions += trial % 2 == 1
            deletions += trial % 2 == 0

            for degree in [1, 2, 4, 8, 16]:
                coefficients = [1.0]
                for j in range(degree):
                    coefficients.append(coefficients[-1] * (0.5 - j) / (j + 1))

                left_blocks = []
                block = update_columns.copy()
                for _ in range(degree):
                    left_blocks.append(block)
                    block = x_action @ block
                right_blocks = [None] * degree
                block = np.zeros_like(update_columns)
                for j in reversed(range(degree)):
                    block = coefficients[j + 1] * update_columns + y_action @ block
                    right_blocks[j] = block
                factored = center ** (-0.5) * sum(
                    left_blocks[j] @ signature @ right_blocks[j].T
                    for j in range(degree)
                )

                expanded = np.zeros_like(base)
                x_power = np.eye(n)
                y_power = np.eye(n)
                for j in range(1, degree + 1):
                    x_power = x_power @ x_action
                    y_power = y_power @ y_action
                    expanded += (
                        center**0.5 * coefficients[j] * (y_power - x_power)
                    )
                scale = max(1.0, np.linalg.norm(expanded, 2))
                identity_error = np.linalg.norm(factored - expanded, 2) / scale
                error = np.linalg.norm(target - factored, 2)
                proved_bound = (
                    0.5
                    * center ** (-0.5)
                    * np.linalg.norm(perturbation, 2)
                    * radius**degree
                    / (1 - radius)
                )
                tail_ratio = error / proved_bound
                # These tolerances accommodate small dense floating arithmetic;
                # the exact claims are the written identities and estimates.
                assert identity_error < 1e-12, (n, trial, degree, identity_error)
                assert tail_ratio <= 1.0001, (n, trial, degree, tail_ratio)
                max_identity_error = max(max_identity_error, identity_error)
                max_tail_ratio = max(max_tail_ratio, tail_ratio)
                checked_cases += 1

    assert checked_cases == 225
    print(
        json.dumps(
            {
                "diagnostic": "expander polynomial update factor identity and tail",
                "seed": SEED,
                "numpy_version": np.__version__,
                "dimension_range": [4, 12],
                "degrees": [1, 2, 4, 8, 16],
                "graph_pairs": graph_pairs,
                "addition_only_pairs": additions,
                "deletion_only_pairs": deletions,
                "update_columns_per_pair": 3,
                "checked_cases": checked_cases,
                "max_factor_identity_scaled_operator_error": float(max_identity_error),
                "max_actual_tail_over_proved_bound": float(max_tail_ratio),
                "assertions": "PASS",
                "scope": "Dense algebra diagnostic; no sparse runtime claim or theorem proof.",
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
