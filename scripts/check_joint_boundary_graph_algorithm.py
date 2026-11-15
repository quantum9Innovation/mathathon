#!/usr/bin/env python3
"""Finite algebra checks for projected fractional graph corrections.

The ordinary log grid here is deliberately not the optimized Gaussian
rule. It tests rank-2p factor restoration and the terminal rank-one
error budget, including a nonsymmetric inexact auxiliary correction.
"""

import json

import numpy as np


SEED = 2026111512


def norm(matrix):
    return float(np.linalg.norm(matrix, 2))


def power(matrix, alpha):
    values, vectors = np.linalg.eigh(matrix)
    assert values[0] > 0
    return (vectors * values**alpha) @ vectors.T


def graph_case(rng, vertices, h):
    masses = 10.0 ** rng.uniform(-1, 1, vertices)
    edges = np.eye(vertices)[:, :-1] - np.eye(vertices)[:, 1:]
    conductances = rng.uniform(0.3, 1.4, vertices - 1)
    laplacian = (edges * conductances) @ edges.T
    inverse_mass = np.diag(masses**-0.5)
    full = inverse_mass @ laplacian @ inverse_mass
    kernel = np.sqrt(masses)
    kernel /= np.linalg.norm(kernel)
    basis, _ = np.linalg.qr(np.column_stack((kernel, np.eye(vertices))))
    basis = basis[:, 1:]
    base = basis.T @ full @ basis
    base *= 0.4 * h / norm(base)
    update = basis.T @ inverse_mass @ edges[:, vertices // 2 - 1]
    update /= np.linalg.norm(update)
    updated = base + np.outer(update, update)
    assert np.linalg.eigvalsh(updated)[-1] <= 1 + h + 2e-14
    return base, updated, update


def main():
    rng = np.random.default_rng(SEED)
    graph_pairs = 0
    restoration_cases = 0
    terminal_cases = 0
    largest_factor_error = 0.0
    largest_auxiliary_grid_error = 0.0
    largest_restoration_error_over_budget = 0.0
    largest_terminal_error_over_epsilon = 0.0

    # Removing the known common kernel is a finite diagnostic convenience.
    # The sparse algorithm uses shifted systems and needs no such basis.
    logs = np.linspace(-64, 64, 1601)
    step = logs[1] - logs[0]
    nodes = np.exp(logs)
    for vertices in (5, 8):
        for _ in range(2):
            for h in (1.0, 1e-2, 1e-4, 1e-6):
                base, updated, w = graph_case(rng, vertices, h)
                graph_pairs += 1
                size = len(w)
                identity = np.eye(size)
                left = np.column_stack([
                    np.linalg.solve(base + t * identity, w) for t in nodes
                ])
                right = np.column_stack([
                    np.linalg.solve(updated + t * identity, w) for t in nodes
                ])
                for alpha in (0.3, 0.5, 0.7):
                    exact = power(updated, alpha) - power(base, alpha)
                    weights = step * np.sin(np.pi * alpha) / np.pi
                    weights = weights * nodes ** (alpha + 1)
                    factor_left = left * np.sqrt(weights)
                    factor_right = right * np.sqrt(weights)
                    grid = factor_left @ factor_right.T
                    grid_error = norm(grid - exact)
                    largest_auxiliary_grid_error = max(
                        largest_auxiliary_grid_error, grid_error
                    )
                    assert grid_error < 2e-7

                    # Give the auxiliary correction an explicitly bounded,
                    # nonsymmetric error. No linear/symmetric solve map is
                    # assumed in the restoration identity.
                    noise = rng.normal(size=(size, size))
                    noise /= norm(noise)
                    noise_scale = 5e-6
                    aux_left = np.column_stack((factor_left, noise_scale * noise))
                    aux_right = np.column_stack((factor_right, identity))
                    auxiliary = aux_left @ aux_right.T
                    auxiliary_error = norm(auxiliary - exact)
                    assert auxiliary_error < 5.1e-6

                    for p in (1, 2, 4):
                        columns = [w]
                        for _ in range(1, min(p, size)):
                            columns.append(base @ columns[-1])
                        vectors, _ = np.linalg.qr(np.column_stack(columns))
                        projector = vectors @ vectors.T
                        complement = identity - projector
                        y = aux_left @ (aux_right.T @ vectors)
                        z = complement @ aux_right @ (aux_left.T @ vectors)
                        restore_left = np.column_stack((y, vectors))
                        restore_right = np.column_stack((vectors, z))
                        restored = restore_left @ restore_right.T
                        reference = (
                            auxiliary @ projector
                            + projector @ auxiliary @ complement
                        )
                        factor_error = norm(restored - reference)
                        largest_factor_error = max(largest_factor_error, factor_error)
                        assert factor_error < 2e-12
                        assert restore_left.shape[1] <= 2 * p

                        exact_restoration = exact - complement @ exact @ complement
                        restore_error = norm(restored - exact_restoration)
                        ratio = restore_error / (3 * auxiliary_error)
                        largest_restoration_error_over_budget = max(
                            largest_restoration_error_over_budget, ratio
                        )
                        assert ratio <= 1 + 1e-8

                        projected = (complement @ factor_left) @ (
                            complement @ factor_right
                        ).T
                        combined = projected + restored
                        projected_error = norm(complement @ (grid - exact) @ complement)
                        assert norm(combined - exact) <= (
                            projected_error + 3 * auxiliary_error + 2e-12
                        )
                        restoration_cases += 1

                    epsilon = max(1e-3, 4 * h**alpha)
                    if epsilon <= 0.5:
                        assert h**alpha <= epsilon / 2
                        assert auxiliary_error <= epsilon / 100
                        column = auxiliary @ w
                        denominator = float(w @ column)
                        assert denominator > 0
                        approximation = np.outer(column, column) / denominator
                        exact_column = exact @ w
                        schur = np.outer(exact_column, exact_column) / float(w @ exact_column)
                        assert norm(approximation - schur) <= 10 * auxiliary_error
                        error_ratio = norm(approximation - exact) / epsilon
                        largest_terminal_error_over_epsilon = max(
                            largest_terminal_error_over_epsilon, error_ratio
                        )
                        assert error_ratio < 1
                        terminal_cases += 1

    print(json.dumps({
        "seed": SEED,
        "numpy_version": np.__version__,
        "common_mass_graph_pairs": graph_pairs,
        "rank_two_p_restoration_cases": restoration_cases,
        "terminal_rank_one_cases": terminal_cases,
        "largest_restoration_factor_identity_error": largest_factor_error,
        "largest_auxiliary_uniform_grid_error": largest_auxiliary_grid_error,
        "largest_restoration_error_over_three_delta": largest_restoration_error_over_budget,
        "largest_terminal_error_over_epsilon": largest_terminal_error_over_epsilon,
        "assertions": "PASS",
        "scope": "finite factor/error checks, not proof of optimized Gaussian width or SDD runtime",
    }, indent=2))


if __name__ == "__main__":
    main()
