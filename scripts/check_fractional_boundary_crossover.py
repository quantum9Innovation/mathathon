#!/usr/bin/env python3
"""Algebra diagnostics for the joint fractional-update boundary theorem.

The sharp asymptotic count is proved analytically. These finite tests check
the nuclear-tail inequality, complex projected nodes, and phase-area algebra.
They do not estimate an asymptotic rank constant from floating eigenvalues.
"""

import json

import numpy as np


SEED = 2026111507


def power(matrix, alpha):
    values, vectors = np.linalg.eigh(matrix)
    assert values[0] >= -1e-12
    return (vectors * np.maximum(values, 0.0) ** alpha) @ vectors.T


def main():
    rng = np.random.default_rng(SEED)
    nuclear_trials = 0
    node_trials = 0
    area_trials = 0
    max_tail_ratio = 0.0
    max_node_ratio = 0.0
    max_area_error = 0.0
    min_residual_eigenvalue = 0.0

    for n in (3, 5, 8):
        identity = np.eye(n)
        for trial in range(8):
            orthogonal, _ = np.linalg.qr(rng.normal(size=(n, n)))
            scale = 10.0 ** (-(trial % 4))
            values = scale * rng.uniform(0.03, 0.45, size=n)
            base = (orthogonal * values) @ orthogonal.T
            vector = rng.normal(size=n)
            vector /= np.linalg.norm(vector)
            updated = base + np.outer(vector, vector)
            h = np.linalg.eigvalsh(updated)[-1] - 1.0
            a = float(vector @ base @ vector)
            assert 0.0 < h < 1.0 and a <= h + 2e-14
            projection = identity - np.outer(vector, vector)

            for alpha in (0.3, 0.5, 0.7):
                difference = power(updated, alpha) - power(base, alpha)
                column = difference @ vector
                rank_one = np.outer(column, column) / float(vector @ column)
                residual = difference - rank_one
                residual_values = np.linalg.eigvalsh(residual)
                min_residual_eigenvalue = min(
                    min_residual_eigenvalue, float(residual_values[0])
                )
                assert residual_values[0] >= -2e-12
                trace_compression = float(np.trace(projection @ difference @ projection))
                moment = float(vector @ power(base, alpha) @ vector)
                eigenvalues = np.linalg.eigvalsh(difference)
                tail = float(eigenvalues[:-1].sum())
                assert tail <= trace_compression + 2e-12
                assert np.trace(residual) <= trace_compression + 2e-12
                assert trace_compression <= moment + 2e-12
                assert moment <= h**alpha + 2e-12
                max_tail_ratio = max(max_tail_ratio, tail / h**alpha)
                nuclear_trials += 1

            for p in (1, 2, 3):
                columns = [vector]
                for _ in range(1, p):
                    columns.append(base @ columns[-1])
                basis, _ = np.linalg.qr(np.column_stack(columns))
                projected = identity - basis @ basis.T
                for angle in (0.0, 0.6 * np.pi, 0.9 * np.pi):
                    cosine = np.cos(angle / 2.0)
                    c_first = 2.0 / cosine
                    c_middle = max(2.0 / cosine, 0.5 / cosine**3)
                    c_last = 2.0 ** (2 * p - 1) / cosine**3
                    for t in (1e-4, 0.03, 1.0, 30.0, 1e4):
                        z = t * np.exp(1j * angle)
                        resolvent = np.linalg.solve(base + z * identity, vector)
                        m_z = vector @ resolvent
                        m_t = float(vector @ np.linalg.solve(base + t * identity, vector))
                        assert abs(1.0 + m_z) + 2e-12 >= cosine * (1.0 + m_t)
                        v = projected @ resolvent
                        node = np.outer(v, v) / (1.0 + m_z)
                        actual = float(np.linalg.norm(node, 2))
                        bound = min(
                            c_first / t,
                            c_middle * h / t**2,
                            c_last * h / t ** (2 * p + 2),
                        )
                        assert actual <= bound * (1.0 + 1e-6) + 1e-25
                        max_node_ratio = max(max_node_ratio, actual / bound)
                        node_trials += 1

    for alpha in (0.3, 0.5, 0.7):
        beta = 1.0 - alpha
        for tau in (0.0, 0.5, 1.0, 1.5, 2.5):
            for v in (0.4, 1.0, 2.0):
                for p in (1, 2, 5):
                    left = -(v + 1.0) / alpha - tau - 1.0
                    right = (v + tau + 1.0) / beta + 1.0
                    grid = np.linspace(left, right, 100001)
                    envelope = np.maximum.reduce(
                        [-alpha * grid, tau + beta * grid, tau + (2 * p + beta) * grid]
                    )
                    numerical = float(np.trapezoid(np.maximum(v - envelope, 0.0), grid))
                    if v <= alpha * tau:
                        exact = 0.0
                    elif v <= tau:
                        exact = (v - alpha * tau) ** 2 / (2.0 * alpha * beta)
                    else:
                        exact = v**2 / (2.0 * alpha) - tau**2 / 2.0
                        exact += (v - tau) ** 2 / (2.0 * (2 * p + beta))
                    error = abs(numerical - exact)
                    max_area_error = max(max_area_error, error)
                    assert error <= 2e-6
                    area_trials += 1

    result = {
        "seed": SEED,
        "numpy_version": np.__version__,
        "nuclear_tail_trials": nuclear_trials,
        "complex_projected_node_trials": node_trials,
        "phase_area_trials": area_trials,
        "largest_nuclear_tail_over_h_alpha": max_tail_ratio,
        "minimum_schur_residual_eigenvalue": min_residual_eigenvalue,
        "largest_projected_node_over_explicit_bound": max_node_ratio,
        "largest_phase_area_quadrature_discrepancy": max_area_error,
        "assertions": "PASS",
        "scope": "finite algebra and area diagnostics, not proof of asymptotic counts",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
