#!/usr/bin/env python3
"""Finite checks for near-real-deflated-raw-solves.txt.

This retains the actual 48-case experiment reported in that note, using
seed 2026111509. It checks the safe-block bounds, Neumann approximation,
Schur reconstruction and normalized physical resolvent identity. These
are finite dense algebra checks, not a proof of a fast split algorithm,
the asymptotic cost, a finite-precision theorem, or the original LRA gate.
"""

import json

import numpy as np


def main():
    seed = 2026111509
    rng = np.random.default_rng(seed)
    eta = 1 / 8
    beta = 2 / (1 - 2 * eta)
    max_safe = 0.0
    max_contraction = 0.0
    max_neumann = 0.0
    max_schur = 0.0
    max_normalized_error = 0.0
    max_woodbury_relative_error = 0.0
    cases = 0

    for m in (8, 16, 32):
        for _ in range(4):
            vals = np.r_[
                rng.uniform(0.65, 1.6, m // 4),
                -(10 ** rng.uniform(-3, 3, m // 4)),
                10 ** rng.uniform(-3, -0.4, m // 4),
                10 ** rng.uniform(0.4, 3, m - 3 * (m // 4)),
            ]
            raw = rng.standard_normal((m, m))
            defect = (raw + raw.T) / 2
            defect *= eta / np.linalg.norm(defect, 2)
            metric = np.eye(m) + defect
            orthogonal, _ = np.linalg.qr(rng.standard_normal((m + 3, m)))
            factor = orthogonal @ np.linalg.cholesky(metric).T
            physical = (factor * vals) @ factor.T

            p = np.flatnonzero((vals >= 0.5) & (vals <= 2))
            q = np.flatnonzero((vals < 0.5) | (vals > 2))
            tpq = metric[np.ix_(p, q)]
            tqp = tpq.T
            tpp = metric[np.ix_(p, p)]
            tqq = metric[np.ix_(q, q)]

            for y in (1.0, 0.1, 0.01, 0.001):
                pole = 1 + 1j * y
                mu = abs(pole) / y
                safe = pole * np.diag(1 / vals[q]) - tqq
                coarse_inverse = np.diag(vals[q] / (pole - vals[q]))
                iteration = coarse_inverse @ (tqq - np.eye(len(q)))
                safe_norm = np.linalg.norm(coarse_inverse, 2)
                contraction = np.linalg.norm(iteration, 2)
                max_safe = max(max_safe, safe_norm)
                max_contraction = max(max_contraction, contraction)
                assert safe_norm <= 2 + 1e-12
                assert contraction <= 2 * eta + 1e-12

                epsilon = 1e-3
                target = epsilon / (10 * mu * mu)
                degree = int(np.ceil(np.log(target / beta) / np.log(2 * eta)))
                approximate_inverse = np.zeros_like(safe)
                term = coarse_inverse.copy()
                for _ in range(degree):
                    approximate_inverse += term
                    term = iteration @ term
                exact_inverse = np.linalg.inv(safe)
                delta = beta * (2 * eta) ** degree
                neumann_error = np.linalg.norm(approximate_inverse - exact_inverse, 2)
                max_neumann = max(max_neumann, neumann_error / max(delta, 1e-13))
                assert neumann_error <= delta + 1e-12

                schur = pole * np.diag(1 / vals[p]) - tpp - tpq @ exact_inverse @ tqp
                approximate_schur = (
                    pole * np.diag(1 / vals[p])
                    - tpp
                    - tpq @ approximate_inverse @ tqp
                )
                inverse_bound = 2 * mu / (1 - eta)
                schur_inverse_norm = np.linalg.norm(np.linalg.inv(schur), 2)
                max_schur = max(max_schur, schur_inverse_norm / inverse_bound)
                assert schur_inverse_norm <= inverse_bound * (1 + 1e-12)

                pencil = pole * np.diag(1 / vals) - metric
                reconstructed_inverse = np.zeros((m, m), complex)
                for j in range(m):
                    rhs = np.eye(m)[:, j]
                    safe_rhs = approximate_inverse @ rhs[q]
                    up = np.linalg.solve(approximate_schur, rhs[p] + tpq @ safe_rhs)
                    uq = safe_rhs + approximate_inverse @ tqp @ up
                    result = np.zeros(m, complex)
                    result[p] = up
                    result[q] = uq
                    reconstructed_inverse[:, j] = result

                exact_pencil_inverse = np.linalg.inv(pencil)
                action_error = factor @ (reconstructed_inverse - exact_pencil_inverse) @ factor.T
                normalized_error = np.linalg.norm(action_error, 2)
                max_normalized_error = max(max_normalized_error, normalized_error / epsilon)
                assert normalized_error <= epsilon

                physical_identity = np.eye(m + 3)
                direct_normalized = pole * np.linalg.inv(physical - pole * physical_identity)
                woodbury_normalized = -physical_identity - factor @ exact_pencil_inverse @ factor.T
                woodbury_relative_error = np.linalg.norm(
                    direct_normalized - woodbury_normalized, 2
                ) / (1 + np.linalg.norm(direct_normalized, 2))
                max_woodbury_relative_error = max(
                    max_woodbury_relative_error, woodbury_relative_error
                )
                assert woodbury_relative_error <= 1e-9
                cases += 1

    print(
        json.dumps(
            {
                "seed": seed,
                "numpy_version": np.__version__,
                "cases": cases,
                "max_safe_multiplier": max_safe,
                "max_actual_contraction": max_contraction,
                "max_R_error_over_bound_or_roundoff_floor": max_neumann,
                "max_schur_inverse_over_bound": max_schur,
                "max_normalized_physical_error_over_epsilon": max_normalized_error,
                "max_woodbury_relative_identity_error": max_woodbury_relative_error,
                "assertions": "PASS",
                "scope": (
                    "finite dense algebra diagnostics, not an exact split algorithm, "
                    "a runtime or stability theorem, or the original arbitrary-factor LRA gate"
                ),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
