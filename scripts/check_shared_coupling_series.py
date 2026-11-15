#!/usr/bin/env python3
"""Dense algebra checks for near-real-shared-coupling-series.txt.

This checks formal-series Richardson coefficients, affine complex
couplings, shared Schur coefficients, shared Q reconstruction, and near
and far normalized physical actions. It does not implement the fast
Frobenius/companion backend or certify an asymptotic runtime or split.
"""

import json

import numpy as np


def norm(a):
    return float(np.linalg.norm(a, 2))


def adjoint(a):
    return a.conj().T


def horner(coefficients, u):
    result = np.zeros_like(coefficients[0])
    for coefficient in coefficients[::-1]:
        result = coefficient + u * result
    return result


def unitary(rng, size):
    raw = rng.standard_normal((size, size))
    raw = raw + 1j * rng.standard_normal((size, size))
    return np.linalg.qr(raw)[0]


def main():
    seed = 2026111511
    rng = np.random.default_rng(seed)
    eta = 1 / 8
    zeta = 1 / 4
    epsilon = 1e-3
    near_heights = np.array([-0.25, -0.1, -0.01, -0.001, 0.001, 0.01, 0.1, 0.25])
    far_heights = np.array([-1.0, 0.5, 1.0])
    mu = float(np.max(np.sqrt(1 + near_heights**2) / np.abs(near_heights)))
    delta = epsilon / (100 * mu**2)
    degree = 1
    while (3 / 4) ** degree > delta / 100:
        degree += 1
    iterations = 1
    while (3 / 5) ** iterations > delta / 100:
        iterations += 1

    maxima = {
        "outer_coarse_inverse": 0.0,
        "outer_contraction": 0.0,
        "coupling_error_over_zeta_delta": 0.0,
        "rhs_error_over_delta_norm_b": 0.0,
        "shared_schur_identity_error": 0.0,
        "shared_reconstruction_identity_error": 0.0,
        "supported_error_over_9mu2_delta_norm_b": 0.0,
        "near_physical_error_over_epsilon_norm_h": 0.0,
        "far_physical_error_over_epsilon_norm_h": 0.0,
        "physical_identity_relative_error": 0.0,
        "analytic_coupling_vs_pointwise_adjoint_difference": 0.0,
    }
    metrics = 0
    near_cases = 0
    far_cases = 0
    boundary_cases = 0

    for m in (12, 20, 28):
        for _ in range(2):
            k = m // 4
            n = m - k
            bqq_values = np.r_[
                -(10 ** rng.uniform(-2, 2, n // 3)),
                rng.uniform(0.05, 0.4, n // 3),
                rng.uniform(2.5, 6, n - 2 * (n // 3)),
            ]
            off = rng.standard_normal((k, n))
            off *= 1e-4 / norm(off)
            coarse_real = np.block(
                [[np.diag(rng.uniform(0.8, 1.2, k)), off],
                 [off.T, np.diag(bqq_values)]]
            )
            random_defect = rng.standard_normal((m, m))
            defect_real = (random_defect + random_defect.T) / 2
            defect_real *= eta / norm(defect_real)
            metric_real = np.eye(m) + defect_real
            physical_basis, _ = np.linalg.qr(rng.standard_normal((m + 4, m)))
            factor_real = physical_basis @ np.linalg.cholesky(metric_real).T

            coordinate_change = np.zeros((m, m), complex)
            coordinate_change[:k, :k] = unitary(rng, k)
            coordinate_change[k:, k:] = unitary(rng, n)
            coarse = adjoint(coordinate_change) @ coarse_real @ coordinate_change
            metric = adjoint(coordinate_change) @ metric_real @ coordinate_change
            factor = factor_real @ coordinate_change
            defect = metric - np.eye(m)
            core = np.linalg.inv(coarse)
            physical = factor @ core @ adjoint(factor)
            assert norm(adjoint(factor) @ factor - metric) < 1e-12
            assert norm(defect) <= eta + 1e-12

            bpp = coarse[:k, :k]
            bpq = coarse[:k, k:]
            bqp = coarse[k:, :k]
            bqq = coarse[k:, k:]
            tpp = metric[:k, :k]
            tpq = metric[:k, k:]
            tqp = metric[k:, :k]
            tqq = metric[k:, k:]
            dqq = tqq - np.eye(n)
            gamma0, gamma1 = tpq - bpq, -bpq
            lambda0, lambda1 = tqp - bqp, -bqp
            assert norm(bpq) <= 1 / 16
            assert norm(gamma0) + norm(gamma1) / 3 <= zeta
            assert norm(lambda0) + norm(lambda1) / 3 <= zeta

            for angle in np.linspace(0, 2 * np.pi, 16, endpoint=False):
                u = np.exp(1j * angle) / 3
                a0 = np.linalg.inv((1 + u) * bqq - np.eye(n))
                maxima["outer_coarse_inverse"] = max(maxima["outer_coarse_inverse"], norm(a0))
                maxima["outer_contraction"] = max(maxima["outer_contraction"], norm(a0 @ dqq))
                assert norm(a0) <= 3 + 1e-12
                assert norm(a0 @ dqq) <= 3 / 8 + 1e-12
                boundary_cases += 1

            a00 = np.linalg.inv(bqq - np.eye(n))
            t0 = np.eye(n) + a00
            coefficients = np.zeros((degree, n, k), complex)
            # Dense coefficient recurrence is used only as an algebra check.
            # The proof uses a Frobenius companion series block implementation.
            for _iteration in range(iterations):
                rhs_coefficients = dqq @ coefficients
                rhs_coefficients[0] += lambda0
                rhs_coefficients[1] += lambda1
                transformed_rhs = a00 @ rhs_coefficients
                updated = np.empty_like(coefficients)
                updated[0] = transformed_rhs[0]
                for a in range(1, degree):
                    updated[a] = transformed_rhs[a] - t0 @ updated[a - 1]
                coefficients = updated

            schur_coefficients = np.zeros((degree + 1, k, k), complex)
            for a in range(degree):
                schur_coefficients[a] += gamma0 @ coefficients[a]
                schur_coefficients[a + 1] += gamma1 @ coefficients[a]

            near_u = 1j * near_heights
            h_block = rng.standard_normal((m + 4, len(near_u)))
            b_block = adjoint(factor) @ h_block
            p_block = np.empty((k, len(near_u)), complex)
            safe_block = np.empty((n, len(near_u)), complex)
            pointwise_u = []
            for j, u in enumerate(near_u):
                gamma = gamma0 + u * gamma1
                coupling = lambda0 + u * lambda1
                maxima["analytic_coupling_vs_pointwise_adjoint_difference"] = max(
                    maxima["analytic_coupling_vs_pointwise_adjoint_difference"],
                    norm(coupling - adjoint(gamma)),
                )
                safe = (1 + u) * bqq - tqq
                inverse = np.linalg.inv(safe)
                approximate_coupling = horner(coefficients, u)
                coupling_error = norm(approximate_coupling - inverse @ coupling)
                maxima["coupling_error_over_zeta_delta"] = max(
                    maxima["coupling_error_over_zeta_delta"], coupling_error / (zeta * delta)
                )
                assert coupling_error <= zeta * delta + 1e-14
                shared_schur = horner(schur_coefficients, u)
                schur_identity_error = norm(shared_schur - gamma @ approximate_coupling)
                maxima["shared_schur_identity_error"] = max(
                    maxima["shared_schur_identity_error"], schur_identity_error
                )
                assert schur_identity_error < 1e-11
                coarse_inverse = np.linalg.inv((1 + u) * bqq - np.eye(n))
                b = b_block[:, j]
                rhat = np.zeros(n, complex)
                for _iteration in range(iterations):
                    rhat = coarse_inverse @ (b[k:] + dqq @ rhat)
                rhs_error = norm((rhat - inverse @ b[k:])[:, None])
                maxima["rhs_error_over_delta_norm_b"] = max(
                    maxima["rhs_error_over_delta_norm_b"], rhs_error / (delta * norm(b[:, None]))
                )
                assert rhs_error <= delta * norm(b[:, None]) + 1e-13
                schur = (1 + u) * bpp - tpp - shared_schur
                p_block[:, j] = np.linalg.solve(schur, b[:k] + gamma @ rhat)
                safe_block[:, j] = rhat
                pointwise_u.append(approximate_coupling)

            reconstructed = safe_block.copy()
            powers = np.ones(len(near_u), complex)
            for coefficient in coefficients:
                reconstructed += coefficient @ (p_block * powers)
                powers *= near_u

            for j, u in enumerate(near_u):
                separate = safe_block[:, j] + pointwise_u[j] @ p_block[:, j]
                identity_error = norm((reconstructed[:, j] - separate)[:, None])
                maxima["shared_reconstruction_identity_error"] = max(
                    maxima["shared_reconstruction_identity_error"], identity_error
                )
                assert identity_error < 1e-10
                vhat = np.r_[p_block[:, j], reconstructed[:, j]]
                b = b_block[:, j]
                exact = np.linalg.solve((1 + u) * coarse - metric, b)
                supported_error = norm((vhat - exact)[:, None])
                maxima["supported_error_over_9mu2_delta_norm_b"] = max(
                    maxima["supported_error_over_9mu2_delta_norm_b"],
                    supported_error / (9 * mu**2 * delta * norm(b[:, None])),
                )
                assert supported_error <= 9 * mu**2 * delta * norm(b[:, None])
                h = h_block[:, j]
                approximate = -h - factor @ vhat
                direct = (1 + u) * np.linalg.solve(physical - (1 + u) * np.eye(m + 4), h)
                physical_error = norm((approximate - direct)[:, None])
                maxima["near_physical_error_over_epsilon_norm_h"] = max(
                    maxima["near_physical_error_over_epsilon_norm_h"],
                    physical_error / (epsilon * norm(h[:, None])),
                )
                assert physical_error <= epsilon * norm(h[:, None])
                identity_relative_error = norm((-h - factor @ exact - direct)[:, None]) / (1 + norm(direct[:, None]))
                maxima["physical_identity_relative_error"] = max(
                    maxima["physical_identity_relative_error"], identity_relative_error
                )
                assert identity_relative_error < 1e-8
                near_cases += 1

            for y in far_heights:
                u = 1j * y
                h = rng.standard_normal(m + 4)
                b = adjoint(factor) @ h
                inverse = np.linalg.inv((1 + u) * coarse - np.eye(m))
                vhat = np.zeros(m, complex)
                for _iteration in range(iterations):
                    vhat = inverse @ (b + defect @ vhat)
                approximate = -h - factor @ vhat
                direct = (1 + u) * np.linalg.solve(physical - (1 + u) * np.eye(m + 4), h)
                error_ratio = norm((approximate - direct)[:, None]) / (epsilon * norm(h[:, None]))
                maxima["far_physical_error_over_epsilon_norm_h"] = max(
                    maxima["far_physical_error_over_epsilon_norm_h"], error_ratio
                )
                assert error_ratio <= 1
                far_cases += 1
            metrics += 1

    assert maxima["analytic_coupling_vs_pointwise_adjoint_difference"] > 1e-6
    print(json.dumps({
        "seed": seed,
        "numpy_version": np.__version__,
        "metrics": metrics,
        "near_poles": near_cases,
        "far_poles": far_cases,
        "outer_boundary_points": boundary_cases,
        "richardson_iterations": iterations,
        "taylor_coefficients": degree,
        "epsilon": epsilon,
        "mu": mu,
        "delta": delta,
        "maxima": maxima,
        "assertions": "PASS",
        "scope": "dense finite algebra checks; no FNF backend, split algorithm, asymptotic runtime or LRA claim",
    }, indent=2))


if __name__ == "__main__":
    main()
