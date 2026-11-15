#!/usr/bin/env python3
"""Finite algebra diagnostics for the Gaussian cone-span obstruction.

These checks corroborate identities and constants. They do not prove the
asymptotic probability statement or provide an arithmetic lower bound.
Requires NumPy and prints a reproducible JSON verification summary.
"""

import json
import math

import numpy as np


SEED = 2026111508


def phi_values(x, eta, degree):
    x = np.asarray(x, dtype=float)
    out = np.empty((degree + 1,) + x.shape)
    out[0] = math.sqrt(math.sinh(eta))
    if degree == 0:
        return out
    z = math.exp(-eta)
    previous = np.ones_like(x)
    current = x.copy()
    for j in range(1, degree + 1):
        out[j] = (current - z * previous) / math.sqrt(z)
        previous, current = current, 2 * x * current - previous
    return out


def main():
    rng = np.random.default_rng(SEED)
    max_gram_error = 0.0
    gram_cases = 0
    max_kernel_ratio = 0.0
    kernel_cases = 0
    max_leverage_ratio = 0.0
    leverage_cases = 0

    for n in (8, 16, 32, 64):
        x = np.cos((np.arange(n) + 0.5) * np.pi / n)
        for eta in (0.15, 0.3, 0.6):
            center = math.cosh(eta)
            for degree in (0, 1, min(4, n // 2), min(10, n // 2)):
                values = phi_values(x, eta, degree)
                weighted = values / np.sqrt(center - x)
                actual = weighted @ weighted.T / n
                at_center = phi_values(np.array(center), eta, degree)
                delta = (1 - math.tanh(n * eta)) / math.sinh(eta)
                predicted = np.eye(degree + 1) - delta * np.outer(
                    at_center, at_center
                )
                err = np.linalg.norm(actual - predicted, 2)
                max_gram_error = max(max_gram_error, err)
                assert err < 2e-10, (n, eta, degree, err)
                gram_cases += 1

    for eta in (0.05, 0.15, 0.3):
        for ratio in (1, 1.5, 2.5, 3):
            zeta = ratio * eta
            for degree in (0, 1, 4, 10):
                values = phi_values(np.array(math.cosh(zeta)), eta, degree)
                kernel = float(values @ values)
                bound = 32 * eta * math.exp(2 * degree * zeta)
                observed = kernel / bound
                max_kernel_ratio = max(max_kernel_ratio, observed)
                assert observed <= 1 + 1e-12
                kernel_cases += 1

    x = np.linspace(-1, 1, 2001)
    for eta in (0.05, 0.15, 0.4, 0.8):
        for degree in (0, 1, 4, 16):
            values = phi_values(x, eta, degree)
            actual = np.max(np.sum(values**2, axis=0) / (math.cosh(eta) - x))
            bound = 3 / eta + 12 * degree
            observed = actual / bound
            max_leverage_ratio = max(max_leverage_ratio, observed)
            assert observed <= 1 + 1e-12
            leverage_cases += 1

    necessary_cases = 0
    max_secular_comparison_error = 0.0
    for dimension in range(4, 13):
        target = 1.1
        spectrum = np.r_[1.4, 1.0, rng.uniform(0.7, 1, dimension - 2)]
        gap_head = spectrum[0] ** 2 - target**2
        bulk_denominators = target**2 - spectrum[1:] ** 2
        for scale in (0.1, 1, 10):
            for _ in range(5):
                vector = rng.normal(size=dimension) + 1j * rng.normal(
                    size=dimension
                )
                vector[0] *= scale
                q, _ = np.linalg.qr(vector[:, None], mode="complete")
                complement = q[:, 1:]
                compressed = complement.conj().T @ (
                    spectrum[:, None] ** 2 * complement
                )
                eigen_slack = target**2 - np.linalg.eigvalsh(compressed)[-1]
                condition_slack = abs(vector[0]) ** 2 - gap_head * np.sum(
                    abs(vector[1:]) ** 2 / bulk_denominators
                )
                if abs(eigen_slack) > 1e-9 and abs(condition_slack) > 1e-9:
                    assert (eigen_slack >= 0) == (condition_slack >= 0)
                projection = np.eye(dimension) - np.outer(
                    vector, vector.conj()
                ) / np.vdot(vector, vector)
                projected_norm_squared = np.linalg.norm(
                    projection * spectrum[None, :], 2
                ) ** 2
                err = abs(projected_norm_squared - np.linalg.eigvalsh(compressed)[-1])
                max_secular_comparison_error = max(
                    max_secular_comparison_error, err
                )
                assert err < 1e-11
                necessary_cases += 1

    cone_cases = 0
    max_cone_error_ratio = 0.0
    for cone in (0.25, 0.5, 1):
        width = cone / 4
        eigenvalues = np.r_[1 + 4 / 10000, 1, np.linspace(1 - width, 1, 61)]
        angle = math.asin(cone)
        for pole_angle in (angle, math.pi / 2, math.pi - angle):
            for magnitude in (0.05, 0.2, 1, 5, 20):
                pole = magnitude * np.exp(1j * pole_angle)
                coefficient = pole / (1 - pole)
                exact = (1 - pole) / (1 - pole * eigenvalues)
                for degree in (0, 1, 3, 8):
                    powers = coefficient * (eigenvalues - 1)
                    approximate = sum(powers**j for j in range(degree + 1))
                    err = np.max(abs(approximate - exact))
                    bound = (4 / 3) * 4 ** (-degree - 1)
                    observed = err / bound
                    max_cone_error_ratio = max(max_cone_error_ratio, observed)
                    assert observed <= 1 + 1e-8
                    cone_cases += 1

    print(
        json.dumps(
            {
                "seed": SEED,
                "numpy_version": np.__version__,
                "weighted_grid_gram_cases": gram_cases,
                "max_weighted_grid_gram_identity_error": max_gram_error,
                "christoffel_bound_cases": kernel_cases,
                "max_christoffel_kernel_over_bound": max_kernel_ratio,
                "leverage_bound_cases": leverage_cases,
                "max_leverage_over_bound": max_leverage_ratio,
                "rank_one_secular_cases": necessary_cases,
                "max_projected_norm_squared_identity_error": max_secular_comparison_error,
                "cone_operator_cases": cone_cases,
                "max_cone_error_over_bound": max_cone_error_ratio,
                "assertions": "PASS",
                "scope": "finite algebra diagnostics, not proof of the asymptotic probability or a raw-input lower bound",
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
