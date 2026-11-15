#!/usr/bin/env python3
"""Dense algebra diagnostics for the bounded-spectrum sharp graph algorithm.

This checks subtraction, collected polynomial factors and actual quadrature.
It does not implement the sparse SDD backend or prove asymptotic node counts.
Known common graph kernels are removed solely for stable dense diagnostics.
"""

import json
import math

import numpy as np


SEED = 2026111508


def norm(matrix):
    return np.linalg.norm(matrix, 2)


def power(matrix, alpha):
    values, vectors = np.linalg.eigh(matrix)
    assert values[0] > 0
    return (vectors * values**alpha) @ vectors.T


def graph_case(rng, n, k):
    weights = rng.uniform(0.2, 1.0, (n, n))
    weights = np.triu(weights, 1)
    weights += weights.T
    laplacian = np.diag(weights.sum(axis=1)) - weights
    masses = rng.uniform(0.4, 2.0, n)
    scale = 1 / np.sqrt(masses)
    a_full = scale[:, None] * laplacian * scale[None, :]
    edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
    chosen = rng.choice(len(edges), k, replace=False)
    update = np.zeros((n, k))
    for column, edge_index in enumerate(chosen):
        i, j = edges[edge_index]
        weight = rng.uniform(0.05, 0.4)
        update[i, column] = math.sqrt(weight / masses[i])
        update[j, column] = -math.sqrt(weight / masses[j])
    kernel = np.sqrt(masses)
    basis = np.zeros((n, n - 1))
    basis[: n - 1] = np.eye(n - 1)
    basis[-1] = -kernel[: n - 1] / kernel[-1]
    basis = np.linalg.qr(basis, mode="reduced")[0]
    assert norm(kernel[None, :] @ basis) < 1e-12
    a = basis.T @ a_full @ basis
    u = basis.T @ update
    b = a + u @ u.T
    return a, b, u


def beta_coefficients(alpha, p):
    beta = np.zeros(p)
    beta[1] = alpha
    for j in range(1, p - 1):
        beta[j + 1] = beta[j] * (j - alpha) / (j + 1)
    return beta


def polynomial_factor(ca, cb, u, coefficients, t_scale, alpha):
    p = len(coefficients)
    right = np.zeros_like(u)
    right_blocks = [None] * (p - 1)
    for ell in range(p - 2, -1, -1):
        right = coefficients[ell + 1] * u + cb @ right
        right_blocks[ell] = right.copy()
    left = u.copy()
    answer = np.zeros_like(ca)
    for ell in range(p - 1):
        answer += t_scale ** (alpha - 1) * left @ right_blocks[ell].T
        left = ca @ left
    return answer


def main():
    rng = np.random.default_rng(SEED)
    geom_error = 0.0
    collected_error = 0.0
    polynomial_error = 0.0
    quad_ratio = 0.0
    cases = 0
    quadratures = 0
    for n in (5, 7):
        for k in (1, 2, 3):
            a, b, u = graph_case(rng, n, k)
            t_scale = 1.2 * max(norm(a), norm(b))
            identity = np.eye(n - 1)
            ca, cb = identity - a / t_scale, identity - b / t_scale
            for p in (2, 3, 4, 8):
                for s in (0.03, 0.4, 2.0, 8.0):
                    t = t_scale * s
                    ra = np.linalg.solve(a + t * identity, identity)
                    rb = np.linalg.solve(b + t * identity, identity)
                    original = ra - rb
                    subtracted = original.copy()
                    for j in range(1, p):
                        difference = np.linalg.matrix_power(ca, j) - np.linalg.matrix_power(cb, j)
                        subtracted -= difference / (t_scale * (1 + s) ** (j + 1))
                    remainder = (
                        np.linalg.matrix_power(ca, p) @ ra
                        - np.linalg.matrix_power(cb, p) @ rb
                    ) / (1 + s) ** p
                    error = norm(subtracted - remainder) * t_scale
                    geom_error = max(geom_error, error)
                    assert error < 1e-11
                    cases += 1

                for alpha in (0.3, 0.5, 0.7):
                    beta = beta_coefficients(alpha, p)
                    coefficient = beta.copy()
                    direct = np.zeros_like(a)
                    collected = np.zeros_like(a)
                    for j in range(1, p):
                        difference = np.linalg.matrix_power(ca, j) - np.linalg.matrix_power(cb, j)
                        direct += t_scale**alpha * beta[j] * difference
                    # A uniform trapezoid checks the collected rule's algebra.
                    # It does not implement the optimized Gaussian node rule.
                    level = 9.0
                    spacing = 0.16
                    lo = math.floor(-(level + 5) / alpha / spacing)
                    hi = math.ceil((level + 5) / (p - alpha) / spacing)
                    c_alpha = math.sin(math.pi * alpha) / math.pi
                    for node in range(lo, hi + 1):
                        s = math.exp(node * spacing)
                        t = t_scale * s
                        ra_u = np.linalg.solve(a + t * identity, u)
                        rb_u = np.linalg.solve(b + t * identity, u)
                        original = ra_u @ rb_u.T
                        omega = spacing * c_alpha * t ** (alpha + 1)
                        collected += omega * original
                        ra = np.linalg.solve(a + t * identity, identity)
                        rb = np.linalg.solve(b + t * identity, identity)
                        remainder = (
                            np.linalg.matrix_power(ca, p) @ ra
                            - np.linalg.matrix_power(cb, p) @ rb
                        ) / (1 + s) ** p
                        direct += omega * remainder
                        for j in range(1, p):
                            coefficient[j] -= (
                                spacing * c_alpha * s ** (alpha + 1) / (1 + s) ** (j + 1)
                            )
                    polynomial_direct = np.zeros_like(a)
                    for j in range(1, p):
                        difference = np.linalg.matrix_power(ca, j) - np.linalg.matrix_power(cb, j)
                        polynomial_direct += t_scale**alpha * coefficient[j] * difference
                    polynomial_factored = polynomial_factor(ca, cb, u, coefficient, t_scale, alpha)
                    error = norm(polynomial_direct - polynomial_factored) / t_scale**alpha
                    polynomial_error = max(polynomial_error, error)
                    assert error < 1e-11
                    collected += polynomial_factored
                    error = norm(direct - collected) / t_scale**alpha
                    collected_error = max(collected_error, error)
                    assert error < 1e-10
                    reference = power(b, alpha) - power(a, alpha)
                    ratio = norm(collected - reference) / (t_scale**alpha * math.exp(-level))
                    quad_ratio = max(quad_ratio, ratio)
                    assert ratio < 1.0
                    quadratures += 1
    print(json.dumps({
        "seed": SEED,
        "numpy_version": np.__version__,
        "graph_pairs": 6,
        "geometric_identity_cases": cases,
        "collected_quadrature_cases": quadratures,
        "max_scaled_geometric_identity_error": geom_error,
        "max_scaled_polynomial_factor_error": polynomial_error,
        "max_scaled_collected_rule_error": collected_error,
        "max_quadrature_error_over_exp_minus_L_budget": quad_ratio,
        "assertions": "PASS",
        "scope": "dense algebra and ordinary-grid corroboration, not optimized-node or sparse-runtime verification",
    }, indent=2))


if __name__ == "__main__":
    main()
