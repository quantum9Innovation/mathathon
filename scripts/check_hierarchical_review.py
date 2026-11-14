#!/usr/bin/env python3
"""Reproduce review arithmetic and optional noncommuting numerical diagnostics.

The numerical checks use dense eigendecompositions as diagnostic tools. They
are not an implementation, timing benchmark, or proof of the fast algorithm.
Run with --numpy for diagnostics in addition to the standard-library checks.
"""

import argparse
from fractions import Fraction as F
import json
import math


def multiplication_exponent(*shape):
    a, b, c = sorted(shape, reverse=True)
    if c * (a + b) <= a * b:
        return a + b
    return (a + b + c) / 2 + (a * b / c + a * c / b + b * c / a) / 4


def arithmetic():
    alpha = (3 * math.sqrt(5) - 5) / 2
    saving = (7 - 3 * math.sqrt(5)) / 8
    coarse = multiplication_exponent(F(57, 50), F(1), F(1))
    true = multiplication_exponent(F(59, 50), F(1), F(14, 25)) + (F(11, 25) - F(1, 12)) / 2
    fine_kernel = multiplication_exponent(F(7, 6), F(1), F(14, 25))
    fine = fine_kernel - F(7, 100) + (F(1, 12) + F(11, 25)) / 2
    assert coarse == F(3362, 1425)
    assert true == F(29227553, 12390000)
    assert fine_kernel == F(867, 400)
    assert fine == F(2831, 1200)
    assert coarse - fine == F(1, 7600)
    assert coarse / F(59, 50) == F(6724, 3363)
    rows = []
    for N in (10**4, 10**6, 10**9):
        m = N**alpha
        rows.append(dict(N=N, m=m, rank_cap=math.isqrt(round(m)),
                         theta=(m / N)**2.5,
                         leading_power_ratio=N**saving,
                         dense_output_decimal_GB=8 * N * N / 1e9))
    return dict(alpha=alpha, saving=saving,
                first_level_min_log10_N=40 * math.log10(2) / (1 - alpha),
                two_level_exponents=dict(coarse=str(coarse), true=str(true),
                                         fine=str(fine), fine_kernel=str(fine_kernel)),
                illustrative_dimensions=rows)


def numerical():
    import numpy as np
    from numpy.polynomial.chebyshev import chebval

    rng = np.random.default_rng(20261114)

    def symmetric(X):
        return (X + X.T) / 2

    def matrix_function(X, f):
        vals, vectors = np.linalg.eigh(symmetric(X))
        return (vectors * f(vals)) @ vectors.T

    def min_relative(X, D):
        Di = matrix_function(D, lambda x: 1 / np.sqrt(x))
        return float(np.linalg.eigvalsh(symmetric(Di @ X @ Di)).min())

    def polynomial_matrix(X, coefficients):
        result = np.zeros_like(X)
        for coefficient in reversed(coefficients):
            result = result @ X + coefficient * np.eye(len(X))
        return result

    worst_margin = 0.0
    worst_carry_error = 0.0
    largest_degree_bound = 0
    for _ in range(48):
        k = 5
        X = rng.normal(size=(k, k))
        D = X @ X.T + np.eye(k)
        Dh = matrix_function(D, np.sqrt)
        A = symmetric(rng.normal(size=(k, k)))
        A *= 0.75 / np.linalg.norm(A, 2)
        H = float(10 ** rng.uniform(-4, -2))
        h = H / 1024
        epsilon = h / H
        K = Dh @ A @ Dh
        Fprev = Dh @ matrix_function(A, lambda x: np.sqrt(x*x + (8*H)**2) + 8*H) @ Dh
        E = symmetric(rng.normal(size=(k, k)))
        E *= 8 * h / np.linalg.norm(E, 2)
        E = Dh @ E @ Dh
        Kj = K + E
        Rp = np.linalg.inv(np.linalg.cholesky(Fprev)).T / math.sqrt(1 + epsilon)
        Aj = symmetric(Rp.T @ Kj @ Rp)
        eta = 8 * epsilon
        tau = h / (10**6 * 3)
        nodes = 1
        while -nodes * math.log1p(eta / 4) > math.log(tau * eta**1.5 / 1000):
            nodes *= 2
        largest_degree_bound = max(largest_degree_bound, nodes)
        grid = np.cos(np.pi * (np.arange(nodes) + 0.5) / nodes)
        values = 1 / np.sqrt(np.sqrt(grid*grid + eta*eta) + eta)
        extension = np.concatenate((values, values[::-1]))
        coefficients = (np.fft.fft(extension)[:nodes] *
                        np.exp(-1j * np.pi * np.arange(nodes) / (2*nodes))).real / nodes
        coefficients[0] /= 2
        pAj = matrix_function(Aj, lambda x: chebval(x, coefficients))
        Rj = Rp @ pAj
        Rji = np.linalg.inv(Rj)
        Fj = symmetric(Rji.T @ Rji)
        inverse = np.linalg.inv(Fj)
        Cj = 100 * (36 + 1)
        checks = (Fj - 8*h*D, 4*D - Fj,
                  Fj - K - 55*h*D, Fj + K - 55*h*D,
                  Cj*h*D - (Fj - 5*K @ inverse @ K))
        margin = min(min_relative(check, D) for check in checks)
        worst_margin = min(worst_margin, margin)
        assert margin > -1e-8, margin

        R0 = np.eye(k) + 0.1 * rng.normal(size=(k, k))
        S = np.eye(k) + 0.1 * rng.normal(size=(k, k))
        A0 = symmetric(rng.normal(size=(k, k))) / 10
        Xi = rng.normal(size=(k, 3))
        T = np.eye(k) - S.T @ A0 @ S
        V = np.eye(k) - A0 @ S @ S.T
        coefficients = [0.2, -0.3, 0.4, -0.1, 0.05]
        Y = polynomial_matrix(T, coefficients) @ S.T @ Xi
        Wo = polynomial_matrix(V, coefficients) @ Xi
        left = np.linalg.inv(R0 @ S).T @ Y
        right = np.linalg.inv(R0).T @ Wo
        error = float(np.linalg.norm(left-right) / max(1.0, np.linalg.norm(right)))
        worst_carry_error = max(worst_carry_error, error)
        assert error < 1e-10, error

    return dict(trials=48, seed=20261114, worst_negative_normalized_margin=worst_margin,
                worst_relative_carry_error=worst_carry_error,
                largest_dyadic_interpolation_node_count=largest_degree_bound,
                scope="diagnostics only; no proof or algorithmic timing claim")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numpy", action="store_true", help="run optional matrix diagnostics")
    args = parser.parse_args()
    result = dict(arithmetic=arithmetic())
    if args.numpy:
        result["numerical"] = numerical()
    print(json.dumps(result, indent=2))
