#!/usr/bin/env python3
"""Dense finite algebra checks for balanced-permutation-concentration.txt.

These checks verify rectangular variance, the combinatorial dilation
variance proxy, truncation Loewner inequalities, and the scalar parameter
choice. They do not implement the large theoretical degree or establish
a statistical tail theorem by experiment.
"""

import json
import math

import numpy as np

from check_balanced_permutation_amm import partitions


def dilation(x):
    n, p = x.shape
    return np.block([[np.zeros((n, n)), x],
                     [x.T, np.zeros((p, p))]])


def main():
    rng = np.random.default_rng(2026111504)
    cases = [(4, 2), (4, 4), (6, 2), (6, 3), (6, 6),
             (8, 2), (8, 4), (8, 8)]
    covariance_error = 0.0
    array_proxy_error = 0.0
    unbiased_error = 0.0
    min_truncation_eigenvalue = 0.0
    graph_pairs = 0
    enumerated_partitions = 0

    for m, s in cases:
        q = m // s
        rho = (q - 1) / (m - 1)
        gamma = 1 / (1 - rho)
        pi = np.eye(m) - np.ones((m, m)) / m
        c = (m - s) / (s - 1)
        v = c / m
        u = -v / (m - 2)
        w = 2 * v / ((m - 2) * (m - 3))
        ac = v - 2 * u + 2 * w
        bc = v - 2 * u + w
        kappa = 2 * (v - 4 * u + 3 * w)
        all_parts = list(partitions(tuple(range(m)), q))
        enumerated_partitions += len(all_parts)

        for trial in range(3):
            a = rng.normal(size=(3, m))
            b = rng.normal(size=(m, 2))
            a /= np.linalg.norm(a, 2)
            b /= np.linalg.norm(b, 2)
            a0, b0 = a @ pi, pi @ b
            xs = []
            for partition in all_parts:
                h = np.zeros((s, m))
                for bucket, block in enumerate(partition):
                    h[bucket, list(block)] = 1
                gram = gamma * (h.T @ h - rho * np.ones((m, m)))
                xs.append(a @ (gram - np.eye(m)) @ b)
            mean = np.mean(xs, axis=0)
            left = np.mean([x @ x.T for x in xs], axis=0)
            right = np.mean([x.T @ x for x in xs], axis=0)
            product = a0 @ b0
            expected_left = (ac * product @ product.T
                             + bc * np.sum(b0 * b0) * a0 @ a0.T
                             - kappa * a0 @ np.diag(np.sum(b0 * b0, axis=1)) @ a0.T)
            expected_right = (ac * product.T @ product
                              + bc * np.sum(a0 * a0) * b0.T @ b0
                              - kappa * b0.T @ np.diag(np.sum(a0 * a0, axis=0)) @ b0)
            err = max(np.linalg.norm(left - expected_left, 2),
                      np.linalg.norm(right - expected_right, 2))
            covariance_error = max(covariance_error, err)
            unbiased_error = max(unbiased_error, np.linalg.norm(mean, 2))
            assert err < 1e-12
            assert np.linalg.norm(mean, 2) < 1e-12

            full_second = np.mean([dilation(x) @ dilation(x) for x in xs], axis=0)
            threshold = float(np.median([np.linalg.norm(x, 2) for x in xs]))
            ys = [x if np.linalg.norm(x, 2) <= threshold else np.zeros_like(x)
                  for x in xs]
            trim_mean = np.mean(ys, axis=0)
            centered_second = np.mean([
                dilation(y - trim_mean) @ dilation(y - trim_mean) for y in ys
            ], axis=0)
            smallest = np.linalg.eigvalsh(full_second - centered_second)[0]
            min_truncation_eigenvalue = min(min_truncation_eigenvalue, float(smallest))
            assert smallest > -1e-12

            fixed_h = np.zeros((s, m))
            for j in range(m):
                fixed_h[j // q, j] = 1
            proxy = np.zeros((s + 2, s + 2))
            for i in range(m):
                for j in range(m):
                    bucket = fixed_h[:, j] - np.ones(s) / s
                    entry = dilation(np.outer(bucket, b0[i]))
                    proxy += entry @ entry / m
            expected_proxy = np.block([
                [np.sum(b0 * b0) / s * (np.eye(s) - np.ones((s, s)) / s),
                 np.zeros((s, 2))],
                [np.zeros((2, s)), (1 - 1 / s) * b0.T @ b0]
            ])
            proxy_err = np.linalg.norm(proxy - expected_proxy, 2)
            array_proxy_error = max(array_proxy_error, proxy_err)
            assert proxy_err < 1e-12
            graph_pairs += 1

    scalar_cases = 0
    c0 = 2 ** 20
    worst_implicit_over_chosen = 0.0
    for rank in (1.0, 2.0, 3.5, 8.0, 30.0):
        for eps in (0.05, 0.2, 0.8):
            for delta in (0.001, 0.1, 0.7):
                s = math.ceil(1 + rank / eps)
                physical_n, physical_p = 31, 19
                dim = 2 * s + physical_n + physical_p
                ell = math.log(c0 * dim / (delta * eps))
                degree = math.ceil(c0 / eps * ell ** 3)
                h = math.log(8192 * dim * degree / (delta * eps))
                variance = 3 * (rank + 2) / (s - 1)
                implicit = (12 * variance / eps ** 2 + 4104 * h ** 2 / eps)
                implicit *= math.log(4 * (physical_n + physical_p) / delta)
                assert degree >= implicit
                assert h < 4 * ell
                worst_implicit_over_chosen = max(worst_implicit_over_chosen,
                                                implicit / degree)
                scalar_cases += 1

    print(json.dumps({
        "seed": 2026111504,
        "numpy_version": np.__version__,
        "rectangular_factor_pairs": graph_pairs,
        "distinct_balanced_partitions": enumerated_partitions,
        "max_rectangular_covariance_error": covariance_error,
        "max_unbiasedness_error": unbiased_error,
        "max_combinatorial_proxy_error": array_proxy_error,
        "minimum_truncation_covariance_difference_eigenvalue": min_truncation_eigenvalue,
        "scalar_parameter_cases": scalar_cases,
        "max_implicit_requirement_over_explicit_degree": worst_implicit_over_chosen,
        "assertions": "PASS",
        "scope": "finite algebra and scalar diagnostics, not proof of asymptotic concentration"
    }, indent=2))


if __name__ == "__main__":
    main()
