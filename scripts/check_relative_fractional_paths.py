#!/usr/bin/env python3
"""Diagnostics for the path-transfer algebra, not proofs or novelty evidence."""
import json
import numpy as np


def power_psd(a, p):
    vals, vecs = np.linalg.eigh(a)
    # Every input here is a connected graph Laplacian, with known nullity one.
    assert vals[1] > 0
    powers = np.zeros_like(vals)
    powers[1:] = vals[1:] ** p
    return (vecs * powers) @ vecs.T


def response(a, b, alpha):
    inverse = power_psd(a, -alpha / 2)
    c = inverse @ (power_psd(b, alpha) - power_psd(a, alpha)) @ inverse
    return (c + c.T) / 2


def path_laplacian(weights):
    n = len(weights) + 1
    out = np.zeros((n, n))
    for i, w in enumerate(weights):
        out[i, i] += w
        out[i + 1, i + 1] += w
        out[i, i + 1] -= w
        out[i + 1, i] -= w
    return out


def sorted_spectrum(a):
    return np.linalg.eigvalsh(a)[::-1]


def main():
    alphas = [0.3, 0.5, 0.7]
    tridiagonal = np.array([[2.0, -0.4, 0.0], [-0.4, 3.0, -0.5],
                            [0.0, -0.5, 4.0]])
    kappa = 0.7
    d = np.linalg.solve(tridiagonal, np.array([1.0, 0.0, 0.0]))
    assert np.all(d > 0)
    tau = kappa * d[0]
    vals, vecs = np.linalg.eigh(tridiagonal)
    update = np.zeros((3, 3))
    update[0, 0] = kappa
    bvals, bvecs = np.linalg.eigh(tridiagonal + update)
    mass_results = []
    for alpha in alphas:
        inv = (vecs * vals ** (-alpha / 2)) @ vecs.T
        delta = ((bvecs * bvals ** alpha) @ bvecs.T
                 - (vecs * vals ** alpha) @ vecs.T)
        expected = np.sort(np.r_[np.linalg.eigvalsh(inv @ delta @ inv), 0])[::-1]
        errors = []
        for ground_size in [10.0, 100.0, 1000.0]:
            h = np.zeros((4, 4))
            h[0, 0] = d[0] / ground_size ** 2
            h[0, 1] = h[1, 0] = -1 / ground_size
            h[1:, 1:] = tridiagonal
            v = np.r_[-d[0] / ground_size, 1.0, 0.0, 0.0]
            hp = h + kappa * np.outer(v, v)
            c = response(h, hp, alpha)
            error = float(np.max(np.abs(sorted_spectrum(c) - expected)))
            errors.append(error)
            budget_error = abs(np.log1p(np.linalg.eigvalsh(c)).sum()
                               - alpha * np.log1p(tau))
            assert budget_error < 1e-10
        assert errors[-1] < 2e-7
        assert errors[-1] < errors[0] / 1000
        mass_results.append(dict(alpha=alpha, spectral_errors=errors))

    # Integer vertex masses allow testing the second, fast-block limit directly.
    masses = np.array([2, 3, 4])
    weights = np.array([1.2, 0.7])
    tau = 0.8
    k = path_laplacian(weights)
    kp = path_laplacian(weights * np.array([1 + tau, 1]))
    scale = np.diag(masses.astype(float) ** -0.5)
    h, hp = scale @ k @ scale, scale @ kp @ scale
    block_results = []
    total_vertices = int(masses.sum())
    for alpha in alphas:
        reference = sorted_spectrum(response(h, hp, alpha))
        expected = np.sort(np.r_[reference, np.zeros(total_vertices - 3)])[::-1]
        errors = []
        budget_errors = []
        for internal_weight in [10.0, 1000.0, 100000.0]:
            physical_weights = []
            changed_index = None
            for cell, cell_size in enumerate(masses):
                physical_weights.extend([internal_weight] * (int(cell_size) - 1))
                if cell < len(weights):
                    if cell == 0:
                        changed_index = len(physical_weights)
                    physical_weights.append(float(weights[cell]))
            physical_weights = np.array(physical_weights)
            updated_weights = physical_weights.copy()
            updated_weights[changed_index] *= 1 + tau
            assert abs(updated_weights[changed_index]
                       / physical_weights[changed_index] - (1 + tau)) < 1e-15
            l = path_laplacian(physical_weights)
            lp = path_laplacian(updated_weights)
            c = response(l, lp, alpha)
            errors.append(float(np.max(np.abs(sorted_spectrum(c) - expected))))
            budget_errors.append(float(abs(np.log1p(np.linalg.eigvalsh(c)).sum()
                                           - alpha * np.log1p(tau))))
        assert errors[-1] < 0.002
        assert errors[-1] < errors[0] / 50
        assert max(budget_errors) < 1e-7
        block_results.append(dict(alpha=alpha, spectral_errors=errors,
                                  determinant_budget_errors=budget_errors))
    print(json.dumps(dict(mass_path=mass_results, unit_mass_blocks=block_results,
                          status="PASS"), indent=2))


if __name__ == "__main__":
    main()
