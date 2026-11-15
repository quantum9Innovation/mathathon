"""Numerically verify Gram quadrature and cutoff constants on weighted paths."""
import json
from pathlib import Path

import numpy as np
from scipy.linalg import eigh


def matrix_power(a, exponent):
    w, v = eigh(a)
    assert w[0] > 0
    return (v * w ** exponent) @ v.T


def main():
    rng = np.random.default_rng(72793)
    n, tau, eps = 15, 1.5, 0.1
    weights = np.exp(np.linspace(-4, 4, n - 1))
    lap = np.zeros((n, n))
    edges = []
    for i, weight in enumerate(weights):
        edge = np.zeros(n)
        edge[i], edge[i + 1] = 1, -1
        lap += weight * np.outer(edge, edge)
        edges.append(edge)
    all_evals, all_evecs = eigh(lap)
    lam, basis = all_evals[1:], all_evecs[:, 1:]
    edit = n // 2
    d = tau * weights[edit]
    update = np.sqrt(d) * (basis.T @ edges[edit])
    results = []
    for alpha in [0.3, 0.5, 0.8]:
        beta = 1 - alpha
        c = np.sin(np.pi * alpha) / np.pi
        delta = matrix_power(np.diag(lam) + np.outer(update, update), alpha)
        delta -= np.diag(lam ** alpha)
        dz, vz = eigh(delta)
        assert dz[0] > -1e-10
        z = vz * np.sqrt(np.maximum(dz, 0))
        # The physical factor is basis @ z; working in the common support
        # avoids contaminating very small shifts with floating-point nullspace error.
        a0 = np.linalg.norm(z, "fro") ** 2
        a1 = np.sum(z ** 2 / lam[:, None])
        p = max(1.0, a0 * d ** (-alpha), a1 * d ** beta)
        gamma = eps / 8
        low = d * min(1.0, (gamma * beta / (4 * c * p)) ** (1 / beta))
        high = d * max(1.0, (4 * c * p / (alpha * gamma)) ** (1 / alpha))
        strip = np.pi / 2
        mbar = c * p / (alpha * beta * np.cos(strip / 2))
        step = min(1.0, 2 * np.pi * strip / np.log1p(8 * mbar / gamma))
        first = int(np.floor(np.log(low / d) / step))
        last = int(np.ceil(np.log(high / d) / step))
        eta = min(1.0, gamma * alpha * beta / (8 * c * p))
        h_exact = z.T @ (lam[:, None] ** (-alpha) * z)
        h_quad = np.zeros_like(h_exact)
        h_approx = np.zeros_like(h_exact)
        maximum_column_energy_ratio = 0.0
        for j in range(first, last + 1):
            shift = d * np.exp(j * step)
            coefficient = c * step * shift ** beta
            x = z / (lam + shift)[:, None]
            h_quad += coefficient * z.T @ x
            column_energy = np.sum(z * x, axis=0)
            direction = rng.standard_normal(z.shape)
            direction /= np.linalg.norm(direction, axis=0)[None, :]
            perturbation = direction * (eta * np.sqrt(column_energy))[None, :]
            perturbation /= np.sqrt(lam + shift)[:, None]
            observed_squared = np.divide(
                np.sum((lam + shift)[:, None] * perturbation ** 2, axis=0),
                column_energy, out=np.zeros_like(column_energy), where=column_energy > 0)
            observed = np.sqrt(observed_squared)
            maximum_column_energy_ratio = max(maximum_column_energy_ratio,
                                               float(np.max(observed)))
            block = z.T @ (x + perturbation)
            h_approx += coefficient * (block + block.T) / 2
        gram_error = np.linalg.norm(h_approx - h_exact, 2)
        assert gram_error <= gamma
        sh, vh = eigh(h_approx)
        selected = vh[:, sh > eps / 2]
        factor = z @ selected
        g = lam[:, None] ** (-alpha / 2) * z
        gf = lam[:, None] ** (-alpha / 2) * factor
        correction = (lam[:, None] ** (-alpha / 2) * delta
                      * lam[None, :] ** (-alpha / 2))
        raw_error = np.linalg.norm(g @ g.T - correction, 2)
        residual = eigh(correction - gf @ gf.T, eigvals_only=True)
        budget = alpha * np.log1p(tau)
        strict_rank = max(0, int(np.ceil(budget / np.log1p(eps / 4))) - 1)
        assert factor.shape[1] <= strict_rank
        assert residual[0] >= -eps / 8 - 1e-10
        assert residual[-1] <= 3 * eps / 4 + 1e-10
        results.append({"alpha": alpha, "P": float(p), "nodes": last - first + 1,
                        "eta": float(eta), "raw_error": float(raw_error),
                        "exact_quadrature_error": float(np.linalg.norm(h_quad - h_exact, 2)),
                        "inexact_gram_error": float(gram_error),
                        "gram_error_budget": gamma,
                        "observed_column_energy_ratio": maximum_column_energy_ratio,
                        "returned_rank": factor.shape[1], "strict_rank_bound": strict_rank,
                        "minimum_relative_residual": float(residual[0]),
                        "maximum_relative_residual": float(residual[-1])})
    destination = Path(__file__).with_name("balanced-gram-checks.json")
    destination.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
