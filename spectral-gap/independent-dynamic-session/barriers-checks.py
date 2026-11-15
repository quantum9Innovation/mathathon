"""Numerical checks for the independent dynamic barriers/flow audit.

These are diagnostics for identities and inequalities proved in the notes,
not substitutes for the access-model proof or a full dynamic algorithm.
"""
import json
from pathlib import Path

import mpmath as mp
import numpy as np


def barrier_checks():
    mp.mp.dps = 90
    alpha, tau = mp.mpf("0.37"), mp.mpf("1.8")
    s = tau / 2
    target = ((1 + tau) / (1 + s)) ** alpha - 1
    rows = []
    for exponent in (2, 6, 12, 24):
        a = mp.mpf(10) ** (-exponent)
        z1, z2 = s / (1 - a), s * (1 - 2 * a) / (1 - a)
        update = mp.matrix([mp.sqrt(a * z1), mp.sqrt(z2)])
        mat_a = mp.diag([a, 1])
        mat_b = mat_a + update * update.T
        evals, evecs = mp.eigsy(mat_b)
        powered = evecs * mp.diag([x ** alpha for x in evals]) * evecs.T
        low = powered[0, 0] / (a ** alpha) - 1
        h = a * z1 / (a + 1) + z2 / 2
        h_formula = s / 2 + s * a / ((a + 1) * 2)
        assert abs(h - h_formula) < mp.mpf("1e-80")
        assert abs(z1 + z2 - tau) < mp.mpf("1e-80")
        rows.append({"a": str(a), "relative_low": float(low),
                     "limit": float(target), "error": float(abs(low - target)),
                     "positive_shift_energy_error_squared":
                         float(a * (1 - a) / (2 * (1 + 2 * a)))})
    assert rows[-1]["error"] < 1e-10
    return rows


def flow_checks():
    rng = np.random.default_rng(721694)
    maxima = {"clip_error_ratio": 0., "inverse_energy_ratio": 0.,
              "ground_energy_ratio": 0., "interpolation_ratio": 0.}
    for _ in range(100):
        n = 8
        edges = [(i, i + 1) for i in range(n - 1)]
        edges += [(0, 3), (2, 6), (1, 7), (0, 6)]
        b = np.zeros((len(edges), n))
        for j, (p, q) in enumerate(edges):
            b[j, p], b[j, q] = 1., -1.
        weights = np.exp(rng.normal(size=len(edges)))
        lap = b.T @ (weights[:, None] * b)
        pinv = np.linalg.inv(lap + np.ones((n, n)) / n) - np.ones((n, n)) / n
        d = float(np.exp(rng.normal()))
        u = np.sqrt(d) * b[0]
        v = pinv @ u
        tau = u @ v
        eta = .1
        noise = rng.normal(size=n)
        noise -= noise.mean()
        noise *= eta * np.sqrt(tau / (noise @ lap @ noise))
        q = v + noise
        assert q[0] > q[1]
        vh = np.clip(q, q[1], q[0])
        vh -= vh.mean()
        err0 = (q - v) @ lap @ (q - v)
        err1 = (vh - v) @ lap @ (vh - v)
        assert err1 <= err0 * (1 + 1e-10)
        maxima["clip_error_ratio"] = max(maxima["clip_error_ratio"], err1 / err0)
        assert vh @ vh <= n * (1 + eta) ** 2 * tau ** 2 / d
        t = float(np.exp(rng.normal()))
        y = np.linalg.solve(lap + t * np.eye(n), vh)
        fstar, gstar = weights * (b @ y), t * y
        df = rng.normal(size=len(edges))
        dg = -(b.T @ df)
        xhat = b.T @ (fstar + df)
        assert np.linalg.norm(xhat - (vh - gstar - dg)) < 1e-10
        e = b.T @ df
        energy = np.sum(df * df / weights) + (dg @ dg) / t
        inv_energy = e @ pinv @ e
        norm_energy = e @ e
        evals, evecs = np.linalg.eigh(lap)
        coeffs = evecs[:, 1:].T @ e
        alpha = .37
        fractional_energy = np.sum(coeffs * coeffs / evals[1:] ** alpha)
        assert inv_energy <= energy * (1 + 1e-10)
        assert norm_energy <= t * energy * (1 + 1e-10)
        assert fractional_energy <= t ** (1 - alpha) * energy * (1 + 1e-10)
        maxima["inverse_energy_ratio"] = max(maxima["inverse_energy_ratio"], inv_energy / energy)
        maxima["ground_energy_ratio"] = max(maxima["ground_energy_ratio"], norm_energy / (t * energy))
        maxima["interpolation_ratio"] = max(maxima["interpolation_ratio"], fractional_energy / (t ** (1 - alpha) * energy))
    return {"trials": 100, "maxima": maxima}


if __name__ == "__main__":
    result = {"status": "passed", "barrier": barrier_checks(), "flow": flow_checks()}
    destination = Path(__file__).with_name("barriers-checks.json")
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
