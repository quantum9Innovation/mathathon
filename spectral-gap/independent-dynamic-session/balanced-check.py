"""Check the raw generalized Nyström identity; numerical checks are not proofs."""
import json
from pathlib import Path

import numpy as np
from scipy.linalg import eigh


def positive_power(a, power):
    d, q = eigh(a)
    return (q * np.maximum(d, 0.0) ** power) @ q.T


def main():
    rng = np.random.default_rng(32173)
    out = []
    n, alpha, tau, width = 48, 0.5, 2.0, 8
    for spread in [0.0, 2.0, 5.0]:
        a = np.exp(np.linspace(-spread, spread, n))
        v = rng.standard_normal(n)
        v *= np.sqrt(tau / (v @ v))
        u = np.sqrt(a) * v
        b_matrix = np.diag(a) + np.outer(u, u)
        delta = positive_power(b_matrix, alpha) - np.diag(a ** alpha)
        whitening = a ** (-alpha / 2)
        c = whitening[:, None] * delta * whitening[None, :]
        c = (c + c.T) / 2
        g = rng.standard_normal((n, width))
        omega = whitening[:, None] * g
        y = delta @ omega
        m = (omega.T @ y + y.T @ omega) / 2
        w, q = eigh(m)
        threshold = max(w[-1], 1.0) * 1e-13
        keep = w > threshold
        x = y @ (q[:, keep] / np.sqrt(w[keep]))
        relative_factor = whitening[:, None] * x
        chat = relative_factor @ relative_factor.T
        # A separate whitened Nyström calculation checks the raw identity.
        yc = c @ g
        mc = (g.T @ yc + yc.T @ g) / 2
        wc, qc = eigh(mc)
        keepc = wc > threshold
        xc = yc @ (qc[:, keepc] / np.sqrt(wc[keepc]))
        chat_direct = xc @ xc.T
        eig_c = np.maximum(eigh(c, eigvals_only=True), 0)
        budget = alpha * np.log1p(tau)
        residual = eigh(c - chat, eigvals_only=True)
        metrics = []
        for mu in [0.01, 0.1, 0.5, 1.0]:
            deff = float(np.sum(eig_c / (eig_c + mu)))
            assert mu * deff <= budget + 1e-9
            metrics.append({"mu": mu, "effective_dimension": deff,
                            "mu_times_effective_dimension": mu * deff})
        identity_error = float(np.linalg.norm(chat - chat_direct, 2))
        assert identity_error < 1e-6
        assert residual[0] > -1e-8
        out.append({"log_condition_A": 2 * spread, "n": n,
                    "factor_width": int(np.sum(keep)),
                    "raw_whitened_identity_error": identity_error,
                    "minimum_residual_eigenvalue": float(residual[0]),
                    "relative_residual_norm": float(residual[-1]),
                    "budget": float(budget),
                    "computed_logdet_budget": float(np.sum(np.log1p(eig_c))),
                    "ridge_dimension_checks": metrics})
    destination = Path(__file__).with_name("balanced-checks.json")
    destination.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
