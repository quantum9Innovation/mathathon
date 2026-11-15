"""Numerical falsification checks for the relative fractional response theorem.

The proof is in spectral-gap/relative-fractional-response.tex.  These checks
compare two independent evaluations on moderately conditioned inputs and use
the resolvent integral on examples too ill-conditioned for a dense power.
They are diagnostics, not a proof or a finite-precision algorithm theorem.
"""

import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad_vec
from scipy.special import logsumexp


def response_integral(log_a, z, alpha):
    """Relative correction for diagonal A, u_i^2=a_i*z_i, via log(t)."""
    n = len(z)
    log_z = np.full(n, -np.inf)
    active = z > 0
    log_z[active] = np.log(z[active])
    log_u = (1 - alpha) * log_a / 2 + log_z / 2

    def integrand(s):
        log_at = np.logaddexp(log_a, s)
        log_denom = logsumexp(np.r_[0.0, log_a + log_z - log_at])
        v = log_u - log_at
        return (np.sin(np.pi * alpha) / np.pi) * np.exp(
            (alpha + 1) * s + v[:, None] + v[None, :] - log_denom
        )

    margin = 42 / min(alpha, 1 - alpha)
    # Splitting at each scale avoids missing narrow features on a huge interval.
    breaks = np.r_[min(log_a) - margin, np.sort(log_a), max(log_a) + margin]
    answer = np.zeros((n, n))
    error = 0.0
    for left, right in zip(breaks[:-1], breaks[1:]):
        if left == right:
            continue
        value, estimate = quad_vec(integrand, left, right, epsabs=1e-11, epsrel=1e-11)
        answer += value
        error += float(estimate)
    return answer, error


def construction(q, alpha, delta):
    r = np.asarray(q) ** (1 / alpha)
    suffix = np.r_[np.cumprod(r[:0:-1])[::-1], 1.0]
    z = (r - 1) * suffix
    log_a = np.arange(len(q) - 1, -1, -1) * np.log(delta)
    return log_a, z


def dense_response(log_a, z, alpha):
    a = np.exp(log_a)
    u = np.sqrt(a * z)
    vals, vecs = np.linalg.eigh(np.diag(a) + np.outer(u, u))
    power = (vecs * vals**alpha) @ vecs.T
    scale = a ** (-alpha / 2)
    return (scale[:, None] * power) * scale[None, :] - np.eye(len(a))


def main():
    rng = np.random.default_rng(2026111507)
    comparisons = []
    for alpha in (0.2, 0.5, 0.8):
        for n in range(1, 7):
            for _ in range(3):
                log_a = rng.uniform(-3, 3, n)
                z = rng.uniform(0, 2, n)
                integral, err = response_integral(log_a, z, alpha)
                dense = dense_response(log_a, z, alpha)
                diff = float(np.linalg.norm(integral - dense, 2))
                determinant = float(np.linalg.slogdet(np.eye(n) + integral)[1])
                exact_logdet = float(alpha * np.log1p(sum(z)))
                comparisons.append((diff, abs(determinant - exact_logdet), err))
                assert diff < 2e-9
                assert abs(determinant - exact_logdet) < 2e-9
                assert np.linalg.eigvalsh(integral)[0] > -2e-10

    limits = []
    # Include nonuniform, reordered, and inactive coordinates; the target
    # spectrum is not just an equal-eigenvalue special case.
    targets = ([1.3], [1.5, 1.1], [1.05, 1.4, 1.0, 1.2], [1.15] * 6)
    for alpha in (0.25, 0.5, 0.75):
        for q in targets:
            rows = []
            for delta in (0.1, 0.001, 1e-8, 1e-20, 1e-40):
                log_a, z = construction(q, alpha, delta)
                correction, quadrature_error = response_integral(log_a, z, alpha)
                eigs = np.linalg.eigvalsh(np.eye(len(q)) + correction)
                distance = float(np.linalg.norm(correction - np.diag(np.array(q) - 1), 2))
                logdet_error = abs(float(np.linalg.slogdet(np.eye(len(q)) + correction)[1]) - sum(np.log(q)))
                assert logdet_error < 3e-9
                rows.append({"delta": delta, "spectrum": eigs.tolist(), "distance_to_target_matrix": distance,
                             "logdet_error": logdet_error, "quadrature_estimate": quadrature_error})
            assert rows[-1]["distance_to_target_matrix"] < 2e-4
            limits.append({"alpha": alpha, "target": q, "rows": rows})

    counts = []
    for n in (1, 2, 5, 12):
        alpha, tau = 0.5, 3.0
        q_target = (1 + tau) ** (alpha / n)
        epsilon = 0.9 * (q_target - 1)
        log_a, z = construction([q_target] * n, alpha, 1e-20)
        correction, _ = response_integral(log_a, z, alpha)
        count = int(np.sum(np.linalg.eigvalsh(correction) > epsilon))
        assert count == n
        counts.append({"n": n, "leverage": float(sum(z)), "epsilon": epsilon, "count": count})

    record = {"seed": 2026111507, "dense_integral_comparisons": len(comparisons),
              "max_dense_discrepancy": max(x[0] for x in comparisons),
              "max_logdet_discrepancy": max(x[1] for x in comparisons),
              "closure_examples": limits, "rank_count_examples": counts,
              "scope": "Floating-point diagnostics; no interval certificate, proof, or novelty claim."}
    destination = Path(__file__).resolve().parents[1] / "spectral-gap" / "relative-fractional-response-checks.json"
    destination.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({key: record[key] for key in ("dense_integral_comparisons", "max_dense_discrepancy",
                                                   "max_logdet_discrepancy")}))
    print(f"PASS: {len(limits)} closure families, {len(counts)} count examples; {destination}")


if __name__ == "__main__":
    main()
