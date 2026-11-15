"""Independent diagnostics for the exact rank-two weighted-path obstruction.

Analytic proof is in spectral-gap/exact-path-rank-two-independent-review.txt.
These floating-point checks corroborate formulas, not the proof or novelty.
"""

import json
import math

import numpy as np


def power(a, exponent):
    values, vectors = np.linalg.eigh(a)
    assert values.min() > 0
    return (vectors * values**exponent) @ vectors.T


def relative_root(a, u):
    inverse_quarter = power(a, -0.25)
    return inverse_quarter @ power(a + np.outer(u, u), 0.5) @ inverse_quarter


def trace_formula(r, tau, determinant_factor):
    k = math.sqrt(1 + tau)
    c = 2 / math.sqrt(determinant_factor)
    z = math.sqrt(r)
    numerator = c * k * z * z + (k + 1) * z + c
    denominator = (c * z * z + 2 * z + c) * (
        c * k * k * z * z + 2 * k * z + c
    )
    return (k + 1) * numerator / math.sqrt(denominator)


def trace_minimum(tau, kappa):
    k = math.sqrt(1 + tau)
    f = k + 1 + 2 * math.sqrt((1 + kappa) * k)
    return (k + 1) / math.sqrt(1 + kappa * (k - 1)**2 / f**2)


def laplacian(weights):
    n = len(weights) + 1
    result = np.zeros((n, n))
    for i, weight in enumerate(weights):
        incidence = np.zeros(n)
        incidence[i] = 1
        incidence[i + 1] = -1
        result += weight * np.outer(incidence, incidence)
    return result


def main():
    rng = np.random.default_rng(2026111507)
    maximum_trace_error = 0.0
    minimum_slack = float("inf")
    cases = 0
    for tau in (0.1, 0.5, 1.0, 2.0, 9.0):
        k = math.sqrt(1 + tau)
        ratios = [math.exp(x) for x in np.linspace(-5, 5, 51)]
        ratios += [1 / k]
        ratios += list(np.exp(rng.uniform(-5, 5, 40)))
        for r in ratios:
            # Three vertices, left edited conductance r and right weight 1.
            l3 = laplacian([r, 1.0])
            basis, _ = np.linalg.qr(np.array([[1., 0.], [0., 1.], [-1., -1.]]))
            a3 = basis.T @ l3 @ basis
            u3 = math.sqrt(tau * r) * basis.T @ np.array([1., -1., 0.])
            # Four vertices, equal outer conductances 1 and edited middle r.
            a4 = np.array([[1., -1.], [-1., 1. + 2. * r]])
            u4 = np.array([0., math.sqrt(2. * tau * r)])
            for a, u, determinant_factor, kappa in (
                (a3, u3, 3., 1 / 3), (a4, u4, 2., 1.),
            ):
                computed = float(np.trace(relative_root(a, u)))
                analytic = trace_formula(r, tau, determinant_factor)
                maximum_trace_error = max(maximum_trace_error, abs(computed - analytic))
                minimum_slack = min(minimum_slack, analytic - trace_minimum(tau, kappa))
                assert abs(computed - analytic) < 2e-10
                assert analytic >= trace_minimum(tau, kappa) - 2e-14
                cases += 1

    k = math.sqrt(2)
    minimum = trace_minimum(1., 1.)
    q2_max = (minimum - math.sqrt(minimum**2 - 4 * k)) / 2
    q1_at_minimum = minimum - q2_max
    target = np.array([5 / 4, 4 * k / 5])
    # An exact radical solution in the proof, evaluated stably here.
    coefficient = 378 + 252 * k
    x = (coefficient + math.sqrt(coefficient**2 + 44 * (800 + 504 * k))) / 22
    square_root_delta = 2 / (x + math.sqrt(x*x - 4))
    delta = square_root_delta**2
    witness = np.diag([delta, 1.])
    update = np.array([math.sqrt(delta / 2), 1 / math.sqrt(2)])
    actual = np.linalg.eigvalsh(relative_root(witness, update))[::-1]
    assert np.max(np.abs(actual - target)) < 2e-12
    assert target.sum() < 12 / 5 < minimum

    print(json.dumps({
        "seed": 2026111507,
        "formula_cases": cases,
        "maximum_trace_error": maximum_trace_error,
        "minimum_slack": minimum_slack,
        "alpha": 0.5,
        "tau": 1,
        "path_minimum_trace": minimum,
        "path_q1_at_minimum": q1_at_minimum,
        "path_maximum_q2": q2_max,
        "forbidden_target_q": target.tolist(),
        "target_trace": float(target.sum()),
        "trace_gap": minimum - float(target.sum()),
        "matrix_witness_delta": delta,
        "matrix_witness_actual_q": actual.tolist(),
        "scope": "floating-point diagnostics; analytic proof is separate",
    }, indent=2))


if __name__ == "__main__":
    main()
