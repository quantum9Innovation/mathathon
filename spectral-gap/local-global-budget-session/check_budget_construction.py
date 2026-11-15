"""Independent finite-circuit checks for the proposed sharp bridge coefficient.

The circuit calculation is exact up to floating-point error.  Fractional
mass separation is checked at moderate scales, where roundoff is tolerable.
This is a sanity check, not a substitute for the proofs in the session.
"""
import json
from pathlib import Path

import numpy as np
from scipy.linalg import eigh


def flat_necks(m, budget, degree=3):
    c = (degree - 2) / degree
    cp = 2 * (degree - 2) / (degree + 2)
    f0 = cp / c
    g = [0.0]
    for j in range(1, m + 1):
        f = f0 * np.exp(-budget * j / m)
        g.append((cp - f * c) / (f - 1))
    return 1 / np.diff(g)


def tree_spec(m):
    """Bottom-tree edge currents are sums of the descendant terminal currents."""
    rows = []

    def branch(indices):
        if len(indices) == 1:
            return
        cut = len(indices) // 2
        for child in (indices[:cut], indices[cut:]):
            row = np.zeros(m)
            row[child] = 1
            rows.append(row)
            branch(child)

    branch(list(range(m)))
    return sum((np.outer(row, row) for row in rows), np.zeros((m, m)))


def circuit(m, q, lengths, bridge_r, degree=3):
    # Boundary vertex 0 is the anchor, 1,...,m are the terminal means.
    edges, next_vertex = [], m + 1
    branching = degree - 1

    def vertex():
        nonlocal next_vertex
        v = next_vertex
        next_vertex += 1
        return v

    def fanout(root, count, callback):
        if count == 1:
            callback(root)
            return
        for _ in range(branching):
            child = vertex()
            edges.append((root, child, 1.0))
            fanout(child, count // branching, callback)

    def bottom(root, indices):
        if len(indices) == 1:
            i = indices[0]
            edges.append((root, i + 1, 1 / lengths[i]))
            return
        cut = len(indices) // 2
        for child_indices in (indices[:cut], indices[cut:]):
            child = vertex()
            edges.append((root, child, 1.0))
            bottom(child, child_indices)

    left, right = vertex(), vertex()
    edges.append((left, right, 1 / bridge_r))
    fanout(left, q, lambda root: bottom(root, list(range(m))))
    # Identify the Q leaves of the second fanout with anchor ports.
    def anchor_fanout(root, count):
        if count == 1:
            return root
        for _ in range(branching):
            if count == branching:
                edges.append((root, 0, 1.0))
            else:
                child = vertex()
                edges.append((root, child, 1.0))
                anchor_fanout(child, count // branching)

    if q == 1:
        raise ValueError("Use q >= 2 for the finite-circuit check")
    anchor_fanout(right, q)
    lap = np.zeros((next_vertex, next_vertex))
    for u, v, conductance in edges:
        lap[u, u] += conductance
        lap[v, v] += conductance
        lap[u, v] -= conductance
        lap[v, u] -= conductance
    grounded = lap[1:, 1:]
    terminal = grounded[:m, :m]
    cross = grounded[:m, m:]
    interior = grounded[m:, m:]
    return terminal - cross @ np.linalg.solve(interior, cross.T)


def reverse_log_pivots(k, kp):
    out = []
    for i in range(len(k)):
        log_ratio = np.linalg.slogdet(kp[i:, i:])[1] - np.linalg.slogdet(k[i:, i:])[1]
        if i + 1 == len(k):
            next_log_ratio = 0.0
        else:
            next_log_ratio = np.linalg.slogdet(kp[i + 1:, i + 1:])[1] - np.linalg.slogdet(k[i + 1:, i + 1:])[1]
        out.append(log_ratio - next_log_ratio)
    return np.array(out)


def fractional_response(k, kp, delta, alpha):
    m = len(k)
    d = np.diag(delta ** (np.arange(m - 1, -1, -1) / 2))
    a, b = d @ k @ d, d @ kp @ d
    w, v = eigh(a)
    z, u = eigh(b)
    apow = (v * w**alpha) @ v.T
    bpow = (u * z**alpha) @ u.T
    inverse = (v * w ** (-alpha / 2)) @ v.T
    return eigh(inverse @ (bpow - apow) @ inverse, eigvals_only=True)


def main():
    results = []
    for degree in (3, 4, 5):
        budget = 0.9 * np.log(2 * degree / (degree + 2))
        access = 2 / (degree - 2)
        for m in (1, 3, 5):
            t = flat_necks(m, budget, degree)
            k = np.linalg.inv(np.diag(t) + (1 + access) * np.ones((m, m)))
            kp = np.linalg.inv(np.diag(t) + (0.5 + access) * np.ones((m, m)))
            pivot_error = np.max(np.abs(reverse_log_pivots(k, kp) - budget / m))
            for q in (degree - 1, (degree - 1) ** 2):
                lengths = np.ceil(q * t)
                for bridge_r in (1, 0.5):
                    actual = circuit(m, q, lengths, bridge_r, degree)
                    impedance = np.diag(lengths / q) + (bridge_r + access * (1 - 1 / q)) * np.ones((m, m)) + tree_spec(m) / q
                    impedance_error = np.max(np.abs(np.linalg.inv(actual) - impedance))
                    assert impedance_error < 1e-9
                    results.append(dict(degree=degree, m=m, q=q, bridge_r=bridge_r, impedance_error=float(impedance_error), pivot_error=float(pivot_error)))
            assert pivot_error < 1e-12
    m, alpha = 3, 0.5
    budget = 0.9 * np.log(6 / 5)
    t = flat_necks(m, budget)
    k = np.linalg.inv(np.diag(t) + 3 * np.ones((m, m)))
    kp = np.linalg.inv(np.diag(t) + 2.5 * np.ones((m, m)))
    target = np.expm1(alpha * budget / m)
    mass_checks = []
    for delta in (0.1, 0.01, 0.001):
        spectrum = fractional_response(k, kp, delta, alpha)
        mass_checks.append(dict(delta=delta, spectrum=spectrum.tolist(), target=float(target), max_error=float(np.max(abs(spectrum - target)))))
    assert mass_checks[-1]["max_error"] < mass_checks[0]["max_error"]
    report = dict(budget=float(budget), circuit_checks=results, mass_checks=mass_checks)
    Path(__file__).with_name("construction-checks.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(dict(circuit_cases=len(results), max_impedance_error=max(x["impedance_error"] for x in results), max_pivot_error=max(x["pivot_error"] for x in results), mass_checks=mass_checks), indent=2))


if __name__ == "__main__":
    main()
