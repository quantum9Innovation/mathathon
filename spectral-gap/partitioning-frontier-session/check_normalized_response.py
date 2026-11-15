#!/usr/bin/env python3
"""Dense corroboration of identities; no nearly-linear implementation claims."""
import json
import math
from pathlib import Path

import numpy as np


def laplacian(n, edges):
    L = np.zeros((n, n))
    for u, v, w in edges:
        b = np.eye(n)[u] - np.eye(n)[v]
        L += w * np.outer(b, b)
    return L


def form(L, alpha):
    d = np.diag(L)
    sd = np.sqrt(d)
    N = L / sd[:, None] / sd[None, :]
    vals, vecs = np.linalg.eigh(N)
    vals[0] = 0.0
    assert vals[1] > 0
    vals = np.maximum(vals, 0.0)
    return sd[:, None] * ((vecs * vals**alpha) @ vecs.T) * sd[None, :]


def basis(n):
    return np.linalg.qr(np.column_stack((np.ones(n), np.eye(n)[:, 1:])))[0][:, 1:]


def F(L, D, t):
    return D - t * D @ np.linalg.solve(L + t * D, D)


def factor_response(L, D, t, u, v, delta):
    n = len(L)
    eu, ev = np.eye(n)[u], np.eye(n)[v]
    b = eu - ev
    K = L + t * D
    Kinvb = np.linalg.solve(K, b)
    Kinve = np.linalg.solve(K, np.column_stack((eu, ev)))
    G = math.sqrt(delta) * np.column_stack((math.sqrt(t) * D @ Kinvb, L @ Kinve))
    V = math.sqrt(delta) * np.column_stack((b, -math.sqrt(t) * eu, -math.sqrt(t) * ev))
    M = np.eye(3) + V.T @ np.linalg.solve(K, V)
    return G @ np.linalg.solve(M, G.T)


def main():
    rng = np.random.default_rng(20261115)
    records = []
    for n in (4, 6, 9):
        for case in range(3):
            edges = [(j, j + 1, float(rng.uniform(0.4, 2))) for j in range(n - 1)]
            for u in range(n):
                for v in range(u + 2, n):
                    if rng.random() < 0.25:
                        edges.append((u, v, float(rng.uniform(0.4, 2))))
            L = laplacian(n, edges)
            D = np.diag(np.diag(L))
            u, v = rng.choice(n, 2, replace=False)
            eu, ev = np.eye(n)[u], np.eye(n)[v]
            b = eu - ev
            delta = float(rng.uniform(0.2, 2))
            Lp = L + delta * np.outer(b, b)
            Dp = D + delta * (np.outer(eu, eu) + np.outer(ev, ev))
            Q = basis(n)
            R = float(b @ np.linalg.pinv(L) @ b)
            max_factor_err = 0.0
            for t in (0.01, 0.1, 1, 10, 100):
                exact = F(Lp, Dp, t) - F(L, D, t)
                got = factor_response(L, D, t, u, v, delta)
                err = float(np.linalg.norm(exact - got, 2))
                max_factor_err = max(max_factor_err, err)
                assert err < 2e-11
                assert np.linalg.eigvalsh(exact)[0] > -2e-11
                assert np.linalg.norm(got @ np.ones(n)) < 1e-10
            for alpha in (0.25, 0.5, 0.8):
                H = form(L, alpha)
                Hp = form(Lp, alpha)
                Hq = Q.T @ H @ Q
                Hpq = Q.T @ Hp @ Q
                eigs, evecs = np.linalg.eigh(Hq)
                invsqrt = (evecs * eigs**-0.5) @ evecs.T
                C = invsqrt @ (Hpq - Hq) @ invsqrt
                actual_budget = np.linalg.slogdet(Hpq)[1] - np.linalg.slogdet(Hq)[1]
                expected_budget = alpha * math.log1p(delta * R) + (1 - alpha) * (
                    math.log1p(delta / D[u, u]) + math.log1p(delta / D[v, v])
                    - math.log1p(2 * delta / np.trace(D)))
                budget_err = abs(actual_budget - expected_budget)
                assert budget_err < 2e-11
                assert np.linalg.eigvalsh(C)[0] > -2e-11
                pdet_formula = alpha * np.linalg.slogdet(Q.T @ L @ Q)[1] + (1 - alpha) * (
                    math.log(n) + np.log(np.diag(D)).sum() - math.log(np.trace(D)))
                assert abs(np.linalg.slogdet(Hq)[1] - pdet_formula) < 2e-11
                records.append(dict(n=n, case=case, alpha=alpha, budget=actual_budget,
                                    budget_error=budget_err, factor_error=max_factor_err))

    path_records = []
    x = np.array([1., 1., -1., -1.])
    for alpha in (0.25, 0.5, 0.8):
        target = (4 / 3)**(1 - alpha) - 1
        for h in (1e-2, 1e-4, 1e-6, 1e-8):
            L = laplacian(4, [(0, 1, 1), (1, 2, h), (2, 3, 1)])
            Lp = laplacian(4, [(0, 1, 2), (1, 2, h), (2, 3, 1)])
            H, Hp = form(L, alpha), form(Lp, alpha)
            den = float(x @ H @ x)
            relative = float(x @ (Hp - H) @ x / den)
            baseline = den / (4 * h**alpha)
            # Bound is analytic; reporting it does not numerically integrate a delicate tail.
            cutoff = 0.1
            upper = 8 * math.sin(math.pi * alpha) / (math.pi * (2 - alpha)) * h*h * cutoff**(alpha - 2)
            path_records.append(dict(alpha=alpha, h=h, relative_response=relative,
                                     target=target, baseline_ratio=baseline,
                                     retained_relative_upper_bound=upper/den))
            if h == 1e-8:
                assert abs(relative - target) < 5e-6
                assert abs(baseline - 1) < 5e-6

    output = dict(status="PASS", identity_cases=records, four_vertex_cases=path_records,
                  scope="Dense double-precision corroboration, not a proof or fast solver benchmark.")
    destination = Path(__file__).with_name("normalized-response-checks.json")
    destination.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(dict(status=output["status"], identity_cases=len(records),
                          factor_cases=9*5, four_vertex_cases=len(path_records),
                          output=str(destination))))


if __name__ == "__main__":
    main()
