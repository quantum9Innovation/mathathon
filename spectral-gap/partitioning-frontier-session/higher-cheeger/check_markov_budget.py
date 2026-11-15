"""Dense corroboration only; no timing or nearly-linear implementation claim."""
from pathlib import Path
import json
import math
import numpy as np
from scipy.linalg import null_space

ROOT = Path(__file__).resolve().parent
rng = np.random.default_rng(20261115)


def matrices(adj):
    deg = adj.sum(axis=1)
    d = np.diag(deg)
    lap = d - adj
    norm = lap / np.sqrt(deg[:, None] * deg[None, :])
    return deg, d, lap, norm


def markov(adj, alpha):
    deg, d, lap, norm = matrices(adj)
    vals, vecs = np.linalg.eigh(norm)
    assert vals[1] > 1e-8
    vals[0] = 0.0
    h = np.sqrt(deg[:, None] * deg[None, :]) * (
        (vecs * vals**alpha) @ vecs.T
    )
    return h, deg, lap


cases = []
for n in (3, 4, 7, 12):
    for rep in range(3):
        adj = np.zeros((n, n))
        for i in range(n - 1):
            adj[i, i + 1] = adj[i + 1, i] = 10**rng.uniform(-1, 1)
        for i in range(n):
            for j in range(i + 2, n):
                if rng.random() < 0.25:
                    adj[i, j] = adj[j, i] = 10**rng.uniform(-1, 1)
        u, v = rng.choice(n, 2, replace=False)
        weight = 10**rng.uniform(-1, 1)
        changed = adj.copy()
        changed[u, v] += weight
        changed[v, u] += weight
        quotient = null_space(np.ones((1, n)))
        for alpha in (0.15, 0.5, 0.85):
            h, deg, lap = markov(adj, alpha)
            hp, _, _ = markov(changed, alpha)
            hq = quotient.T @ h @ quotient
            dhq = quotient.T @ (hp - h) @ quotient
            eig, vec = np.linalg.eigh(hq)
            invroot = (vec * eig**-0.5) @ vec.T
            response = invroot @ dhq @ invroot
            ev = np.linalg.eigvalsh(response)
            b = np.eye(n)[u] - np.eye(n)[v]
            resistance = b @ np.linalg.pinv(lap, hermitian=True) @ b
            tau = weight * resistance
            budget = alpha * math.log1p(tau) + (1 - alpha) * (
                math.log1p(weight / deg[u])
                + math.log1p(weight / deg[v])
                - math.log1p(2 * weight / deg.sum())
            )
            actual = np.log1p(ev).sum()
            tree_log = np.linalg.slogdet(lap[:-1, :-1])[1]
            pdet_log = np.linalg.slogdet(hq)[1]
            predicted = math.log(n) + alpha * tree_log + (1 - alpha) * (
                np.log(deg).sum() - math.log(deg.sum())
            )
            assert ev[0] > -2e-10
            assert abs(actual - budget) < 2e-9
            assert abs(pdet_log - predicted) < 2e-9
            assert budget <= (2 - alpha) * math.log1p(tau) + 1e-12
            for eps in (0.01, 0.1, 0.5):
                assert (ev > eps).sum() * math.log1p(eps) < budget + 1e-11
            cases.append({
                "n": n, "alpha": alpha, "tau": float(tau),
                "budget": float(budget), "logdet_error": float(abs(actual-budget)),
                "pdet_error": float(abs(pdet_log-predicted)),
                "response_min_eigenvalue": float(ev[0]),
            })


def conductance(adj, subset):
    mask = np.zeros(len(adj), dtype=bool)
    mask[list(subset)] = True
    return adj[np.ix_(mask, ~mask)].sum() / adj[mask].sum()


local_cases = []
for eta in (0.5, 0.1, 0.001):
    # Vertex order u, a, s, r, q, p, b, v.
    adj = np.zeros((8, 8))
    for i, weight in enumerate((1, eta, 1, eta, 1, eta, 1)):
        adj[i, i + 1] = adj[i + 1, i] = weight
    old_phi = max(conductance(adj, s) for s in ({0, 1}, {6, 7}, {2, 3, 4, 5}))
    changed = adj.copy()
    changed[0, 7] = changed[7, 0] = 1
    uverts = (0, 1, 6, 7)
    sets = [set(uverts[i] for i in range(4) if bits & (1 << i))
            for bits in range(1, 16)]
    local_best = min(max(conductance(changed, a), conductance(changed, b))
                     for a in sets for b in sets if not a & b)
    new_phi = max(conductance(changed, s) for s in (set(uverts), {4, 5}, {2, 3}))
    eig = np.linalg.eigvalsh(matrices(changed)[3])
    assert abs(old_phi - eta/(2+eta)) < 1e-12
    assert local_best >= 1/3 - 1e-12
    assert abs(local_best - (1+eta)/(3+eta)) < 1e-12
    assert new_phi <= eta/(1+eta) + 1e-12
    assert eig[2] <= 2*eta/(1+eta) + 1e-12
    local_cases.append({"eta": eta, "old_max_conductance": old_phi,
                        "new_global_max_conductance": new_phi,
                        "best_two_disjoint_sets_in_U": local_best,
                        "new_lambda3": float(eig[2])})

report = {"status": "PASS", "scope": "dense corroboration only",
          "budget_cases": cases, "locality_cases": local_cases}
(ROOT / "diagnostics.json").write_text(json.dumps(report, indent=2) + "\n")
print(f"PASS: {len(cases)} degree-aware budgets and {len(local_cases)} exhaustive locality cases")
