#!/usr/bin/env python3
"""Reproduce the two unit-mass graph obstructions and soft identities.

Run: uv run --with numpy --with scipy python check_partitioning.py
All generated output stays beside this file. Numerical checks supplement,
and do not replace, the proofs in the session notes.
"""
from pathlib import Path
import json
import numpy as np
from scipy.linalg import eigh, null_space
from scipy.optimize import brentq

HERE = Path(__file__).resolve().parent


def graph_embedding(n=65, gamma=1/32):
    r = n - 1
    delta = 1/(2*n)
    b = np.eye(n)[:, 0] - np.eye(n)[:, 1]
    base = null_space(np.ones((1, n)))
    target = np.full(r, np.sqrt(2/r))
    old = base.T @ b
    v = old - target
    house = np.eye(r) - 2*np.outer(v, v)/(v @ v)
    U = base @ house
    H = (U * (np.arange(1, r+1)/r)) @ U.T
    L = np.eye(n) - np.ones((n, n))/n + delta*H
    off = L.copy()
    np.fill_diagonal(off, -np.inf)
    assert np.max(off) <= -1/(2*n) + 1e-12
    assert np.linalg.norm(L @ np.ones(n)) < 1e-11
    assert np.linalg.norm(U.T @ b - target) < 1e-12
    d = gamma*delta/2
    B = L + d*np.outer(b, b)
    vals, vecs = eigh(L)
    tau = d*np.sum((vecs[:, 1:].T @ b)**2/vals[1:])
    k = r//2
    cut = 1 + delta/r*(k+0.5)
    vals2, vecs2 = eigh(B)
    P = vecs[:, 1:k+1] @ vecs[:, 1:k+1].T
    Q = vecs2[:, 1:k+1] @ vecs2[:, 1:k+1].T
    assert vals2[k] < cut < vals[k+1]
    return {"n": n, "tau": float(tau), "edge_increment": d,
            "largest_offdiagonal": float(np.max(off)),
            "projector_HS_squared": float(np.sum((P-Q)**2))}


def cauchy_obstruction(r, gamma=1/32):
    # Work at the exact scaled spectral level, avoiding tiny-gap cancellation.
    inds = np.arange(1, r+1, dtype=float)
    nu = np.empty(r)
    for j in range(1, r+1):
        def secular(theta):
            return 1 + gamma*np.sum(1/(inds-j-theta))
        hi = 1-1e-12 if j < r else max(1., 2*gamma*r)
        theta = brentq(secular, 1e-12, hi, xtol=1e-14)
        nu[j-1] = j + theta
    raw = 1/(inds[:, None] - nu[None, :])
    norm = 1/np.linalg.norm(raw, axis=0)
    V = raw*norm
    assert np.linalg.norm(V.T @ V - np.eye(r), ord=np.inf) < 1e-7
    bulk = slice(r//4, 3*r//4)
    shifts = nu - inds
    if gamma <= 1/32:
        assert np.min(shifts[bulk]) >= gamma/2 - 1e-10
        assert np.max(shifts[bulk]) <= 2*gamma + 1e-10
    else:
        assert np.min(shifts[bulk]) >= 1/64 - 1e-10
        assert np.max(shifts[bulk]) <= 63/64 + 1e-10
    k = r//2
    cross = V[:k, k:]
    hs = 2*np.sum(cross**2)
    lower = (gamma**2/16 if gamma <= 1/32 else 1/20000)*np.log(1+r//16)
    assert hs >= lower
    n = r+1
    delta = 1/(2*n)
    ll = np.log1p(delta*inds/r)
    lm = np.log1p(delta*nu/r)
    integrated = np.sum(V**2*np.abs(ll[:, None]-lm[None, :]))
    tau = gamma*delta*np.mean(1/(1+delta*inds/r))
    logdet = np.log1p(tau)
    # Exact trace/soft integral budget, from the signed spectral overlap sum.
    signed = np.sum(V**2*(lm[None, :]-ll[:, None]))
    assert abs(signed-logdet) < 1e-11
    if gamma <= 1/32:
        integrated_lower = delta*gamma**2/128*np.log(1+r//16)
        assert integrated >= integrated_lower
    cross_singulars = np.linalg.svd(cross, compute_uv=False)
    return {"r": r, "tau": float(tau), "projector_HS_squared": float(hs),
            "HS_lower_bound": float(lower),
            "integrated_hard_motion": float(integrated),
            "logdet_budget": float(logdet),
            "hard_motion_over_budget": float(integrated/logdet),
            "singulars_cross_above_gamma_over_20": int(np.sum(
                cross_singulars >= gamma/20)),
            "singulars_cross_above_one_over_600": int(np.sum(
                cross_singulars >= 1/600)),
            "minimum_bulk_shift": float(np.min(shifts[bulk])),
            "maximum_bulk_shift": float(np.max(shifts[bulk]))}


def path_laplacian(r):
    T = np.zeros((r, r))
    for i in range(r-1):
        T[i, i] += 1
        T[i+1, i+1] += 1
        T[i, i+1] -= 1
        T[i+1, i] -= 1
    return T


def balanced_switch(r):
    n = 4*r
    delta = 1/n
    K = np.zeros((4, 4))
    for p, q, w in [(0, 1, (1+delta)/2), (2, 3, (1+delta)/2),
                     (0, 2, 1/2), (1, 3, 1/2)]:
        K[p, p] += w
        K[q, q] += w
        K[p, q] -= w
        K[q, p] -= w
    M = n*r*r
    # Multiply the whole graph by 2, so the edited edge is a unit edge.
    L = 2*(np.kron(K, np.eye(r)) + M*np.kron(np.eye(4), path_laplacian(r)))
    b = np.eye(n)[:, 0] - np.eye(n)[:, 2*r]
    B = L + np.outer(b, b)
    x = np.repeat([1, 1, -1, -1], r)/np.sqrt(n)
    y = np.repeat([1, -1, 1, -1], r)/np.sqrt(n)
    vals, vecs = eigh(L)
    vals2, vecs2 = eigh(B)
    tau = np.sum((vecs[:, 1:].T @ b)**2/vals[1:])
    assert abs(abs(vecs[:, 1] @ x)-1) < 1e-8
    assert abs(abs(vecs2[:, 1] @ y)-1) < 1e-8
    assert tau <= 4/n
    moved = min(np.sum(np.sign(x) != np.sign(y)),
                np.sum(np.sign(x) != -np.sign(y)))
    off = L.copy()
    np.fill_diagonal(off, 0)
    degrees = np.sum(off < -1e-8, axis=1)
    assert np.max(degrees) <= 4
    assert np.isclose(-L[0, 2*r], 1)
    assert moved == n//2
    for alpha in [0.25, 0.5, 0.75]:
        Ua = vecs[:, 1:]
        va = vals[1:]
        Vb = vecs2[:, 1:]
        vb = vals2[1:]
        inv = (Ua * va**(-alpha/2)) @ Ua.T
        power_a = (Ua * va**alpha) @ Ua.T
        power_b = (Vb * vb**alpha) @ Vb.T
        C = inv @ (power_b-power_a) @ inv
        eig = np.linalg.eigvalsh(Ua.T @ C @ Ua)
        assert eig.min() > -1e-8
        assert eig.max() <= (1+tau)**alpha-1+1e-8
        assert abs(np.sum(np.log1p(eig))-alpha*np.log1p(tau)) < 1e-7
    result = {"n": n, "tau": float(tau), "maximum_degree": int(degrees.max()),
              "moved_vertices": int(moved), "old_fiedler": float(vals[1]),
              "new_fiedler": float(vals2[1]), "new_lambda3": float(vals2[2]),
              "cut_x_old": float(n/4*(x @ L @ x)),
              "cut_y_old": float(n/4*(y @ L @ y)),
              "cut_x_new": float(n/4*(x @ B @ x)),
              "cut_y_new": float(n/4*(y @ B @ y))}
    if n <= 16:
        from itertools import combinations
        costs = []
        for subset in combinations(range(1, n), n//2-1):
            idx = (0,)+subset  # remove the complement symmetry
            signs = -np.ones(n)
            signs[list(idx)] = 1
            costs.append((float(signs @ L @ signs/4),
                          float(signs @ B @ signs/4), idx))
        old = sorted(costs, key=lambda row: row[0])
        new = sorted(costs, key=lambda row: row[1])
        assert old[0][2] != new[0][2]
        assert old[1][0] > old[0][0] + 1e-6
        assert new[1][1] > new[0][1] + 1e-6
        result["enumerated_unique_optima"] = True
    return result


if __name__ == "__main__":
    tau_star = 0.001
    fixed_tau = []
    for r in [64, 128, 256, 512]:
        delta = 1/(2*(r+1))
        a_r = np.mean(1/(1+delta*np.arange(1, r+1)/r))
        row = cauchy_obstruction(r, gamma=tau_star/(delta*a_r))
        assert abs(row["tau"]-tau_star) < 1e-14
        fixed_tau.append(row)
    results = {"embedding": graph_embedding(),
               "balanced_switch": [balanced_switch(r) for r in [2, 3, 4, 8, 16]],
               "cauchy_projectors": [cauchy_obstruction(r) for r in [64, 128, 256, 512]],
               "fixed_leverage_projectors": fixed_tau}
    path = HERE/"partitioning-checks.json"
    path.write_text(json.dumps(results, indent=2)+"\n")
    print(json.dumps(results, indent=2))
