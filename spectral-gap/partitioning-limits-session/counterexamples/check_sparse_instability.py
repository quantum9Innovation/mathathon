#!/usr/bin/env python3
"""Dense corroboration of the written exact proof; not the proof itself."""
import json
from pathlib import Path

import numpy as np


def check(m):
    n = 4 * m
    a = 4 * m / (4 * m + 1)
    big = 2 * m**3
    vertices = [(s, t, j) for s in (-1, 1) for t in (-1, 1) for j in range(m)]
    index = {v: i for i, v in enumerate(vertices)}
    lap = np.zeros((n, n))

    def add_edge(u, v, weight):
        i, k = index[u], index[v]
        lap[i, i] += weight
        lap[k, k] += weight
        lap[i, k] -= weight
        lap[k, i] -= weight

    for s, t, j in vertices:
        if s == -1:
            add_edge((s, t, j), (-s, t, j), a)
        if t == -1:
            add_edge((s, t, j), (s, -t, j), 1)
        if j + 1 < m:
            add_edge((s, t, j), (s, t, j + 1), big)
    x = np.array([s for s, _, _ in vertices]) / np.sqrt(n)
    y = np.array([t for _, t, _ in vertices]) / np.sqrt(n)
    r = np.zeros(n)
    r[index[(1, 1, m // 2)]] = 1
    r[index[(-1, 1, m // 2)]] = -1
    edited = lap + a * np.outer(r, r)
    vals, vecs = np.linalg.eigh(lap)
    vals_new, vecs_new = np.linalg.eigh(edited)
    tau = a * np.sum((vecs[:, 1:].T @ r)**2 / vals[1:])
    pre_alignment = abs(x @ vecs[:, 1])
    post_alignment = abs(y @ vecs_new[:, 1])
    distance = min(np.count_nonzero((x > 0) != (y > 0)),
                   np.count_nonzero((x > 0) != (y < 0)))
    row = {
        "m": m,
        "n": n,
        "a": a,
        "lambda2_pre": float(vals[1]),
        "lambda2_post": float(vals_new[1]),
        "lambda3_post": float(vals_new[2]),
        "fiedler_pre_alignment": float(pre_alignment),
        "fiedler_post_alignment": float(post_alignment),
        "edge_leverage": float(tau),
        "leverage_bound": 1/m,
        "cut_distance": int(distance),
        "cut_weight_pre_x": 2*m*a,
        "cut_weight_post_x": 2*m*a+a,
        "cut_weight_y": 2*m,
    }
    tol = 1e-7
    assert abs(vals[1] - 2*a) < tol
    assert abs(vals_new[1] - 2) < tol
    assert vals_new[2] > 2
    assert pre_alignment > 1-tol and post_alignment > 1-tol
    assert tau < 1/m
    assert distance == n//2
    assert 2*m*a < 2*m < 2*m*a+a
    return row


if __name__ == "__main__":
    results = {"status": "PASS", "proof_status": "Numerical corroboration only",
               "cases": [check(m) for m in (2, 3, 4, 8, 16, 32)]}
    output = Path(__file__).with_name("sparse-instability-checks.json")
    output.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
