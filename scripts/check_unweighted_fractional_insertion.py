#!/usr/bin/env python3
"""Finite diagnostics of bipartite unweighted insertion transfer; not a proof."""
import json
import numpy as np


def fractional(a, exponent):
    values, vectors = np.linalg.eigh(a)
    assert values[1] > 0
    powers = np.zeros_like(values)
    powers[1:] = values[1:] ** exponent
    return (vectors * powers) @ vectors.T


def response(a, b, alpha):
    inverse = fractional(a, -alpha / 2)
    c = inverse @ (fractional(b, alpha) - fractional(a, alpha)) @ inverse
    return (c + c.T) / 2


def host(s):
    # Target masses 1,2,1; macro conductances 1 and 1/2.
    sizes = [s, 2 * s, s]
    edges = []
    colors = []
    cells = []
    ports = []
    for index, size in enumerate(sizes):
        assert size % 2 == 0
        start = len(colors)
        half = size // 2
        colors.extend([0] * half + [1] * half)
        vertices = list(range(start, start + size))
        cells.append(vertices)
        for u in vertices[:half]:
            for v in vertices[half:]:
                edges.append((u, v))
        ports.append(start if index == 0 else start + half)

    def add_path(u, v, length):
        previous = u
        for step in range(length - 1):
            vertex = len(colors)
            colors.append(1 - colors[previous])
            edges.append((previous, vertex))
            previous = vertex
        assert colors[previous] != colors[v]
        edges.append((previous, v))

    for _ in range(3):
        add_path(ports[0], ports[1], 3)
    for _ in range(2):
        add_path(ports[1], ports[2], 4)
    n = len(colors)
    adjacency = np.zeros((n, n), dtype=float)
    for u, v in edges:
        assert u != v and adjacency[u, v] == 0
        assert colors[u] != colors[v]
        adjacency[u, v] = adjacency[v, u] = 1
    u, v = ports[:2]
    assert adjacency[u, v] == 0 and colors[u] != colors[v]
    laplacian = np.diag(adjacency.sum(axis=1)) - adjacency
    b = np.zeros(n)
    b[u], b[v] = 1, -1
    updated = laplacian + np.outer(b, b)
    j = np.zeros((n, 3))
    for i, vertices in enumerate(cells):
        j[vertices, i] = 1 / np.sqrt(len(vertices))
    return laplacian, updated, b, j


def main():
    k = np.array([[1.0, -1.0, 0.0], [-1.0, 1.5, -0.5],
                  [0.0, -0.5, 0.5]])
    edit = np.array([1.0, -1.0, 0.0])
    kp = k + np.outer(edit, edit)
    m = np.diag(np.array([1.0, 2.0, 1.0]) ** -0.5)
    h, hp = m @ k @ m, m @ kp @ m
    alphas = [0.3, 0.5, 0.7]
    results = []
    previous_errors = {alpha: [] for alpha in alphas}
    for s in [4, 16, 64]:
        l, lp, b, j = host(s)
        effective_resistance = float(b @ fractional(l, -1) @ b)
        assert abs(effective_resistance - 1) < 1e-10
        for alpha in alphas:
            c = response(l, lp, alpha)
            eigs = np.linalg.eigvalsh(c)[::-1]
            target = np.linalg.eigvalsh(response(h, hp, alpha))[::-1]
            expected = np.sort(np.r_[target, np.zeros(len(l) - 3)])[::-1]
            spectral_error = float(np.max(np.abs(eigs - expected)))
            previous_errors[alpha].append(spectral_error)
            budget_error = float(abs(np.log1p(eigs).sum() - alpha * np.log(2)))
            assert budget_error < 1e-9
            compressed_error = float(np.linalg.norm(
                j.T @ fractional(s * l, alpha) @ j - fractional(h, alpha), 2))
            results.append(dict(s=s, vertices=len(l), alpha=alpha,
                                effective_resistance=effective_resistance,
                                spectral_error=spectral_error,
                                compressed_power_error=compressed_error,
                                determinant_budget_error=budget_error))
    for alpha, errors in previous_errors.items():
        # The theorem is asymptotic and supplies no uniform finite-s rate.
        # These specific cases need not improve monotonically at small s.
        assert errors[-1] < errors[0]
    print(json.dumps(dict(results=results, status="PASS"), indent=2))


if __name__ == "__main__":
    main()
