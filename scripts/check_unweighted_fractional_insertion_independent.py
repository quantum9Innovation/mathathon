"""Independent finite diagnostics of the unweighted bipartite insertion proof.

No convergence rate is asserted: the proof takes a sequence of large finite
graphs. Dense powers here only corroborate the graph and relative algebra.
"""

import json
from pathlib import Path

import numpy as np
from scipy.linalg import eigh


def power_on_graph(a, exponent):
    values, vectors = eigh(a)
    assert values[1] > 0
    weights = np.zeros(len(values))
    weights[1:] = values[1:] ** exponent
    return (vectors * weights) @ vectors.T


def correction(a, b, alpha):
    inverse = power_on_graph(a, -alpha / 2)
    c = inverse @ (power_on_graph(b, alpha) - power_on_graph(a, alpha)) @ inverse
    return (c + c.T) / 2


def path_matrix(weights):
    n = len(weights) + 1
    a = np.zeros((n, n))
    for i, w in enumerate(weights):
        a[i, i] += w
        a[i + 1, i + 1] += w
        a[i, i + 1] -= w
        a[i + 1, i] -= w
    return a


def graph(scale):
    edges = set()
    ports = []
    count = 0
    for i, mass in enumerate((2, 3, 4)):
        m = scale * mass // 2
        left = list(range(count, count + m))
        right = list(range(count + m, count + 2 * m))
        count += 2 * m
        ports.append(left[0])
        for u in left:
            for v in right:
                edges.add((u, v))

    def connector(u, v, width, length):
        nonlocal count
        for _ in range(width):
            chain = [u] + list(range(count, count + length - 1)) + [v]
            count += length - 1
            for p, q in zip(chain[:-1], chain[1:]):
                edge = tuple(sorted((p, q)))
                assert edge not in edges
                edges.add(edge)

    connector(ports[0], ports[1], 3, 3)  # Conductance exactly one.
    connector(ports[1], ports[2], 4, 6)  # Conductance exactly two thirds.
    insertion = tuple(sorted(ports[:2]))
    assert insertion not in edges
    adjacency = [[] for _ in range(count)]
    l = np.zeros((count, count))
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
        l[u, u] += 1
        l[v, v] += 1
        l[u, v] -= 1
        l[v, u] -= 1
    color = np.full(count, -1)
    color[0] = 0
    queue = [0]
    for u in queue:
        for v in adjacency[u]:
            if color[v] == -1:
                color[v] = 1 - color[u]
                queue.append(v)
            assert color[v] != color[u]
    assert len(queue) == count
    assert color[insertion[0]] != color[insertion[1]]
    b = np.zeros(count)
    b[insertion[0]], b[insertion[1]] = 1, -1
    return l, l + np.outer(b, b), b, len(edges)


def main():
    mass_scale = np.diag(np.array([2, 3, 4], dtype=float) ** -0.5)
    h = mass_scale @ path_matrix([1.0, 2 / 3]) @ mass_scale
    hp = mass_scale @ path_matrix([2.0, 2 / 3]) @ mass_scale
    records = []
    for scale in (4, 8, 16, 32):
        a, b, edge, edge_count = graph(scale)
        resistance = float(edge @ power_on_graph(a, -1) @ edge)
        assert abs(resistance - 1) < 3e-10
        for alpha in (0.25, 0.5, 0.75):
            target = np.linalg.eigvalsh(correction(h, hp, alpha))[::-1][:2]
            values = np.linalg.eigvalsh(correction(a, b, alpha))[::-1]
            logdet_error = abs(float(np.log1p(values).sum()) - alpha * np.log(2))
            assert logdet_error < 1e-8
            assert values[-1] > -1e-9
            records.append({"scale": scale, "alpha": alpha, "vertices": len(a),
                            "edges_before": edge_count, "effective_resistance": resistance,
                            "macro_spectrum": target.tolist(), "host_top_spectrum": values[:5].tolist(),
                            "top_two_error": float(np.max(np.abs(values[:2] - target))),
                            "largest_extra_eigenvalue": float(values[2]),
                            "logdet_error": logdet_error})
    # The theorem gives a limit without an explicit finite-size rate. Record
    # all spectral errors, including nonmonotone values; positivity, electrical
    # resistance and the determinant identity are the finite checks above.
    out = Path(__file__).resolve().parents[1] / "spectral-gap" / "unweighted-fractional-insertion-independent-checks.json"
    out.write_text(json.dumps({"status": "PASS", "cases": records,
                               "scope": "Finite diagnostics, not a proof or rate certificate."}, indent=2) + "\n")
    print(f"PASS: {len(records)} graph cases; {out}")
    print(f"Maximum logdet discrepancy: {max(r['logdet_error'] for r in records):.3g}")


if __name__ == "__main__":
    main()
