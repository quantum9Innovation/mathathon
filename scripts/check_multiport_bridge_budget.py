"""Finite electrical diagnostics for the sharp bridge-budget construction.

Checks actual simple bipartite graphs, their reservoir-mean impedances,
the multiport Thomson bounds, and equal target Schur-pivot allocation.
This is not a fractional-power convergence test or an efficiency claim.
"""

import json
from pathlib import Path

import numpy as np
from scipy.linalg import eigvalsh
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import splu


def target(degree, m, fraction=0.9):
    access = 2 / (degree - 2)
    c, cp = 1 / (1 + access), 1 / (0.5 + access)
    budget = np.log(cp / c)
    s = fraction * budget
    r = (cp / c) * np.exp(-s * np.arange(m + 1) / m)
    g = (cp - r * c) / (r - 1)
    q = np.diff(g)
    assert np.all(q > 0)
    t = 1 / q
    k = np.linalg.inv(np.diag(t) + (1 + access) * np.ones((m, m)))
    kp = np.linalg.inv(np.diag(t) + (0.5 + access) * np.ones((m, m)))
    ratios = []
    for i in range(m):
        _, a = np.linalg.slogdet(k[i:, i:])
        _, ap = np.linalg.slogdet(kp[i:, i:])
        if i + 1 < m:
            _, b = np.linalg.slogdet(k[i + 1 :, i + 1 :])
            _, bp = np.linalg.slogdet(kp[i + 1 :, i + 1 :])
        else:
            b = bp = 0.0
        ratios.append(ap - a - bp + b)
    assert np.max(np.abs(np.array(ratios) - s / m)) < 1e-11
    return t, s, ratios


def graph(degree, m, height):
    q, copies = degree - 1, (degree - 1) ** height
    assert copies <= 9
    edges, colors = set(), []

    def vertex(color):
        colors.append(color)
        return len(colors) - 1

    def edge(a, b):
        assert a != b and colors[a] != colors[b]
        e = tuple(sorted((a, b)))
        assert e not in edges
        edges.add(e)

    def tree(root, depth):
        if depth == 0:
            return [root]
        leaves = []
        for _ in range(q):
            child = vertex(1 - colors[root])
            edge(root, child)
            leaves.extend(tree(child, depth - 1))
        return leaves

    def bottom(root, labels, leaf_rows, row):
        if len(labels) == 1:
            leaf_rows[labels[0]] = root
            return
        cut = len(labels) // 2
        for part in (labels[:cut], labels[cut:]):
            child = vertex(1 - colors[root])
            edge(root, child)
            indicator = np.zeros(m)
            indicator[part] = 1
            row.append(indicator)
            bottom(child, part, leaf_rows, row)

    def reservoir(port_colors):
        old = [vertex(0) for _ in range(3)] + [vertex(1) for _ in range(3)]
        vertices, ports = list(old), []
        for index, (a, b) in enumerate((a, b) for a in old[:3] for b in old[3:]):
            if index < copies:
                x, y = vertex(1), vertex(0)
                vertices.extend((x, y))
                edge(a, x)
                edge(x, y)
                edge(y, b)
                ports.append(x if port_colors[index] == 1 else y)
            else:
                edge(a, b)
        local = np.zeros((len(vertices), len(vertices)))
        indices = {v: i for i, v in enumerate(vertices)}
        for a, b in edges:
            if a in indices and b in indices:
                i, j = indices[a], indices[b]
                local[i, i] += 1
                local[j, j] += 1
                local[i, j] -= 1
                local[j, i] -= 1
        return vertices, ports, 1 / eigvalsh(local)[1]

    left, right = vertex(0), vertex(1)
    edge(left, right)
    left_leaves = tree(left, height - 1)
    # Last-level leaves are ports, so no identification is needed.
    left_parents = [v for v in left_leaves for _ in range(q)]
    anchor, anchor_ports, bound = reservoir([1 - colors[v] for v in left_parents])
    for parent, port in zip(left_parents, anchor_ports):
        edge(parent, port)

    t, s, pivots = target(degree, m)
    lengths = np.maximum(1, np.rint(copies * t).astype(int))
    right_leaves = tree(right, height)
    colored_leaves, rows = [], []
    for root in right_leaves:
        leaves, row = [None] * m, []
        bottom(root, list(range(m)), leaves, row)
        colored_leaves.append(leaves)
        rows = row
    rb = sum((np.outer(row, row) for row in rows), np.zeros((m, m)))
    reservoirs = [anchor]
    for i in range(m):
        starts = [leaves[i] for leaves in colored_leaves]
        vertices, ports, ri = reservoir([colors[v] ^ (int(lengths[i]) % 2) for v in starts])
        reservoirs.append(vertices)
        bound = max(bound, ri)
        for start, port in zip(starts, ports):
            previous = start
            for _ in range(int(lengths[i]) - 1):
                nxt = vertex(1 - colors[previous])
                edge(previous, nxt)
                previous = nxt
            edge(previous, port)

    n = len(colors)
    data, row, col = [], [], []
    degrees = np.zeros(n, dtype=int)
    for a, b in edges:
        degrees[a] += 1
        degrees[b] += 1
        row.extend((a, b, a, b))
        col.extend((a, b, b, a))
        data.extend((1.0, 1.0, -1.0, -1.0))
    assert degrees.max() <= degree
    lap = coo_matrix((data, (row, col)), shape=(n, n)).tocsc()
    loads = np.zeros((n, m))
    loads[anchor, :] = -1 / len(anchor)
    for i, vertices in enumerate(reservoirs[1:]):
        loads[vertices, i] = 1 / len(vertices)
    assert np.max(np.abs(loads.sum(axis=0))) < 1e-13
    unit = np.zeros(n)
    unit[left], unit[right] = 1, -1
    j = np.ones((m, m))
    records, impedances = [], []
    for rb_value, update in ((1.0, False), (0.5, True)):
        a = lap.copy()
        if update:
            v = coo_matrix(unit[:, None]).tocsc()
            a = a + v @ v.T
        solver = splu(a[1:, 1:].tocsc())
        potentials = solver.solve(loads[1:, :])
        actual = loads[1:, :].T @ potentials
        impedances.append(actual)
        ideal = np.diag(lengths / copies) + (rb_value + 2 * (1 - 1 / copies) / (degree - 2)) * j + rb / copies
        difference = (actual - ideal + actual.T - ideal.T) / 2
        lower = float(eigvalsh(difference)[0])
        upper = float(eigvalsh((bound / copies) * (np.eye(m) + j) - difference)[0])
        assert lower > -2e-9 and upper > -2e-9
        resistance = float(unit[1:] @ solver.solve(unit[1:]))
        assert abs(resistance - rb_value) < 2e-9
        records.append({"updated": update, "contact_lower_margin": lower,
                        "contact_upper_margin": upper, "bridge_resistance": resistance})
    impedance_update_error = float(np.max(np.abs(impedances[1] - impedances[0] + 0.5 * j)))
    assert impedance_update_error < 2e-9
    return {"degree": degree, "m": m, "Q": copies, "vertices": n,
            "edges": len(edges), "bipartite": True, "equal_log_pivots": pivots,
            "allocated_budget": s, "impedance_update_error": impedance_update_error,
            "electrical_checks": records}


def main():
    records = [graph(d, m, h) for d, m, h in
               ((3, 2, 1), (3, 3, 2), (3, 3, 3), (4, 2, 1), (4, 3, 2), (5, 3, 1))]
    destination = Path(__file__).resolve().parents[1] / "spectral-gap/multiport-bridge-budget-checks.json"
    destination.write_text(json.dumps({"status": "PASS", "cases": records}, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "graphs": len(records),
                      "electrical_pairs": 2 * len(records), "output": str(destination)}))


if __name__ == "__main__":
    main()
