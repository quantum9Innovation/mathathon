from fractions import Fraction as F
from pathlib import Path
import hashlib
import json


def zero(r, c):
    return [[F(0) for _ in range(c)] for _ in range(r)]


def identity(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def scale(t, a):
    return [[t * x for x in row] for row in a]


def add(*matrices):
    return [
        [sum(a[i][j] for a in matrices) for j in range(len(matrices[0][0]))]
        for i in range(len(matrices[0]))
    ]


def multiply(a, b):
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def inverse(a):
    n = len(a)
    t = [list(row) + unit for row, unit in zip(a, identity(n))]
    for k in range(n):
        pivot = next(i for i in range(k, n) if t[i][k])
        t[k], t[pivot] = t[pivot], t[k]
        c = t[k][k]
        t[k] = [x / c for x in t[k]]
        for i in range(n):
            if i != k:
                c = t[i][k]
                t[i] = [x - c * y for x, y in zip(t[i], t[k])]
    return [row[n:] for row in t]


def determinant(a):
    t = [list(row) for row in a]
    result = F(1)
    for k in range(len(t)):
        pivot = next((i for i in range(k, len(t)) if t[i][k]), None)
        if pivot is None:
            return F(0)
        if pivot != k:
            t[k], t[pivot] = t[pivot], t[k]
            result = -result
        c = t[k][k]
        result *= c
        for i in range(k + 1, len(t)):
            r = t[i][k] / c
            for j in range(k + 1, len(t)):
                t[i][j] -= r * t[k][j]
    return result


def adjacency(n, edges):
    a = zero(n, n)
    for i, j in edges:
        a[i][j] = F(1)
        a[j][i] = F(1)
    assert all(sum(row) == 3 for row in a)
    return a


graphs = {
    "K4": adjacency(4, [(i, j) for i in range(4) for j in range(i + 1, 4)]),
    "triangular_prism": adjacency(
        6,
        [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)],
    ),
    "cube": adjacency(
        8, [(i, j) for i in range(8) for j in range(i + 1, 8) if (i ^ j) in (1, 2, 4)]
    ),
}

cases = []
for name, a in graphs.items():
    n = len(a)
    unit = identity(n)
    perron = [[F(1, n) for _ in range(n)] for _ in range(n)]
    q = add(unit, scale(-1, perron))
    for marks in ([0], [0, 1], [0, n - 1], [0, 1, n - 1]):
        m = len(marks)
        e = [[F(i == j) for j in marks] for i in range(n)]
        et = transpose(e)
        b = multiply(a, e)
        bt = transpose(b)
        for z in (F(5, 2), F(3), F(7, 2), F(4), F(5)):
            shifted = add(scale(z, unit), scale(-1, a), scale(3, perron))
            r = multiply(multiply(q, inverse(shifted)), q)
            lhs = multiply(multiply(a, r), a)
            rhs = add(scale(z * z, r), scale(-z, unit), scale(-1, a), scale(z + 3, perron))
            assert lhs == rhs, (name, marks, z, "resolvent_polynomial")
            g = multiply(multiply(et, r), e)
            marked_a = multiply(multiply(et, a), e)
            for interaction in (False, True):
                c = [
                    [F(1, 7) if i == j else F(i + j + 1, 31) for j in range(m)]
                    for i in range(m)
                ] if interaction else zero(m, m)
                regular = add(
                    scale(z, identity(m)), scale(-1, c), scale(-1, multiply(multiply(bt, r), b))
                )
                predicted = add(
                    scale(2 * z, identity(m)),
                    scale(-1, c),
                    scale(-z * z, g),
                    marked_a,
                    [[-(z + 3) / n for _ in range(m)] for _ in range(m)],
                )
                assert regular == predicted, (name, marks, z, interaction, "stationary_correction")
                augmented = [a[i] + b[i] for i in range(n)] + [bt[i] + c[i] for i in range(m)]
                pencil = [[n * (z - 3)] + [F(-3)] * m]
                pencil += [[F(-3)] + regular[i] for i in range(m)]
                characteristic = determinant(add(scale(z, identity(n + m)), scale(-1, augmented)))
                assert characteristic * n * z == determinant(shifted) * determinant(pencil), (
                    name, marks, z, interaction, "pole_free_schur_determinant"
                )
                cases.append({
                    "host": name,
                    "marks": marks,
                    "z": str(z),
                    "interaction": interaction,
                    "at_perron_pole": z == 3,
                })

report = {
    "status": "pass",
    "arithmetic": "exact rational",
    "cases": len(cases),
    "checks_per_case": [
        "projected resolvent polynomial identity",
        "marked stationary correction",
        "pole-free Schur characteristic identity",
    ],
    "perron_pole_cases": sum(c["at_perron_pole"] for c in cases),
    "scope": "finite algebra corroboration only, no random-graph asymptotic inference",
    "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "details": cases,
}
Path(__file__).with_name("finite-check.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({key: report[key] for key in ("status", "arithmetic", "cases", "perron_pole_cases")}))
