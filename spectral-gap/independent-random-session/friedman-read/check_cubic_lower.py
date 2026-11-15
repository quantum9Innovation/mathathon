"""Corroborate the cubic lower-bound formulas and finite covering witnesses."""

from collections import defaultdict
from decimal import Decimal, getcontext
from hashlib import sha256
import json
from pathlib import Path

import numpy as np
from scipy.linalg import helmert
from scipy.sparse import csr_matrix


HERE = Path(__file__).resolve().parent
THEOREM = HERE.parent / "sharp-cubic-threshold.tex"


def constants():
    getcontext().prec = 90
    a = Decimal("1.52")
    for _ in range(20):
        a -= (a ** 3 - a - 2) / (3 * a ** 2 - 1)
    t = 1 / a
    ell = a + 2 * t
    b = (ell - 1) / 2
    q = 2 * t * t
    assert a > Decimal(2).sqrt()
    assert q < 1
    assert abs(ell * b - 2 - t * b) < Decimal("1e-80")
    return a, t, ell, b, q


def finite_radial(R, t, ell, b, q):
    quotient = np.zeros((R + 2, R + 2))
    quotient[0, 0] = 1.0
    quotient[0, 1] = quotient[1, 0] = 2.0
    if R:
        quotient[1, 2] = quotient[2, 1] = 1.0
    for j in range(2, R + 1):
        quotient[j, j + 1] = quotient[j + 1, j] = np.sqrt(2.0)
    radial = np.array(
        [np.sqrt(2.0), np.sqrt(2.0) * b]
        + [np.sqrt(2.0 ** k) * b * t ** k for k in range(1, R + 1)]
    )
    M = 2 + 2 * b * b + 2 * b * b * t * t * (1 - q ** R) / (1 - q)
    trial = ell - 2 * b * b * t * q ** R / M
    direct = float(radial @ quotient @ radial / (radial @ radial))
    vals = np.linalg.eigvalsh(quotient)
    assert abs(float(radial @ radial) - M) < 1e-11
    assert abs(direct - trial) < 1e-12
    assert vals[-1] >= trial - 1e-12
    return quotient, direct, float(vals[-1])


def make_lift(m, n, seed, identity=False):
    rng = np.random.default_rng(seed)
    pairs = []
    neighbors = [[] for _ in range(4 * m * n)]

    def index(j, kind, sheet):
        return (4 * j + kind) * n + sheet

    def add_permutation(j, u, jj, v, p):
        for i in range(n):
            x, y = index(j, u, i), index(jj, v, int(p[i]))
            pairs.append((x, y))
            neighbors[x].append(y)
            neighbors[y].append(x)

    for j in range(m):
        for u, v in [(0, 1), (0, 2), (0, 3)]:
            add_permutation(j, u, j, v, np.arange(n))
        for u, v in [(1, 2), (1, 3)]:
            if identity:
                p = np.arange(n)
            elif j == 0:
                p = np.concatenate(([0], rng.permutation(np.arange(1, n))))
            else:
                p = rng.permutation(n)
            add_permutation(j, u, j, v, p)
        connector = np.arange(n) if identity else rng.permutation(n)
        add_permutation(j, 3, (j + 1) % m, 2, connector)
    assert all(len(set(ns)) == len(ns) == 3 for ns in neighbors)
    rows = [x for x, y in pairs] + [y for x, y in pairs]
    cols = [y for x, y in pairs] + [x for x, y in pairs]
    A = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(4 * m * n, 4 * m * n))
    return A, neighbors


def finite_tree_mapping(R, n, neighbors):
    edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]
    mapping = [0, n, 2 * n, 3 * n]
    parent = {2: 0, 3: 0}
    level = [2, 3]
    for k in range(R):
        next_level = []
        for v in level:
            if k == 0:
                candidates = [x for x in neighbors[mapping[v]] if x not in mapping[:4]]
                assert len(candidates) == 1
            else:
                candidates = [x for x in neighbors[mapping[v]] if x != mapping[parent[v]]]
                assert len(candidates) == 2
            for target in candidates:
                w = len(mapping)
                mapping.append(target)
                parent[w] = v
                edges.append((v, w))
                next_level.append(w)
        level = next_level
    count = len(mapping)
    T = np.zeros((count, count))
    for x, y in edges:
        T[x, y] = T[y, x] = 1
    assert count == 2 ** (R + 1) + 2
    return T, mapping


def check_pushforward(m, n, seed, Rs, identity=False):
    A, neighbors = make_lift(m, n, seed, identity=identity)
    if identity:
        new_max = 3.0
    else:
        W = np.kron(np.eye(4 * m), helmert(n).T)
        restricted = W.T @ (A @ W)
        new_max = float(np.linalg.eigvalsh(restricted)[-1])
    results = []
    for R in Rs:
        S = 2 ** (R + 1) + 2
        assert n >= 2 * S
        T, mapping = finite_tree_mapping(R, n, neighbors)
        values, vectors = np.linalg.eigh(T)
        mu = float(values[-1])
        h = np.abs(vectors[:, -1])
        assert np.max(np.abs(T @ h - mu * h)) < 1e-10
        g = np.zeros(A.shape[0])
        for i, x in enumerate(mapping):
            g[x] += h[i]
        surplus = A @ g - mu * g
        assert float(surplus.min()) > -1e-10
        old = np.repeat(g.reshape(4 * m, n).mean(axis=1), n)
        delta = float(old @ old / (g @ g))
        assert delta <= S / n + 1e-12
        gnew = g - old
        rayleigh = float(gnew @ (A @ gnew) / (gnew @ gnew))
        predicted = (mu - 3 * delta) / (1 - delta)
        assert rayleigh >= predicted - 1e-10
        assert new_max >= rayleigh - 1e-10
        collisions = len(mapping) - len(set(mapping))
        results.append({
            "m": m, "n": n, "seed": seed, "R": R,
            "all_permutations_identity": identity,
            "support_bound": S, "actual_support": int(np.count_nonzero(g)),
            "branch_mapping_collisions": collisions,
            "Dirichlet_Perron_value": mu,
            "minimum_pushforward_subeigen_surplus": float(surplus.min()),
            "old_projection_fraction": delta,
            "projection_Rayleigh_bound": predicted,
            "actual_new_witness_Rayleigh": rayleigh,
            "largest_new_eigenvalue": new_max,
        })
    return results


def main():
    a, t, ell, b, q = constants()
    tf, lf, bf, qf = map(float, (t, ell, b, q))
    radial = []
    for R in range(81):
        _, trial, perron = finite_radial(R, tf, lf, bf, qf)
        radial.append({"R": R, "trial_Rayleigh": trial, "Dirichlet_Perron_value": perron})
    finite_checks = []
    for m, n, seed, Rs in [(3, 16, 251, [0, 1]), (3, 32, 502, [0, 1, 2]), (5, 16, 753, [1])]:
        finite_checks.extend(check_pushforward(m, n, seed, Rs))
    collision_check = check_pushforward(3, 64, 0, [3], identity=True)
    assert collision_check[0]["branch_mapping_collisions"] > 0
    finite_checks.extend(collision_check)
    output = {
        "reviewed_tex_sha256_at_check": sha256(THEOREM.read_bytes()).hexdigest(),
        "constants": {"alpha": str(a), "t": str(t), "L": str(ell), "b": str(b), "q": str(q)},
        "exact_algebraic_factorization": "(alpha-1)(alpha^3-alpha-2)=alpha^4-alpha^3-alpha^2-alpha+2",
        "radial_quotient_checks": radial,
        "small_finite_lift_checks": finite_checks,
        "limits": "Numerical checks corroborate formulas. The written proof establishes the theorem for all permitted parameters.",
    }
    dest = HERE / "cubic-lower-checks.json"
    dest.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"output": str(dest), "radial_checks": len(radial), "finite_lift_checks": len(finite_checks), "L": str(ell)}))


if __name__ == "__main__":
    main()
