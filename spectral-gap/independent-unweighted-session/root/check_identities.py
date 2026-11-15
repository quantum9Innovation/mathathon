"""Finite checks of identities used in the proofs; no asymptotic claim relies on these."""
import json
from pathlib import Path

import numpy as np


def path_check(n, p, alpha):
    k = np.arange(1, n)
    lam = 4 * np.sin(k * np.pi / (2 * n)) ** 2
    phi = np.sqrt(2 / n) * np.cos(
        np.pi * (np.arange(1, n + 1)[:, None] - .5) * k[None, :] / n
    )
    u = phi[p - 1] - phi[p]
    z = u ** 2 / lam
    assert np.max(np.abs(z - 2 / n * np.sin(k * np.pi * p / n) ** 2)) < 1e-12
    b = np.diag(lam) + np.outer(u, u)
    blam, bv = np.linalg.eigh(b)
    inv = lam ** (-alpha / 2)
    correction = ((bv * blam ** alpha) @ bv.T) * np.outer(inv, inv) - np.eye(n - 1)
    correction = (correction + correction.T) / 2
    diff = np.log(lam[:, None] / lam[None, :])
    ker = np.full_like(diff, alpha)
    off = np.abs(diff) > 1e-14
    ker[off] = np.sinh(alpha * diff[off] / 2) / np.sinh(diff[off] / 2)
    signed_sqrt_z = u / np.sqrt(lam)
    derivative = np.outer(signed_sqrt_z, signed_sqrt_z) * ker
    eig = np.linalg.eigvalsh(correction)
    lower = float(np.linalg.eigvalsh(correction - derivative / 2)[0])
    upper = float(np.linalg.eigvalsh(derivative - correction)[0])
    logdet_error = abs(float(np.log1p(eig).sum()) - alpha * np.log(2))
    assert min(lower, upper) > -1e-8
    assert logdet_error < 1e-8
    assert eig[-1] >= alpha / 4 - 1e-8
    edge_mean_energy = float(u @ (lam * u) / 2)
    jensen_outlier = (1 + 2 / edge_mean_energy) ** alpha - 1
    assert eig[-1] >= jensen_outlier - 1e-8
    for cutoff in lam:
        assert z[lam <= cutoff].sum() <= np.sqrt(cutoff) + 1e-12
    return dict(n=n, p=p, alpha=alpha, sandwich_min=min(lower, upper),
                logdet_error=logdet_error, largest=float(eig[-1]),
                jensen_outlier=float(jensen_outlier),
                counts={str(e): int((eig > e).sum()) for e in [1e-2, 1e-4, 1e-6]})


def fanout_check(m=8, neck_factor=4):
    # Complete binary tree, root 0; leaf terminal necks, and an ideal ground edge.
    edges = [(i, 2 * i + 1) for i in range(m - 1)]
    edges += [(i, 2 * i + 2) for i in range(m - 1)]
    next_vertex = 2 * m - 1
    terminals = []
    for leaf in range(m - 1, 2 * m - 1):
        prev = leaf
        for _ in range(neck_factor * m):
            edges.append((prev, next_vertex))
            prev = next_vertex
            next_vertex += 1
        terminals.append(prev)
    matrix = np.zeros((next_vertex, next_vertex))
    for a, b in edges:
        matrix[a, a] += 1
        matrix[b, b] += 1
        matrix[a, b] -= 1
        matrix[b, a] -= 1
    interior = np.setdiff1d(np.arange(next_vertex), terminals)

    def kron(ground_conductance):
        mat = matrix.copy()
        mat[0, 0] += ground_conductance
        cross = mat[np.ix_(terminals, interior)]
        return mat[np.ix_(terminals, terminals)] - cross @ np.linalg.solve(
            mat[np.ix_(interior, interior)], cross.T)

    k0, k1 = kron(1), kron(2)
    change_eigs = np.linalg.eigvalsh(k1 - k0)
    assert change_eigs[-2] < 1e-12
    assert change_eigs[0] > -1e-12
    suffix_logratios = [
        np.linalg.slogdet(k1[i:, i:])[1] - np.linalg.slogdet(k0[i:, i:])[1]
        for i in range(m)
    ] + [0.]
    pivot_logratios = np.array(suffix_logratios[:-1]) - suffix_logratios[1:]
    assert pivot_logratios.min() > 0
    # With ideal contacts, the elementary circuit estimate gives this bound.
    bound = ((1 - 1 / neck_factor) ** 2 /
             ((neck_factor * m + np.log2(m)) *
              (1 + 1 / neck_factor) * (2 + 1 / neck_factor)))
    assert pivot_logratios.min() >= bound - 1e-10
    return dict(m=m, neck_factor=neck_factor,
                minimum_pivot_logratio=float(pivot_logratios.min()),
                proved_lower_estimate=float(bound),
                total_low_logbudget=float(sum(pivot_logratios)))


if __name__ == "__main__":
    results = {"paths": [path_check(n, p, a)
                         for n in [8, 32, 128]
                         for p in [1, n // 2]
                         for a in [.2, .5, .8]],
               "fanout": fanout_check()}
    output = Path(__file__).with_name("identity-checks.json")
    output.write_text(json.dumps(results, indent=2) + "\n")
    print(f"PASS: {len(results['paths'])} path checks; binary fanout pivot identities")
