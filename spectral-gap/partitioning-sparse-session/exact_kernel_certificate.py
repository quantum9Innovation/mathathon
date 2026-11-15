"""Exact, finite-field certificates for an embedded equitable bisection.

No random-model theorem is asserted.  A successful certificate is a proof
for the supplied integer graph.  Failure means UNDECIDED, not nonuniqueness.
The sampler uses configuration rejection, conditional on simplicity, so its
three independent blocks have precisely the RSBM law (up to the PRNG).
Only numpy/scipy are used; there is no approximate rank decision.
"""

from __future__ import annotations

import argparse
import json
import random
from pathlib import Path

import numpy as np
from scipy.linalg import eigvalsh


def regular_edges(n: int, degree: int, rng: random.Random):
    assert n * degree % 2 == 0 and degree < n
    if degree == 0:
        return []
    while True:
        stubs = [v for v in range(n) for _ in range(degree)]
        rng.shuffle(stubs)
        edges = set()
        for u, v in zip(stubs[::2], stubs[1::2]):
            e = (min(u, v), max(u, v))
            if u == v or e in edges:
                break
            edges.add(e)
        else:
            return sorted(edges)


def biregular_edges(n: int, degree: int, rng: random.Random):
    assert degree <= n
    while True:
        left = [v for v in range(n) for _ in range(degree)]
        right = left.copy()
        rng.shuffle(right)
        edges = set()
        for u, v in zip(left, right):
            e = (u, v + n)
            if e in edges:
                break
            edges.add(e)
        else:
            return sorted(edges)


def rsbm(n: int, d_in: int, d_out: int, rng: random.Random):
    edges = regular_edges(n, d_in, rng)
    edges += [(u + n, v + n) for u, v in regular_edges(n, d_in, rng)]
    edges += biregular_edges(n, d_out, rng)
    permutation = list(range(2 * n))
    rng.shuffle(permutation)
    adjacency = np.zeros((2 * n, 2 * n), dtype=np.int64)
    labels = np.zeros(2 * n, dtype=np.int64)
    for old, new in enumerate(permutation):
        labels[new] = 1 if old < n else -1
    for u, v in edges:
        i, j = permutation[u], permutation[v]
        adjacency[i, j] = adjacency[j, i] = 1
    return adjacency, labels


def solve_mod(matrix: np.ndarray, rhs: np.ndarray, prime: int):
    """Gaussian elimination; returns (solution,det mod p) or None.

    Residues/products fit in int64 for the explicitly used small primes.
    """
    assert prime < 1_000_000
    a = matrix.copy() % prime
    b = rhs.copy() % prime
    size = len(b)
    determinant = 1
    for column in range(size):
        possible = np.flatnonzero(a[column:, column])
        if not len(possible):
            return None
        pivot = column + int(possible[0])
        if pivot != column:
            a[[column, pivot]] = a[[pivot, column]]
            b[[column, pivot]] = b[[pivot, column]]
            determinant = -determinant
        pivot_value = int(a[column, column])
        determinant = determinant * pivot_value % prime
        inverse = pow(pivot_value, -1, prime)
        a[column, column:] = a[column, column:] * inverse % prime
        b[column] = b[column] * inverse % prime
        factors = a[column + 1 :, column].copy()
        a[column + 1 :, column:] = (
            a[column + 1 :, column:]
            - factors[:, None] * a[column, column:][None, :]
        ) % prime
        b[column + 1 :] = (b[column + 1 :] - factors * b[column]) % prime
    solution = np.zeros(size, dtype=np.int64)
    for row in range(size - 1, -1, -1):
        solution[row] = (b[row] - a[row, row + 1 :] @ solution[row + 1 :]) % prime
    assert np.all((matrix @ solution - rhs) % prime == 0)
    return solution, int(determinant % prime)


def certify(adjacency: np.ndarray, eigenvalue: int, primes=(1009, 1013, 1019)):
    """Input has no planted labels.  Recover and certify if a minor succeeds."""
    size = len(adjacency)
    assert np.array_equal(adjacency, adjacency.T)
    assert np.all(np.diag(adjacency) == 0)
    assert np.all((adjacency == 0) | (adjacency == 1))
    assert np.all(adjacency.sum(axis=1) == adjacency[0].sum())
    assert isinstance(eigenvalue, int) and abs(eigenvalue) <= int(adjacency[0].sum())
    m = adjacency - eigenvalue * np.eye(size, dtype=np.int64)
    for prime in primes:
        result = solve_mod(m[1:, 1:], -m[1:, 0], prime)
        if result is None:
            continue
        z, determinant = result
        if not np.all((z == 1) | (z == prime - 1)):
            continue
        labels = np.r_[1, np.where(z == 1, 1, -1)]
        if np.any(m @ labels) or int(labels.sum()) != 0:
            continue
        # Nonzero integer minor + an exact null vector proves nullity one.
        return {
            "status": "CERTIFIED_UNIQUE_EQUITABLE_BISECTION_AT_LAMBDA",
            "eigenvalue": eigenvalue,
            "prime": prime,
            "deleted_vertex": 0,
            "cofactor_determinant_mod_prime": determinant,
            "labels": labels.tolist(),
        }
    return {"status": "UNDECIDED", "eigenvalue": eigenvalue}


def cube_lift(n: int, rng: random.Random):
    adjacency = np.zeros((8 * n, 8 * n), dtype=np.int64)
    for vertex in range(8):
        for coordinate in range(3):
            other = vertex ^ (1 << coordinate)
            if vertex < other:
                matching = list(range(n))
                rng.shuffle(matching)
                for i, j in enumerate(matching):
                    a, b = vertex * n + i, other * n + j
                    adjacency[a, b] = adjacency[b, a] = 1
    return adjacency


def run_diagnostics(destination: Path):
    rng = random.Random(20261115)
    records = []
    representative = None
    parameters = [(2, 1), (3, 1), (3, 2), (4, 1), (4, 3), (5, 3)]
    for d_in, d_out in parameters:
        for n in (24, 48, 96):
            for trial in range(8):
                adjacency, planted = rsbm(n, d_in, d_out, rng)
                lam, degree = d_in - d_out, d_in + d_out
                assert np.all(adjacency @ planted == lam * planted)
                certificate = certify(adjacency, lam)
                success = certificate["status"].startswith("CERTIFIED")
                eigenvalues = eigvalsh(adjacency.astype(float))
                record = {
                    "n_per_block": n, "d_in": d_in, "d_out": d_out,
                    "trial": trial, "certified": success,
                    "numeric_multiplicity_at_lambda": int(np.sum(abs(eigenvalues - lam) < 1e-8)),
                    "inside_tree_bulk": lam * lam < 4 * (degree - 1),
                    "scalar_bh_min_on_planted_vector": degree - 1 - lam * lam / 4,
                }
                if success:
                    recovered = np.array(certificate["labels"])
                    assert abs(int(recovered @ planted)) == 2 * n
                    record["prime"] = certificate["prime"]
                records.append(record)
                if success and d_in == 4 and d_out == 3 and n == 48 and trial == 0:
                    representative = {
                        "vertices": len(adjacency),
                        "edges": [list(map(int, e)) for e in zip(*np.where(np.triu(adjacency, 1)))],
                        "certificate": certificate,
                    }
    # Real exact counterexamples: at least three independent planted modes.
    cube_records = []
    for n in (1, 3, 8):
        adjacency = cube_lift(n, rng)
        for coordinate in range(3):
            labels = np.repeat([1 if not (v & (1 << coordinate)) else -1 for v in range(8)], n)
            assert np.all(adjacency @ labels == labels)
            assert sum(labels) == 0
        certificate = certify(adjacency, 1)
        assert certificate["status"] == "UNDECIDED"
        cube_records.append({"lift_degree": n, "vertices": 8 * n, "certificate_status": "UNDECIDED",
                             "known_independent_flat_modes": 3})
    summary = {
        "scope": "Finite exact certificates and numerical diagnostics, not an asymptotic theorem or novelty claim.",
        "seed": 20261115,
        "rsbm_samples": len(records),
        "certified": sum(r["certified"] for r in records),
        "undecided": sum(not r["certified"] for r in records),
        "records": records,
        "cube_counterexamples": cube_records,
    }
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "kernel-diagnostics.json").write_text(json.dumps(summary, indent=2) + "\n")
    (destination / "example-certificate.json").write_text(json.dumps(representative, indent=2) + "\n")
    print(json.dumps({key: summary[key] for key in ("rsbm_samples", "certified", "undecided")}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    run_diagnostics(args.output)
