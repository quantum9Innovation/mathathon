"""Exact finite diagnostics for unequal-block-integer-mode.tex, not a limit proof."""

import json
import random
from pathlib import Path

import numpy as np

from exact_kernel_certificate import regular_edges, solve_mod


def cross_edges(n1, n2, b1, b2, rng, structured=False):
    assert n1 * b1 == n2 * b2
    if structured:
        # A disjoint union of K_(b2,b1), fixed before sampling internal graphs.
        assert n1 % b2 == 0 and n2 % b1 == 0
        return [(i * b2 + u, n1 + i * b1 + v)
                for i in range(n1 // b2) for u in range(b2) for v in range(b1)]
    while True:
        left = [v for v in range(n1) for _ in range(b1)]
        right = [v for v in range(n2) for _ in range(b2)]
        rng.shuffle(right)
        edges = set()
        for u, v in zip(left, right):
            edge = (u, n1 + v)
            if edge in edges:
                break
            edges.add(edge)
        else:
            return sorted(edges)


def example(a1, a2, b1, b2, lam, n1, n2, rng, structured):
    # Sample the cross graph first; the proof permits any such fixed graph.
    edges = cross_edges(n1, n2, b1, b2, rng, structured)
    edges += regular_edges(n1, a1, rng)
    edges += [(u + n1, v + n1) for u, v in regular_edges(n2, a2, rng)]
    permutation = list(range(n1 + n2))
    rng.shuffle(permutation)
    adjacency = np.zeros((n1 + n2, n1 + n2), dtype=np.int64)
    planted = np.zeros(n1 + n2, dtype=np.int64)
    for old, new in enumerate(permutation):
        planted[new] = b1 if old < n1 else -(a1 - lam)
    for u, v in edges:
        i, j = permutation[u], permutation[v]
        adjacency[i, j] = adjacency[j, i] = 1
    assert np.all(adjacency @ planted == lam * planted)
    return adjacency, planted


def certify_two_levels(adjacency, lam, a1, b1, n1, n2):
    """Recover without labels; any acceptance proves real nullity one."""
    size = len(adjacency)
    m = adjacency - lam * np.eye(size, dtype=np.int64)
    c1 = a1 - lam
    assert c1 > 0
    for prime in (1009, 1013, 1019):
        if (b1 * c1 * (b1 + c1)) % prime == 0:
            continue
        result = solve_mod(m[1:, 1:], -m[1:, 0], prime)
        if result is None:
            continue
        residue_tail, det = result
        residues = np.r_[1, residue_tail]
        for first_positive in (True, False):
            first = b1 if first_positive else -c1
            positive_residue = b1 * pow(first % prime, -1, prime) % prime
            negative_residue = -c1 * pow(first % prime, -1, prime) % prime
            if not np.all((residues == positive_residue) | (residues == negative_residue)):
                continue
            candidate = np.where(residues == positive_residue, b1, -c1)
            if int(np.sum(candidate > 0)) != n1 or int(np.sum(candidate < 0)) != n2:
                continue
            if np.any(m @ candidate):
                continue
            return {"status": "CERTIFIED", "prime": prime,
                    "deleted_vertex": 0, "cofactor_mod_prime": det,
                    "integer_kernel_vector": candidate.tolist()}
    return {"status": "UNDECIDED"}


def main():
    rng = random.Random(2026111502)
    cases = [
        # a1,a2,b1,b2,lambda, n1/k,n2/k.
        (5, 3, 2, 4, 1, 4, 2),  # regular degree7, unequal blocks2:1.
        (4, 3, 2, 1, 2, 1, 2),
        (5, 4, 3, 2, 2, 2, 3),
    ]
    records, representative = [], None
    for a1, a2, b1, b2, lam, s1, s2 in cases:
        assert (a1 - lam) * (a2 - lam) == b1 * b2
        for scale in (6, 12):
            n1, n2 = s1 * scale, s2 * scale
            for structured in (False, True):
                for trial in range(4):
                    adjacency, planted = example(a1, a2, b1, b2, lam, n1, n2, rng, structured)
                    certificate = certify_two_levels(adjacency, lam, a1, b1, n1, n2)
                    success = certificate["status"] == "CERTIFIED"
                    if success:
                        assert np.array_equal(certificate["integer_kernel_vector"], planted)
                    records.append({"a1": a1, "a2": a2, "b1": b1, "b2": b2,
                                    "lambda": lam, "n1": n1, "n2": n2,
                                    "structured_cross": structured, "trial": trial,
                                    "certified": success})
                    if a1 == 5 and a2 == 3 and scale == 12 and structured and trial == 0:
                        representative = {
                            "parameters": {"a1": a1, "a2": a2, "b1": b1, "b2": b2,
                                           "lambda": lam, "n1": n1, "n2": n2},
                            "edges": [list(map(int, pair)) for pair in zip(*np.where(np.triu(adjacency, 1)))],
                            "certificate": certificate,
                        }
    result = {"scope": "Exact finite checks; no asymptotic probability or novelty conclusion.",
              "samples": len(records), "certified": sum(r["certified"] for r in records),
              "records": records}
    folder = Path(__file__).resolve().parent
    (folder / "unequal-block-checks.json").write_text(json.dumps(result, indent=2) + "\n")
    (folder / "unequal-block-example.json").write_text(json.dumps(representative, indent=2) + "\n")
    print(json.dumps({"samples": result["samples"], "certified": result["certified"]}))


if __name__ == "__main__":
    main()
