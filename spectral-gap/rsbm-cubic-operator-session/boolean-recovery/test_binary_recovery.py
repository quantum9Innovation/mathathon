"""Exhaustive exact checks and correctly sampled uniform-simple demonstrations.

Run: python3 test_binary_recovery.py
Output: one concise JSON object. No nonstandard dependency is used.
"""

import itertools
import json
import random
import time
from fractions import Fraction

from binary_recovery import (
    affine_labelings,
    binary_affine_space,
    canonical_partition,
    is_perfect_matching_cut,
    recover,
)


def build_graph(plus, minus, matching=None, permutation=None):
    n = len(plus)
    matching = list(range(n)) if matching is None else matching
    permutation = list(range(2 * n)) if permutation is None else permutation
    adjacency = [[] for _ in range(2 * n)]

    def edge(a, b):
        a, b = permutation[a], permutation[b]
        adjacency[a].append(b)
        adjacency[b].append(a)

    for side, graph in enumerate((plus, minus)):
        for i, neighbors in enumerate(graph):
            for j in neighbors:
                if i < j:
                    edge(i + side * n, j + side * n)
    for i, j in enumerate(matching):
        edge(i, j + n)
    planted = sum(1 << permutation[i] for i in range(n))
    return adjacency, canonical_partition(planted, 2 * n)


def all_simple_two_factors(n):
    edges = list(itertools.combinations(range(n), 2))
    out = []
    for selected in itertools.combinations(edges, n):
        degrees = [0] * n
        for a, b in selected:
            degrees[a] += 1
            degrees[b] += 1
        if degrees != [2] * n:
            continue
        adjacency = [[] for _ in range(n)]
        for a, b in selected:
            adjacency[a].append(b)
            adjacency[b].append(a)
        out.append(adjacency)
    return out


def parity_solution(adjacency, mask):
    return all(
        (sum((mask >> j) & 1 for j in neighbors) + ((mask >> i) & 1)) % 2 == 1
        for i, neighbors in enumerate(adjacency)
    )


def exhaustive_small_tests():
    reports = []
    for n in (3, 4, 5):
        graphs = all_simple_two_factors(n)
        nonunique = 0
        nullities = {}
        for plus in graphs:
            for minus in graphs:
                adjacency, planted = build_graph(plus, minus)
                particular, basis = binary_affine_space(adjacency)
                affine = set(affine_labelings(particular, basis))
                brute_parity = {
                    mask for mask in range(1 << (2 * n)) if parity_solution(adjacency, mask)
                }
                assert affine == brute_parity
                accepted = {
                    canonical_partition(mask, 2 * n)
                    for mask in affine
                    if is_perfect_matching_cut(adjacency, mask)
                }
                brute_cuts = {
                    canonical_partition(mask, 2 * n)
                    for mask in range(1 << (2 * n))
                    if is_perfect_matching_cut(adjacency, mask)
                }
                assert accepted == brute_cuts
                assert planted in accepted
                outcome = recover(adjacency)
                assert (outcome.status == "ok") == (len(accepted) == 1)
                if outcome.status == "ok":
                    assert outcome.partition == planted
                else:
                    assert outcome.status == "multiple_partitions"
                    nonunique += 1
                cutoff = recover(adjacency, cutoff_exponent=0)
                assert cutoff.status == "cutoff" and cutoff.checked_candidates == 0
                nullities[len(basis)] = nullities.get(len(basis), 0) + 1
        reports.append({
            "N": n,
            "simple_two_factors": len(graphs),
            "ordered_graph_pairs": len(graphs) ** 2,
            "all_affine_and_cut_sets_match_brute_force": True,
            "nonunique_partitions": nonunique,
            "binary_nullity_histogram": nullities,
        })
    return reports


def uniform_simple_two_factor(n, rng):
    """Uniform configuration pairing, rejected unless simple: exact graph law.

    A shuffled list of distinct stubs paired consecutively is a uniform
    perfect matching of stubs. Every simple labeled 2-regular graph has
    exactly 2^n preimages in this pairing space, so rejection gives the
    desired uniform law. This is not a uniform-permutation cycle model.
    """
    attempts = 0
    while True:
        attempts += 1
        stubs = list(range(2 * n))
        rng.shuffle(stubs)
        adjacency = [set() for _ in range(n)]
        valid = True
        for i in range(0, 2 * n, 2):
            a, b = stubs[i] // 2, stubs[i + 1] // 2
            if a == b or b in adjacency[a]:
                valid = False
                break
            adjacency[a].add(b)
            adjacency[b].add(a)
        if valid:
            return [sorted(neighbors) for neighbors in adjacency], attempts


def random_demonstrations():
    rng = random.Random(20261115)
    reports = []
    for n in (100, 300, 1000):
        start = time.perf_counter()
        plus, attempts_plus = uniform_simple_two_factor(n, rng)
        minus, attempts_minus = uniform_simple_two_factor(n, rng)
        matching = list(range(n))
        rng.shuffle(matching)
        permutation = list(range(2 * n))
        rng.shuffle(permutation)
        adjacency, planted = build_graph(plus, minus, matching, permutation)
        outcome = recover(adjacency)
        assert outcome.status == "ok" and outcome.partition == planted
        reports.append({
            "N": n,
            "binary_nullity": outcome.binary_nullity,
            "affine_candidates": outcome.affine_candidates,
            "checked_candidates": outcome.checked_candidates,
            "recovered_planted_after_random_vertex_permutation": True,
            "configuration_rejection_attempts": [attempts_plus, attempts_minus],
            "elapsed_seconds": round(time.perf_counter() - start, 6),
        })
    return reports


def deterministic_edge_cases():
    # K4 has affine parity solutions but no perfect matching cut.
    k4 = [[j for j in range(4) if j != i] for i in range(4)]
    outcome = recover(k4)
    assert outcome.status == "no_partition" and outcome.affine_candidates == 8

    # Earlier certified example: unique Boolean partition, real corank two.
    cycles = ([0, 1, 2, 3, 4, 5, 6, 7], [5, 6, 7, 0, 4, 1, 2, 3])
    graphs = []
    for cycle in cycles:
        graph = [[] for _ in range(8)]
        for i in range(8):
            a, b = cycle[i], cycle[(i + 1) % 8]
            graph[a].append(b)
            graph[b].append(a)
        graphs.append(graph)
    adjacency, planted = build_graph(*graphs)
    recovery = recover(adjacency)
    assert recovery.status == "ok" and recovery.partition == planted
    assert recovery.affine_candidates == 16

    # Independently certify that this Boolean recovery example really has
    # real eigenvalue-1 multiplicity two. All arithmetic is exact rational.
    matrix = [[int(j in adjacency[i]) - int(i == j) for j in range(16)] for i in range(16)]
    vectors = (
        [-1, 0, -1, -2, -1, 0, 0, -1, 0, 2, 1, 0, 1, 1, 1, 0],
        [0, -1, 0, 1, 0, -1, -1, 0, 1, -1, 0, 1, 0, 0, 0, 1],
    )
    for vector in vectors:
        assert all(sum(a * b for a, b in zip(row, vector)) == 0 for row in matrix)
    assert vectors[0][0] * vectors[1][1] - vectors[0][1] * vectors[1][0] == 1
    rational_rows = [[Fraction(value) for value in row] for row in matrix]
    rank = 0
    for column in range(16):
        pivot = next((i for i in range(rank, 16) if rational_rows[i][column]), None)
        if pivot is None:
            continue
        rational_rows[rank], rational_rows[pivot] = rational_rows[pivot], rational_rows[rank]
        pivot_row = rational_rows[rank]
        for i in range(rank + 1, 16):
            if rational_rows[i][column]:
                scale = rational_rows[i][column] / pivot_row[column]
                rational_rows[i] = [a - scale * b for a, b in zip(rational_rows[i], pivot_row)]
        rank += 1
    assert rank == 14

    c = [[int(j in graphs[0][i]) - int(i == j) for j in range(8)] for i in range(8)]
    d = [[int(j in graphs[1][i]) - int(i == j) for j in range(8)] for i in range(8)]
    kernel_matrix = [[sum(d[i][h] * c[h][j] for h in range(8)) - int(i == j)
                      for j in range(8)] for i in range(8)]
    minor = [row[:6] for row in kernel_matrix[:6]]

    def bareiss_determinant(rows):
        rows = [row[:] for row in rows]
        sign, denominator = 1, 1
        for k in range(len(rows) - 1):
            if not rows[k][k]:
                pivot = next((i for i in range(k + 1, len(rows)) if rows[i][k]), None)
                if pivot is None:
                    return 0
                rows[k], rows[pivot] = rows[pivot], rows[k]
                sign *= -1
            pivot_value = rows[k][k]
            for i in range(k + 1, len(rows)):
                for j in range(k + 1, len(rows)):
                    numerator = pivot_value * rows[i][j] - rows[i][k] * rows[k][j]
                    assert numerator % denominator == 0
                    rows[i][j] = numerator // denominator
                rows[i][k] = 0
            denominator = pivot_value
        return sign * rows[-1][-1]

    assert bareiss_determinant(minor) == -4
    return {
        "K4_no_partition_correctly_rejected": True,
        "certified_real_corank_two_N8": {
            "recovered_planted": True,
            "binary_nullity": recovery.binary_nullity,
            "affine_candidates": recovery.affine_candidates,
            "exact_rational_rank_A_minus_I": rank,
            "nonzero_six_by_six_minor_of_reduced_K": -4,
            "two_independent_integer_kernel_vectors_checked": True,
        },
    }


if __name__ == "__main__":
    print(json.dumps({
        "exhaustive_simple_model": exhaustive_small_tests(),
        "deterministic_edge_cases": deterministic_edge_cases(),
        "uniform_simple_demonstrations": random_demonstrations(),
        "sampling": "independent uniform configuration pairings conditioned simple",
        "seed": 20261115,
    }, indent=2, sort_keys=True))
