"""Exact generic recovery checks using the requested uniform simple laws.

Run: python3 test_general_recovery.py
Internal graphs use uniform configuration pairing followed by rejection.
Cross graphs use one uniform bijection of all bN distinguished stubs,
followed by duplicate-edge rejection. No sum of random matchings is used.
"""

import json
import random
import time

from binary_recovery import (
    affine_labelings,
    binary_affine_space,
    canonical_partition,
    is_prescribed_crossing_degree,
    recover_regular,
)


def uniform_simple_internal(n, degree, rng):
    if n * degree % 2:
        raise ValueError("The number of internal stubs must be even")
    attempts = 0
    while True:
        attempts += 1
        stubs = list(range(degree * n))
        rng.shuffle(stubs)
        adjacency = [set() for _ in range(n)]
        valid = True
        for i in range(0, degree * n, 2):
            a, b = stubs[i] // degree, stubs[i + 1] // degree
            if a == b or b in adjacency[a]:
                valid = False
                break
            adjacency[a].add(b)
            adjacency[b].add(a)
        if valid:
            return [sorted(neighbors) for neighbors in adjacency], attempts


def uniform_simple_cross(n, degree, rng):
    attempts = 0
    while True:
        attempts += 1
        # Domain stubs are distinguished and fixed in vertex order. A
        # uniform permutation of all target stubs is a uniform bijection.
        target_stubs = list(range(degree * n))
        rng.shuffle(target_stubs)
        adjacency = [set() for _ in range(n)]
        valid = True
        for source_stub, target_stub in enumerate(target_stubs):
            a, b = source_stub // degree, target_stub // degree
            if b in adjacency[a]:
                valid = False
                break
            adjacency[a].add(b)
        if valid:
            target_degrees = [0] * n
            for neighbors in adjacency:
                for j in neighbors:
                    target_degrees[j] += 1
            assert target_degrees == [degree] * n
            return [sorted(neighbors) for neighbors in adjacency], attempts


def sample_model(n, internal_degree, cross_degree, rng):
    plus, attempts_plus = uniform_simple_internal(n, internal_degree, rng)
    minus, attempts_minus = uniform_simple_internal(n, internal_degree, rng)
    cross, attempts_cross = uniform_simple_cross(n, cross_degree, rng)
    permutation = list(range(2 * n))
    rng.shuffle(permutation)
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
    for i, neighbors in enumerate(cross):
        for j in neighbors:
            edge(i, n + j)
    planted = canonical_partition(sum(1 << permutation[i] for i in range(n)), 2 * n)
    return adjacency, planted, [attempts_plus, attempts_minus, attempts_cross]


def check_small_cases(rng):
    reports = []
    for a, b, n in ((2, 1, 3), (2, 1, 4), (3, 1, 4), (3, 2, 4), (4, 1, 5), (4, 2, 5), (4, 3, 5)):
        adjacency, planted, attempts = sample_model(n, a, b, rng)
        particular, basis = binary_affine_space(adjacency, b & 1)
        affine = set(affine_labelings(particular, basis))

        def parity_valid(mask):
            return all(
                (sum((mask >> j) & 1 for j in neighbors) + ((a + b) & 1) * ((mask >> i) & 1)) % 2 == b % 2
                for i, neighbors in enumerate(adjacency)
            )

        brute_affine = {mask for mask in range(1 << (2 * n)) if parity_valid(mask)}
        assert affine == brute_affine
        accepted = {
            canonical_partition(mask, 2 * n)
            for mask in affine
            if is_prescribed_crossing_degree(adjacency, mask, b)
        }
        brute = {
            canonical_partition(mask, 2 * n)
            for mask in range(1 << (2 * n))
            if is_prescribed_crossing_degree(adjacency, mask, b)
        }
        assert accepted == brute and planted in accepted
        outcome = recover_regular(adjacency, b)
        assert (outcome.status == "ok") == (len(accepted) == 1)
        if outcome.status == "ok":
            assert outcome.partition == planted
        else:
            assert outcome.status == "multiple_partitions"
        assert recover_regular(adjacency, b, cutoff_exponent=0).status == "cutoff"
        reports.append({
            "N": n, "a": a, "b": b,
            "binary_nullity": len(basis),
            "inequivalent_partitions": len(accepted),
            "all_affine_and_verified_sets_match_brute_force": True,
            "nonuniqueness_correctly_detected": len(accepted) > 1,
        })
    return reports


def demonstrations(rng):
    reports = []
    for a, b, n in ((4, 1, 101), (4, 2, 101), (4, 3, 101), (3, 1, 100), (3, 2, 100), (2, 1, 101)):
        start = time.perf_counter()
        adjacency, planted, attempts = sample_model(n, a, b, rng)
        outcome = recover_regular(adjacency, b)
        assert outcome.status == "ok" and outcome.partition == planted
        reports.append({
            "N": n, "a": a, "b": b,
            "binary_nullity": outcome.binary_nullity,
            "affine_candidates": outcome.affine_candidates,
            "checked_candidates": outcome.checked_candidates,
            "recovered_planted_after_random_vertex_permutation": True,
            "configuration_rejection_attempts_internal_left_right_cross": attempts,
            "formal_cutoff_exponent": 27,
            "elapsed_seconds": round(time.perf_counter() - start, 6),
        })
    return reports


def unpromised_input_checks():
    # Two disjoint odd-order K5 components give an inconsistent RHS for
    # prescribed odd crossing degree. Recovery must report this explicitly.
    two_k5 = [[j for j in range(10) if j // 5 == i // 5 and j != i] for i in range(10)]
    assert recover_regular(two_k5, 1).status == "inconsistent"
    # K6 has parity solutions for b=2, but every balanced split has crossing
    # degree three; the integer verification must reject all candidates.
    k6 = [[j for j in range(6) if j != i] for i in range(6)]
    assert recover_regular(k6, 2).status == "no_partition"
    return {"inconsistent_system_detected": True, "integer_verification_rejects_wrong_degree": True}


if __name__ == "__main__":
    rng = random.Random(2026111502)
    print(json.dumps({
        "seed": 2026111502,
        "small_exact_checks": check_small_cases(rng),
        "unpromised_input_checks": unpromised_input_checks(),
        "uniform_simple_demonstrations": demonstrations(rng),
        "sampling": {
            "internal": "uniform pairing of all aN distinguished stubs, conditioned simple",
            "cross": "uniform bijection of all bN distinguished stubs, conditioned simple",
        },
    }, indent=2, sort_keys=True))
