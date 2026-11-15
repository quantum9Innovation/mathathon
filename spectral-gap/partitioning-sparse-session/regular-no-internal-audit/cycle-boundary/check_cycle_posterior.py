"""Exhaust all named projections and edge matchings in small lift models."""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, permutations, product
from math import factorial
from pathlib import Path
import json


def balanced_blocks(vertices, k, size):
    if k == 1:
        yield (tuple(vertices),)
        return
    for block in combinations(vertices, size):
        chosen = set(block)
        remaining = tuple(v for v in vertices if v not in chosen)
        for tail in balanced_blocks(remaining, k - 1, size):
            yield (block,) + tail


def cycle_components(graph, n, edge_bits):
    adjacent = [[] for _ in range(n)]
    for (u, v), bit in edge_bits.items():
        if graph & bit:
            adjacent[u].append(v)
            adjacent[v].append(u)
    assert all(len(a) == 2 for a in adjacent)
    unseen = set(range(n))
    sizes = []
    while unseen:
        todo = [next(iter(unseen))]
        seen = set(todo)
        while todo:
            for v in adjacent[todo.pop()]:
                if v not in seen:
                    seen.add(v)
                    todo.append(v)
        unseen.difference_update(seen)
        sizes.append(len(seen))
    return tuple(sorted(sizes))


def exact_success(k, size):
    t = Fraction(1, 2 * k)
    result = Fraction(2 * k, factorial(size))
    for j in range(size):
        result *= t + j
    return result


def check(k, size):
    n = k * size
    edge_bits = {uv: 1 << j for j, uv in enumerate(combinations(range(n), 2))}
    all_perms = tuple(permutations(range(size)))
    outcomes = defaultdict(Counter)
    cases = 0
    prior_maps = 0
    for blocks in balanced_blocks(tuple(range(n)), k, size):
        prior_maps += 1
        unordered = tuple(sorted(sum(1 << v for v in block) for block in blocks))
        edge_codes = []
        for i in range(k):
            left, right = blocks[i], blocks[(i + 1) % k]
            codes = []
            for perm in all_perms:
                code = 0
                for u in range(size):
                    endpoints = tuple(sorted((left[u], right[perm[u]])))
                    code |= edge_bits[endpoints]
                codes.append(code)
            edge_codes.append(codes)
        for code_tuple in product(*edge_codes):
            graph = 0
            for code in code_tuple:
                graph |= code
            outcomes[graph][unordered] += 1
            cases += 1

    assert prior_maps == factorial(n) // factorial(size) ** k
    assert cases == factorial(n)
    component_joint_counts = Counter()
    graph_counts = Counter()
    largest_posterior_support = 0
    max_likelihood_discrepancy = 0
    for graph, partitions in outcomes.items():
        component_sizes = cycle_components(graph, n, edge_bits)
        assert all(s % k == 0 for s in component_sizes)
        r = len(component_sizes)
        assert len(partitions) == (2 * k) ** (r - 1)
        assert sum(partitions.values()) == (2 * k) ** r
        max_likelihood_discrepancy = max(
            max_likelihood_discrepancy,
            max(abs(value - 2 * k) for value in partitions.values()),
        )
        assert all(value == 2 * k for value in partitions.values())
        component_joint_counts[r] += sum(partitions.values())
        graph_counts[r] += 1
        largest_posterior_support = max(largest_posterior_support, len(partitions))
        if r == 1:
            assert len(partitions) == 1

    permutation_cycles = Counter()
    for perm in permutations(range(size)):
        unseen = set(range(size))
        cycles = 0
        while unseen:
            v = next(iter(unseen))
            while v in unseen:
                unseen.remove(v)
                v = perm[v]
            cycles += 1
        permutation_cycles[cycles] += 1
    for r in range(1, size + 1):
        assert Fraction(component_joint_counts[r], cases) == Fraction(
            permutation_cycles[r], factorial(size)
        )
    bayes = sum(Fraction(max(parts.values()), cases) for parts in outcomes.values())
    formula = exact_success(k, size)
    assert bayes == formula
    assert Fraction(component_joint_counts[1], cases) == Fraction(1, size)
    return {
        "k": k,
        "fiber_size": size,
        "vertices": n,
        "named_balanced_projections": prior_maps,
        "joint_projection_matching_cases": cases,
        "observed_labeled_graphs": len(outcomes),
        "graphs_by_component_count": dict(sorted(graph_counts.items())),
        "largest_posterior_support": largest_posterior_support,
        "max_unordered_likelihood_numerator_error": max_likelihood_discrepancy,
        "exact_bayes_success": str(bayes),
        "exact_formula": str(formula),
        "connected_probability": str(Fraction(1, size)),
        "status": "PASS",
    }


if __name__ == "__main__":
    records = [check(k, size) for k, size in [(3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (5, 1)]]
    result = {
        "scope": "All balanced named projections and all edge matchings; exact integer posterior numerators.",
        "records": records,
        "status": "PASS",
    }
    path = Path(__file__).with_name("cycle-posterior-checks.json")
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
