"""Exact finite configuration checks of the aggregate-fiber identity.

This verifies the counting identity, including loops, repeated edges,
ordered stubs, cross bijections, and the characteristic-two reduction.
It is finite verification, not a substitute for the asymptotic proofs.
Only Python's standard library is required.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import permutations, product
from math import factorial
import json
from pathlib import Path


def pairings(stubs):
    if not stubs:
        yield ()
        return
    first = stubs[0]
    for i in range(1, len(stubs)):
        rest = stubs[1:i] + stubs[i + 1 :]
        for tail in pairings(rest):
            yield ((first, stubs[i]),) + tail


def double_factorial_odd(n):
    result = 1
    for k in range(n, 0, -2):
        result *= k
    return result


def pairing_weight(table):
    if table[1] != table[2] or table[0] % 2 or table[3] % 2:
        return 0
    return (factorial(table[1]) * double_factorial_odd(table[0] - 1)
            * double_factorial_odd(table[3] - 1))


def fiber_moment(a, b, size):
    """Enumerate every ordered profile array, grouping only its tables."""
    delta = a - b
    profiles = []
    for labels in product(range(2), repeat=a + b + 1):
        root, *neighbors = labels
        if (sum(neighbors) - delta * root) % 2:
            continue
        internal = [0] * 4
        cross = [0] * 4
        for label in neighbors[:a]:
            internal[2 * root + label] += 1
        for label in neighbors[a:]:
            cross[2 * root + label] += 1
        profiles.append((tuple(internal), tuple(cross)))
    counts = Counter()
    for array in product(profiles, repeat=size):
        internal = tuple(sum(star[0][i] for star in array) for i in range(4))
        cross = tuple(sum(star[1][i] for star in array) for i in range(4))
        if pairing_weight(internal):
            counts[internal, cross] += 1
    weighted = defaultdict(int)
    for (internal, cross), count in counts.items():
        weighted[cross] += count * pairing_weight(internal)
    numerator = sum(value * weighted.get((h[0], h[2], h[1], h[3]), 0)
                    * factorial(h[0]) * factorial(h[1]) * factorial(h[2]) * factorial(h[3])
                    for h, value in weighted.items())
    denominator = (double_factorial_odd(a * size - 1) ** 2
                   * factorial(b * size))
    return Fraction(numerator, denominator), len(counts), len(weighted)


def internal_rows(pairing, degree, size):
    rows = [0] * size
    for stub, partner in pairing:
        i, j = stub // degree, partner // degree
        if i != j:
            rows[i] ^= 1 << j
            rows[j] ^= 1 << i
        # A loop has integer diagonal weight two, hence vanishes mod two.
    return rows


def nullity(rows, dimension):
    rows = list(rows)
    rank = 0
    for column in range(dimension):
        pivot = next((i for i in range(rank, dimension)
                      if (rows[i] >> column) & 1), None)
        if pivot is None:
            continue
        rows[pivot], rows[rank] = rows[rank], rows[pivot]
        for i in range(rank + 1, dimension):
            if (rows[i] >> column) & 1:
                rows[i] ^= rows[rank]
        rank += 1
    return dimension - rank


def configuration_moment(a, b, size):
    internals = [internal_rows(pairing, a, size)
                 for pairing in pairings(tuple(range(a * size)))]
    cross_rows = []
    for bijection in permutations(range(b * size)):
        plus, minus = [0] * size, [0] * size
        for stub, partner in enumerate(bijection):
            i, j = stub // b, partner // b
            plus[i] ^= 1 << j
            minus[j] ^= 1 << i
        cross_rows.append((plus, minus))
    distribution = Counter()
    for left, right, cross in product(internals, internals, cross_rows):
        plus, minus = cross
        rows = [left[i] ^ (plus[i] << size)
                ^ (((a - b) % 2) << i) for i in range(size)]
        rows += [(right[i] << size) ^ minus[i]
                 ^ (((a - b) % 2) << (size + i)) for i in range(size)]
        distribution[nullity(rows, 2 * size)] += 1
    total = sum(distribution.values())
    moment = Fraction(sum((1 << r) * count for r, count in distribution.items()), total)
    return moment, total, dict(sorted(distribution.items()))


def main():
    results = []
    for a, b, size in [(2, 1, 2), (2, 1, 3), (3, 1, 2), (2, 2, 2), (3, 2, 2)]:
        fiber, table_pairs, cross_tables = fiber_moment(a, b, size)
        direct, configurations, distribution = configuration_moment(a, b, size)
        assert fiber == direct, (a, b, size, fiber, direct)
        results.append({"a": a, "b": b, "N": size,
                        "configurations": configurations,
                        "valid_internal_cross_table_pairs": table_pairs,
                        "cross_tables": cross_tables,
                        "moment_fiber": str(fiber), "moment_direct": str(direct),
                        "binary_nullity_counts": distribution, "status": "PASS"})
    output = {"scope": "Exact configuration-model identity, not asymptotic recovery",
              "cases": results, "status": "PASS"}
    destination = Path(__file__).with_name("fiber-checks.json")
    destination.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
