"""Exhaust exact typed-configuration counts and the symmetrized all-slot identity.

The checks are finite corroboration; the written proof is independent of them.
Only Python's standard library is used. Zero/one internal degrees are explicit.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import permutations, product
from math import factorial, log
from pathlib import Path
import json


def pairings(stubs):
    if not stubs:
        yield ()
        return
    first, rest = stubs[0], stubs[1:]
    for j, other in enumerate(rest):
        for tail in pairings(rest[:j] + rest[j + 1:]):
            yield ((first, other),) + tail


def pair_count(n):
    assert n % 2 == 0
    return factorial(n) // (2 ** (n // 2) * factorial(n // 2))


def entropy(counts):
    total = sum(counts)
    if not total:
        return 0.0
    return -sum((x / total) * log(x / total) for x in counts if x)


def configurations(sizes, frame):
    offsets, cursor = [], 0
    for size in sizes:
        offsets.append(cursor)
        cursor += size
    d = sum(frame[0])
    assert all(sum(row) == d for row in frame)
    starts = [[sum(row[:j]) for j in range(len(sizes))] for row in frame]
    factor_lists, denominator = [], 1
    for i, size in enumerate(sizes):
        a = frame[i][i]
        if a:
            stubs = tuple((offsets[i] + v, starts[i][i] + ell)
                          for v in range(size) for ell in range(a))
            factor_lists.append(tuple(pairings(stubs)))
            denominator *= pair_count(len(stubs))
        for j in range(i + 1, len(sizes)):
            b, c = frame[i][j], frame[j][i]
            assert size * b == sizes[j] * c
            if not b:
                continue
            left = tuple((offsets[i] + v, starts[i][j] + ell)
                         for v in range(size) for ell in range(b))
            right = tuple((offsets[j] + v, starts[j][i] + ell)
                          for v in range(sizes[j]) for ell in range(c))
            factor_lists.append(tuple(tuple(zip(left, perm)) for perm in permutations(right)))
            denominator *= factorial(len(left))
    rows_counter = Counter()
    for factors in product(*factor_lists):
        rows = [[None] * d for _ in range(cursor)]
        for edges in factors:
            for (v, slot), (w, target_slot) in edges:
                rows[v][slot] = w
                rows[w][target_slot] = v
        assert all(all(w is not None for w in row) for row in rows)
        rows_counter[tuple(tuple(row) for row in rows)] += 1
    assert sum(rows_counter.values()) == denominator
    return offsets, rows_counter, denominator


def tables_and_numerator(types, sizes, frame, q):
    k = len(sizes)
    tables = {}
    result = 1
    for i, stars in enumerate(types):
        divisor = 1
        for _, count in stars:
            divisor *= factorial(count)
        assert factorial(sizes[i]) % divisor == 0
        result *= factorial(sizes[i]) // divisor
        offset = 1
        for j in range(k):
            degree = frame[i][j]
            if degree:
                matrix = [[0] * q for _ in range(q)]
                for star, count in stars:
                    for y in star[offset:offset + degree]:
                        matrix[star[0]][y] += count
                tables[i, j] = matrix
            offset += degree
    for (i, j), matrix in tables.items():
        if i == j:
            for x in range(q):
                assert matrix[x][x] % 2 == 0
                result *= pair_count(matrix[x][x])
                for y in range(x + 1, q):
                    assert matrix[x][y] == matrix[y][x]
                    result *= factorial(matrix[x][y])
        elif i < j:
            assert all(matrix[x][y] == tables[j, i][y][x]
                       for x in range(q) for y in range(q))
            for row in matrix:
                for entry in row:
                    result *= factorial(entry)
    return tables, result


@lru_cache(None)
def symmetrized(stars, degrees):
    groups, start = [], 1
    for degree in degrees:
        groups.append(tuple(permutations(range(start, start + degree))))
        start += degree
    result = Counter()
    for star, count in stars:
        for picks in product(*groups):
            permuted = (star[0],) + tuple(star[pos] for group in picks for pos in group)
            result[permuted] += count
    return tuple(sorted(result.items()))


def projection_entropy(stars, positions):
    counts = Counter()
    for star, count in stars:
        counts[tuple(star[pos] for pos in positions)] += count
    return entropy(counts.values())


def check_entropy(types, sizes, frame, tables):
    d = sum(frame[0])
    original = sum(n * entropy([count for _, count in stars])
                   for n, stars in zip(sizes, types))
    symmetric = tuple(symmetrized(stars, tuple(row)) for stars, row in zip(types, frame))
    sym_phi = sum(n * entropy([count for _, count in stars])
                  for n, stars in zip(sizes, symmetric))
    edge_mi_sum = 0.0
    root_entropies = [projection_entropy(stars, (0,)) for stars in symmetric]
    for (i, j), matrix in tables.items():
        if i > j:
            continue
        edges = sizes[i] * frame[i][j] / (2 if i == j else 1)
        pair_h = entropy([entry for row in matrix for entry in row])
        original -= edges * pair_h
        sym_phi -= edges * pair_h
        edge_mi_sum += edges * (root_entropies[i] + root_entropies[j] - pair_h)
    j_sum = 0.0
    max_omit_error = 0.0
    for i, stars in enumerate(symmetric):
        root_h = root_entropies[i]
        star_h = entropy([count for _, count in stars])
        for t in range(1, d + 1):
            retained = (0,) + tuple(s for s in range(1, d + 1) if s != t)
            retained_h = projection_entropy(stars, retained)
            max_omit_error = max(max_omit_error, abs(star_h - retained_h))
            j_it = sum(projection_entropy(stars, (0, s)) - root_h
                       for s in range(1, d + 1) if s != t) - (retained_h - root_h)
            assert j_it >= -1e-10
            j_sum += sizes[i] * j_it / d
    rhs = -(d - 2) * edge_mi_sum / d - j_sum
    residual = abs(sym_phi - rhs)
    assert residual < 1e-9
    assert original <= sym_phi + 1e-9
    assert original <= 1e-9
    assert max_omit_error < 1e-9
    return original, residual, max_omit_error, sym_phi - original


cases = (
    ("simple-K4-lift-size1-odd", (1, 1, 1, 1),
     ((0, 1, 1, 1), (1, 0, 1, 1), (1, 1, 0, 1), (1, 1, 1, 0)), 2),
    ("simple-K4-lift-size2", (2, 2, 2, 2),
     ((0, 1, 1, 1), (1, 0, 1, 1), (1, 1, 0, 1), (1, 1, 1, 0)), 1),
    ("zero-internal-three-cross-stubs", (2, 2), ((0, 3), (3, 0)), 2),
    ("one-internal-two-cross-stubs", (2, 2), ((1, 2), (2, 1)), 2),
    ("unequal-zero-one-internal-small", (1, 1, 2),
     ((0, 1, 2), (1, 0, 2), (1, 1, 1)), 2),
    ("unequal-zero-one-internal", (2, 2, 4),
     ((0, 1, 2), (1, 0, 2), (1, 1, 1)), 1),
    ("internal-cubic-with-loops", (2,), ((3,),), 2),
)

records = []
for name, sizes, frame, r in cases:
    q = 2 ** r
    offsets, configurations_by_rows, denominator = configurations(sizes, frame)
    all_labels = tuple(product(range(q), repeat=sum(sizes)))
    case_summary = {"name": name, "sizes": sizes, "frame": frame,
                    "field": "F_2", "dimension": r,
                    "labeled_configurations": denominator,
                    "distinct_ordered_neighbor_arrays": len(configurations_by_rows),
                    "labelings_per_configuration": len(all_labels), "targets": []}
    for entries in product(range(2), repeat=r*r):
        R = tuple(tuple(entries[i*r:(i+1)*r]) for i in range(r))
        images = []
        for x in range(q):
            image = 0
            for j in range(r):
                image |= (sum(((x >> i) & 1) * R[i][j] for i in range(r)) % 2) << j
            images.append(image)
        observed = Counter()
        for neighbors, multiplicity in configurations_by_rows.items():
            for labels in all_labels:
                valid = True
                for v, adjacent in enumerate(neighbors):
                    value = 0
                    for w in adjacent:
                        value ^= labels[w]
                    if value != images[labels[v]]:
                        valid = False
                        break
                if not valid:
                    continue
                types = []
                for i, n in enumerate(sizes):
                    stars = Counter((labels[v],) + tuple(labels[w] for w in neighbors[v])
                                    for v in range(offsets[i], offsets[i] + n))
                    types.append(tuple(sorted(stars.items())))
                observed[tuple(types)] += multiplicity
        maximum_phi = -float("inf")
        maximum_residual = maximum_omit_error = maximum_entropy_gain = 0.0
        for types, actual_numerator in observed.items():
            tables, predicted_numerator = tables_and_numerator(types, sizes, frame, q)
            assert predicted_numerator == actual_numerator
            phi, residual, omit_error, entropy_gain = check_entropy(types, sizes, frame, tables)
            maximum_phi = max(maximum_phi, phi)
            maximum_residual = max(maximum_residual, residual)
            maximum_omit_error = max(maximum_omit_error, omit_error)
            maximum_entropy_gain = max(maximum_entropy_gain, entropy_gain)
        case_summary["targets"].append({
            "R": R, "compatible_types": len(observed),
            "exact_expected_intertwiners": str(Fraction(sum(observed.values()), denominator)),
            "maximum_original_entropy_exponent": maximum_phi,
            "maximum_identity_residual": maximum_residual,
            "maximum_omission_entropy_error": maximum_omit_error,
            "maximum_symmetrization_entropy_gain": maximum_entropy_gain,
            "status": "PASS"})
    records.append(case_summary)
    print(name, "PASS", flush=True)

report = {"status": "PASS", "scope": "Exhaustive labeled configurations and all binary targets of the stated order; exact integer factorial numerators plus floating entropy identities.",
          "cases": records}
target = Path(__file__).resolve().parent / "all-slot-type-checks.json"
target.write_text(json.dumps(report, indent=2) + "\n")
print("All", sum(len(case["targets"]) for case in records), "target cases passed.")
