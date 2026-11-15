"""Exhaustive labeled-configuration check of the exact star-type formula."""
from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import factorial, log
from pathlib import Path
import json


def pairings(items):
    if not items:
        yield ()
        return
    first, rest = items[0], items[1:]
    for j, other in enumerate(rest):
        for tail in pairings(rest[:j] + rest[j + 1 :]):
            yield ((first, other),) + tail


def pair_count(n):
    assert n % 2 == 0
    return factorial(n) // (2 ** (n // 2) * factorial(n // 2))


def internal_neighbors(n, degree):
    result = []
    for pairing in pairings(tuple(range(n * degree))):
        partner = [None] * (n * degree)
        for i, j in pairing:
            partner[i], partner[j] = j // degree, i // degree
        result.append(tuple(tuple(partner[v * degree : (v + 1) * degree]) for v in range(n)))
    return result


def cross_neighbors(n1, n2, b1, b2):
    assert n1 * b1 == n2 * b2
    result = []
    for perm in permutations(range(n1 * b1)):
        left = [None] * (n1 * b1)
        right = [None] * (n2 * b2)
        for i, j in enumerate(perm):
            left[i], right[j] = n1 + j // b2, i // b1
        result.append((tuple(tuple(left[v * b1 : (v + 1) * b1]) for v in range(n1)),
                       tuple(tuple(right[v * b2 : (v + 1) * b2]) for v in range(n2))))
    return result


def entropy(counts):
    total = sum(counts)
    return -sum(float(Fraction(x, total)) * log(float(Fraction(x, total))) for x in counts if x)


records = []
for n1, n2, a, b1, b2, r, R in (
    (2, 2, 2, 1, 1, 2, ((0, 1), (1, 1))),
    (2, 2, 2, 1, 1, 2, ((0, 0), (0, 0))),
    (2, 2, 2, 1, 1, 2, ((1, 0), (0, 1))),
    (2, 2, 2, 1, 1, 2, ((1, 1), (0, 1))),
    (3, 3, 2, 1, 1, 1, ((1,),)),
    (2, 4, 2, 2, 1, 1, ((0,),)),
    (2, 4, 2, 2, 1, 1, ((1,),)),
):
    q = 2 ** r
    lookup = []
    for x in range(q):
        image = 0
        for j in range(r):
            bit = sum(((x >> i) & 1) * R[i][j] for i in range(r)) % 2
            image |= bit << j
        lookup.append(image)
    configurations = []
    for internal1, internal2, (cross1, cross2) in product(
            internal_neighbors(n1, a), internal_neighbors(n2, a), cross_neighbors(n1, n2, b1, b2)):
        rows = tuple(internal1[v] + cross1[v] for v in range(n1))
        rows += tuple(tuple(n1 + w for w in internal2[v]) + cross2[v] for v in range(n2))
        configurations.append(rows)
    denominator = pair_count(n1 * a) * pair_count(n2 * a) * factorial(n1 * b1)
    assert len(configurations) == denominator
    observed = Counter()
    for labels in product(range(q), repeat=n1 + n2):
        for neighbors in configurations:
            valid = True
            for v, adjacent in enumerate(neighbors):
                value = 0
                for w in adjacent:
                    value ^= labels[w]
                if value != lookup[labels[v]]:
                    valid = False
                    break
            if not valid:
                continue
            types = []
            for vertices in (range(n1), range(n1, n1 + n2)):
                stars = Counter((labels[v],) + tuple(labels[w] for w in neighbors[v]) for v in vertices)
                types.append(tuple(sorted(stars.items())))
            observed[tuple(types)] += 1

    maximal_phi = -float("inf")
    for types, actual_count in observed.items():
        predicted = 1
        internal_pairs, cross_pairs = [], []
        star_entropy = 0
        for size, cross_degree, stars in zip((n1, n2), (b1, b2), types):
            divisor = 1
            im = [[0] * q for _ in range(q)]
            cm = [[0] * q for _ in range(q)]
            for star, multiplicity in stars:
                divisor *= factorial(multiplicity)
                for label in star[1 : 1 + a]:
                    im[star[0]][label] += multiplicity
                for label in star[1 + a :]:
                    cm[star[0]][label] += multiplicity
            assert factorial(size) % divisor == 0
            predicted *= factorial(size) // divisor
            for x in range(q):
                assert im[x][x] % 2 == 0
                predicted *= pair_count(im[x][x])
                for y in range(x + 1, q):
                    assert im[x][y] == im[y][x]
                    predicted *= factorial(im[x][y])
            internal_pairs.append(im)
            cross_pairs.append(cm)
            star_entropy += size * entropy([count for _, count in stars])
        assert all(cross_pairs[0][x][y] == cross_pairs[1][y][x] for x in range(q) for y in range(q))
        for row in cross_pairs[0]:
            for entry in row:
                predicted *= factorial(entry)
        assert predicted == actual_count
        phi = star_entropy
        for size, matrix in zip((n1, n2), internal_pairs):
            phi -= size * a / 2 * entropy([x for row in matrix for x in row])
        phi -= n1 * b1 * entropy([x for row in cross_pairs[0] for x in row])
        assert phi <= 1e-10
        maximal_phi = max(maximal_phi, phi)
    moment = Fraction(sum(observed.values()), denominator)
    records.append({"sizes": [n1, n2], "internal_degree": a, "cross_degrees": [b1, b2],
                    "field": "F_2", "vector_dimension": r, "R": R,
                    "configurations": denominator, "labelings": q ** (n1 + n2),
                    "realized_compatible_types": len(observed),
                    "exact_expected_intertwiners": str(moment),
                    "maximum_type_entropy_phi": maximal_phi, "status": "PASS"})

report = {"records": records,
          "scope": "Exact star-type factorial checks on all labeled configurations, retaining loops and parallel edges."}
target = Path(__file__).resolve().parent / "exact-type-checks.json"
target.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
