from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import random


HERE = Path(__file__).resolve().parent
PACKET = HERE.parent / "mixed-two-conflict"


@lru_cache(None)
def permutations_of(n):
    return tuple(permutations(range(n)))


def falling(n, j):
    return factorial(n) // factorial(n - j)


@lru_cache(None)
def polynomial(n, j, s):
    if j == 0:
        return 1
    return sum(
        comb(j - 1, ell - 1)
        * ((ell - 1) * n + s)
        * factorial(ell - 1)
        * polynomial(n, j - ell, s)
        for ell in range(1, j + 1)
    )


def kernel(n, j, s):
    return Fraction(n**s * polynomial(n, j, s), falling(n, j + s))


def direct(n, pattern):
    answer = Fraction(1)
    for color in sorted({cell[0] for cell in pattern}):
        cells = [cell for cell in pattern if cell[0] == color]
        exponent = sum(cell[3] for cell in cells)
        total = 0
        for sigma in permutations_of(n):
            value = 1
            for _, row, col, p, q in cells:
                indicator = int(sigma[row] == col)
                if q and not indicator:
                    value = 0
                    break
                value *= (n * indicator - 1) ** p
            total += value
        answer *= Fraction(total, factorial(n) * n**exponent)
    return answer


def conflict(left, right):
    return left[:3] != right[:3] and left[0] == right[0] and (
        left[1] == right[1] or left[2] == right[2]
    )


def split(pattern):
    consistent = []
    inconsistent = []
    for cell in pattern:
        if cell[3:] != (1, 0):
            continue
        target = inconsistent if any(conflict(cell, other) for other in pattern) else consistent
        target.append(cell)
    return consistent, inconsistent


def bound(n, a, h, b):
    r = a - h - 2
    return Fraction(2 ** (b - 2), n**a) * (
        2 * kernel(n, h, r + 1) - kernel(n, h, r)
    )


counts = Counter()
examples = {}


def selected_supports(n, pattern, consistent, inconsistent):
    e, f = inconsistent[:2]
    retained = [e, f] + consistent
    remainder = [cell for cell in pattern if cell not in retained]
    h, r = len(consistent), len(remainder)
    B = 2 * kernel(n, h, r + 1) - kernel(n, h, r)
    for flags in product([0, 1], repeat=r):
        selected = [cell for cell, flag in zip(remainder, flags) if flag]
        original = retained + [(*cell[:3], 0, 1) for cell in selected]
        actual = direct(n, original)
        assert abs(actual) <= Fraction(B, n ** (h + 2 + len(selected)))
        if any(conflict(left, right) for left, right in combinations(selected, 2)):
            case = "incompatible"
        else:
            forced = [any(conflict(cell, other) for other in selected) for cell in [e, f]]
            if all(forced):
                case = "both_forced"
            elif any(forced):
                case = "one_forced"
            elif conflict(e, f):
                case = "unforced_pair_conflict"
            else:
                case = "unforced_pair_compatible"
                assert len(selected) <= r - 1
        counts["selected_" + case] += 1
        examples.setdefault(case, {
            "n": n,
            "full_pattern": pattern,
            "retained": [e, f],
            "selected": selected,
            "direct_value": str(actual),
            "selected_bound": str(Fraction(B, n ** (h + 2 + len(selected)))),
        })


def check(n, pattern, family, with_selected=False):
    consistent, inconsistent = split(pattern)
    h, b = len(consistent), len(inconsistent)
    if b < 2:
        return
    actual = direct(n, pattern)
    expected = bound(n, len(pattern), h, b)
    assert abs(actual) <= expected, (n, pattern, actual, expected)
    counts[family + ("_b2" if b == 2 else "_b_above2")] += 1
    counts["original_product_total"] += 1
    counts["endpoint_a_n"] += int(len(pattern) == n)
    counts["multiple_colors"] += int(len({cell[0] for cell in pattern}) > 1)
    counts["repeated_or_mixed_powers"] += int(any(p >= 2 or (p and q) for _, _, _, p, q in pattern))
    if with_selected:
        selected_supports(n, pattern, consistent, inconsistent)


choices = [(0, 1), (1, 0), (2, 0), (3, 0), (1, 2)]
for n in [2, 3]:
    cells = list(product(range(2), range(n), range(n)))
    for a in range(2, n + 1):
        for support in combinations(cells, a):
            for exponents in product(choices, repeat=a):
                pattern = [(*cell, *exponent) for cell, exponent in zip(support, exponents)]
                check(n, pattern, "exhaustive_two_colors", True)

for n in [4]:
    cells = list(product(range(1), range(n), range(n)))
    for a in range(2, n + 1):
        for support in combinations(cells, a):
            for exponents in product([(0, 1), (1, 0)], repeat=a):
                pattern = [(*cell, *exponent) for cell, exponent in zip(support, exponents)]
                check(n, pattern, "exhaustive_one_color_n4", True)

rng = random.Random(942081)
rich_choices = choices + [(5, 0), (7, 0), (2, 3), (4, 1), (0, 4)]
for n, trials in [(5, 2400), (6, 1800)]:
    cells = list(product(range(3), range(n), range(n)))
    for _ in range(trials):
        a = rng.randint(2, n)
        support = rng.sample(cells, a)
        exponents = [rng.choice(rich_choices) for _ in range(a)]
        pattern = [(*cell, *exponent) for cell, exponent in zip(support, exponents)]
        check(n, pattern, "sampled_three_colors", True)

for n in range(2, 9):
    for a in range(2, n + 1):
        for h in range(a - 1):
            r = a - h - 2
            pattern = [(0, 0, 0, 1, 0), (0, 0, 1, 1, 0)]
            pattern += [(0, i, i + 1, 0, 1) for i in range(1, r + 1)]
            pattern += [(0, i, i + 1, 1, 0) for i in range(r + 1, a - 1)]
            consistent, inconsistent = split(pattern)
            assert (len(consistent), len(inconsistent)) == (h, 2)
            actual = direct(n, pattern)
            expected = bound(n, a, h, 2)
            assert actual == -expected, (n, a, h, actual, expected)
            counts["direct_attainment"] += 1

special_patterns = [
    (3, [(0, 0, 0, 1, 0), (0, 1, 1, 1, 0), (0, 0, 1, 0, 1)]),
    (4, [(0, 0, 0, 1, 0), (1, 0, 0, 1, 0), (0, 0, 1, 0, 1), (1, 0, 1, 0, 1)]),
    (4, [(0, 0, 0, 1, 0), (0, 0, 1, 1, 0), (0, 0, 2, 0, 1), (0, 3, 3, 1, 0)]),
]
for n, pattern in special_patterns:
    check(n, pattern, "targeted_shared_neighbor_and_colors", True)

manifest_path = PACKET / "MANIFEST-v1.json"
manifest = json.loads(manifest_path.read_text())
verified = []
for entry in manifest["inputs"] + manifest["outputs"]:
    path = PACKET / entry["path"]
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    assert actual == entry["sha256"], (path, actual)
    verified.append({"path": str(path.relative_to(HERE.parent.parent)), "sha256": actual})

result = {
    "status": "all checks passed",
    "method": "Exact original products evaluated over every permutation within each color, then multiplied across independent colors",
    "author_checker_read_or_imported": False,
    "parent_checker_read_or_imported": False,
    "sample_seed": 942081,
    "counts": dict(counts),
    "selected_case_examples": examples,
    "verified_packet_entries": verified,
    "packet_manifest_sha256": hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
    "integration_candidate_sha256": hashlib.sha256((PACKET / "integration-candidate-v1.tex").read_bytes()).hexdigest(),
}
(HERE / "two-conflict-v1-check-results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"status": result["status"], "counts": result["counts"]}, indent=2))
