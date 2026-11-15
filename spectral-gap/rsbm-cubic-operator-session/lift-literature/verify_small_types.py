"""Independent exact finite-N check of the F_2 type formula.

One side enumerates all pairs of stub pairings and computes matrix rank.
The other enumerates profile count vectors and applies the factorial formula.
This is validation of the count, not a substitute for its proof.
"""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import factorial


def pairings(items):
    if not items:
        yield ()
        return
    first = items[0]
    for index in range(1, len(items)):
        second = items[index]
        rest = items[1:index] + items[index + 1 :]
        for tail in pairings(rest):
            yield ((first, second),) + tail


def adjacency_multiplicities(n):
    counts = Counter()
    for edges in pairings(tuple(range(2 * n))):
        rows = [0] * n
        for stub, other in edges:
            u, v = stub // 2, other // 2
            rows[u] ^= 1 << v
            rows[v] ^= 1 << u
        counts[tuple(rows)] += 1
    return counts


def rank_f2(rows):
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot in pivots:
                row ^= pivots[pivot]
            else:
                pivots[pivot] = row
                break
    return len(pivots)


def direct_moment(n):
    matrices = adjacency_multiplicities(n)
    numerator = 0
    for left, left_count in matrices.items():
        for right, right_count in matrices.items():
            rows = [
                left[i] ^ (1 << i) ^ (1 << (n + i)) for i in range(n)
            ] + [
                (right[i] << n) ^ (1 << i) ^ (1 << (n + i))
                for i in range(n)
            ]
            nullity = 2 * n - rank_f2(rows)
            numerator += left_count * right_count * (1 << nullity)
    denominator = sum(matrices.values()) ** 2
    return Fraction(numerator, denominator)


def compositions(total, slots):
    if slots == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in compositions(total - first, slots - 1):
            yield (first,) + tail


def odd_double_factorial(k):
    answer = 1
    for j in range(1, k + 1, 2):
        answer *= j
    return answer


def table_weight(table):
    if table[0][1] != table[1][0]:
        return 0
    if table[0][0] % 2 or table[1][1] % 2:
        return 0
    return (
        factorial(table[0][1])
        * odd_double_factorial(table[0][0] - 1)
        * odd_double_factorial(table[1][1] - 1)
    )


def type_moment(n):
    profiles = tuple(product(range(2), repeat=4))
    numerator = 0
    for counts in compositions(n, len(profiles)):
        plus = [[0, 0], [0, 0]]
        minus = [[0, 0], [0, 0]]
        multinomial = factorial(n)
        for count, (a, d, b, e) in zip(counts, profiles):
            multinomial //= factorial(count)
            if count:
                c, f = a ^ d ^ b, a ^ d ^ e
                plus[a][b] += count
                plus[a][c] += count
                minus[d][e] += count
                minus[d][f] += count
        numerator += multinomial * table_weight(plus) * table_weight(minus)
    denominator = odd_double_factorial(2 * n - 1) ** 2
    return Fraction(numerator, denominator)


if __name__ == "__main__":
    for n in range(1, 5):
        direct, types = direct_moment(n), type_moment(n)
        assert direct == types, (n, direct, types)
        print(f"N={n}: direct={direct}, type_formula={types}, agree=True")
