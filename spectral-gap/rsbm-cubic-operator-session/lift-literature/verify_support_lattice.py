"""Independently compute the support-difference lattice index by integer HNF.

Coordinates delete the last entry of each zero-total table, identifying
the fixed-total integer difference lattice with Z^{2(p^2-1)}. Thus the
absolute determinant of the column HNF is the exact index in that lattice.
"""

from itertools import product
import sys

from sympy import Matrix, zeros
from sympy.matrices.normalforms import hermite_normal_form


def profile(p, a, d, b, e):
    c, f = (a + d - b) % p, (a + d - e) % p
    plus, minus = [0] * (p * p), [0] * (p * p)
    plus[a * p + b] += 1
    plus[a * p + c] += 1
    minus[d * p + e] += 1
    minus[d * p + f] += 1
    return plus[:-1] + minus[:-1]


def rank_mod(matrix, prime):
    rows = [[int(x) % prime for x in row] for row in matrix.tolist()]
    rank = 0
    for column in range(matrix.cols):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inverse = pow(rows[rank][column], -1, prime)
        rows[rank] = [(x * inverse) % prime for x in rows[rank]]
        for index in range(rank + 1, len(rows)):
            factor = rows[index][column]
            if factor:
                rows[index] = [
                    (x - factor * y) % prime
                    for x, y in zip(rows[index], rows[rank])
                ]
        rank += 1
    return rank


def symmetric_total_zero_basis(p):
    columns = []
    for a in range(p - 1):
        table = [0] * (p * p)
        table[a * p + a] = 1
        table[-1] = -1
        columns.append(table)
    for a in range(p):
        for b in range(a + 1, p):
            table = [0] * (p * p)
            table[a * p + b] = table[b * p + a] = 1
            table[-1] = -2
            columns.append(table)
    return Matrix.hstack(*(Matrix(column) for column in columns))


def check(p):
    origin = profile(p, 0, 0, 0, 0)
    columns = []
    for a, d, b, e in product(range(p), repeat=4):
        current = profile(p, a, d, b, e)
        columns.append([u - v for u, v in zip(current, origin)])
    support = Matrix.hstack(*(Matrix(column) for column in columns))
    hnf = hermite_normal_form(support)
    assert hnf.rows == hnf.cols == 2 * (p * p - 1)
    actual = abs(int(hnf.det()))
    expected = (2 ** (2 * p - 2)) * p**3
    assert actual == expected, (p, actual, expected)
    print(f"p={p}: rank={hnf.rows}, index={actual}, expected={expected}, agree=True")

    # Independently intersect the computed HNF lattice with symmetry and
    # even diagonal; do not invoke the manuscript's congruence formula.
    block = symmetric_total_zero_basis(p)
    pair_full = Matrix.diag(block, block)
    keep = list(range(p * p - 1)) + list(range(p * p, 2 * p * p - 1))
    pair_reduced = pair_full.extract(keep, range(pair_full.cols))
    denominator = 2 * p
    membership = denominator * hnf.inv() * pair_reduced
    assert all(value.q == 1 for value in membership)
    diagonal_rows = [a * p + a for a in range(p)] + [
        p * p + a * p + a for a in range(p)
    ]
    # p times a diagonal coordinate is 0 modulo 2p iff that coordinate
    # is even; modulo p this additional condition vanishes.
    diagonals = p * pair_full.extract(diagonal_rows, range(pair_full.cols))
    conditions = membership.col_join(diagonals)
    rank_two, rank_p = rank_mod(conditions, 2), rank_mod(conditions, p)
    expected_two, expected_p = 4 * p - 4, 2
    assert (rank_two, rank_p) == (expected_two, expected_p)
    print(
        f"p={p}: symmetric/even-diagonal intersection index="
        f"2^{rank_two} * {p}^{rank_p}, agree=True"
    )


if __name__ == "__main__":
    for prime in map(int, sys.argv[1:] or (3, 5)):
        check(prime)
