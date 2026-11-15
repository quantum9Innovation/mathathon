"""Independent exact enumeration of the p=3 configuration moment, N<=3.

Only the standard library is used.  The first count enumerates all pairs
of stub pairings and computes their modular nullities.  The second count
enumerates unordered profile multisets and uses the proposed type formula.
Both return the integer sum of kernel sizes over all pairing pairs.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, product
from math import factorial, prod


def pairings(stubs):
    if not stubs:
        yield ()
        return
    a = stubs[0]
    for j in range(1, len(stubs)):
        b = stubs[j]
        remainder = stubs[1:j] + stubs[j + 1 :]
        for rest in pairings(remainder):
            yield ((a, b),) + rest


def adjacency(n, pairing):
    matrix = [[0] * n for _ in range(n)]
    for a, b in pairing:
        u, v = a // 2, b // 2
        matrix[u][v] += 1
        matrix[v][u] += 1
    return matrix


def rank_mod3(matrix):
    a = [[entry % 3 for entry in row] for row in matrix]
    rank = 0
    for column in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a)) if a[i][column]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inverse = 1 if a[rank][column] == 1 else 2
        a[rank] = [(inverse * entry) % 3 for entry in a[rank]]
        for i in range(rank + 1, len(a)):
            coefficient = a[i][column]
            a[i] = [(x - coefficient * y) % 3 for x, y in zip(a[i], a[rank])]
        rank += 1
    return rank


def direct_pairing_sum(n):
    matrices = [adjacency(n, pairing) for pairing in pairings(tuple(range(2 * n)))]
    total = 0
    for plus, minus in product(matrices, repeat=2):
        matrix = [[0] * (2 * n) for _ in range(2 * n)]
        for i, j in product(range(n), repeat=2):
            matrix[i][j] = plus[i][j] - (i == j)
            matrix[n + i][n + j] = minus[i][j] - (i == j)
        for i in range(n):
            matrix[i][n + i] = matrix[n + i][i] = -1
        total += 3 ** (2 * n - rank_mod3(matrix))
    return total, len(matrices) ** 2


def compatible_pairings(table):
    answer = 1
    for u in range(3):
        if table[u][u] % 2:
            return 0
        diagonal = table[u][u]
        answer *= factorial(diagonal) // (2 ** (diagonal // 2) * factorial(diagonal // 2))
        for v in range(u + 1, 3):
            if table[u][v] != table[v][u]:
                return 0
            answer *= factorial(table[u][v])
    return answer


def type_formula_sum(n):
    profiles = list(product(range(3), repeat=4))
    total = 0
    for indices in combinations_with_replacement(range(len(profiles)), n):
        plus = [[0] * 3 for _ in range(3)]
        minus = [[0] * 3 for _ in range(3)]
        for index in indices:
            a, d, b, e = profiles[index]
            c, f = (a + d - b) % 3, (a + d - e) % 3
            plus[a][b] += 1
            plus[a][c] += 1
            minus[d][e] += 1
            minus[d][f] += 1
        multiplicity = factorial(n) // prod(factorial(v) for v in Counter(indices).values())
        total += multiplicity * compatible_pairings(plus) * compatible_pairings(minus)
    return total


if __name__ == "__main__":
    for n in range(1, 4):
        direct, denominator = direct_pairing_sum(n)
        by_type = type_formula_sum(n)
        assert direct == by_type, (n, direct, by_type)
        print(f"N={n}: pairing sum={direct}, type sum={by_type}, E|ker|={Fraction(direct, denominator)}")
