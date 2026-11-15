#!/usr/bin/env python3
"""Exact covariance-map and contrast-subspace checks, standard library only.

The identities are proved in matmul/balanced-variance-and-birthday.txt.
Finite enumeration is corroboration and does not establish a general
concentration theorem or an improvement over other sketches.
"""

from fractions import Fraction as F
from itertools import combinations, permutations, product
import json

from check_balanced_permutation_amm import partitions, multiply


def transpose(a):
    return list(map(list, zip(*a)))


def outer(x, y=None):
    if y is None:
        y = x
    return [[u*v for v in y] for u in x]


def add(a, b):
    return [[u+v for u, v in zip(x, y)] for x, y in zip(a, b)]


def scale(a, x):
    return [[x*v for v in row] for row in a]


def exact_t_numerators(m, s):
    q = m//s
    for partition in partitions(tuple(range(m)), q):
        bucket = {v: b for b, block in enumerate(partition) for v in block}
        yield [[0 if i == j else (m-1)*int(bucket[i] == bucket[j])-(q-1)
                for j in range(m)] for i in range(m)]


def covariance_case(m, s):
    q, c = m//s, F(m-s, s-1)
    v = c/m
    u, w = -v/(m-2), 2*v/((m-2)*(m-3))
    aa, bb, kk = v-2*u+2*w, v-2*u+w, 2*(v-4*u+3*w)
    pi = [[int(i == j)-F(1, m) for j in range(m)] for i in range(m)]
    ts = list(exact_t_numerators(m, s))
    denominator = len(ts)*(m-q)**2
    basis = []
    for i in range(m-1):
        x = [int(j == i)-int(j == m-1) for j in range(m)]
        basis.append(x)
    # These rank-one matrices span all symmetric matrices with zero row sums.
    vectors = basis + [[x+y for x, y in zip(basis[i], basis[j])]
                       for i, j in combinations(range(m-1), 2)]
    for vector in vectors:
        g = outer(vector)
        diagonal = [[g[i][i] if i == j else 0 for j in range(m)]
                    for i in range(m)]
        expected = add(add(scale(g, aa), scale(pi, bb*sum(x*x for x in vector))),
                       scale(multiply(multiply(pi, diagonal), pi), -kk))
        total = [[0]*m for _ in range(m)]
        for t in ts:
            image = [sum(a*b for a, b in zip(row, vector)) for row in t]
            total = add(total, outer(image))
        actual = scale(total, F(1, denominator))
        assert actual == expected, (m, s, "full covariance map", vector)

    projected_ranks = []
    tau = 2*c*F(m-1, m*(m-3))
    for rank in range(1, m//2+1):
        # Columns of V are disjoint coordinate contrasts. U=V/sqrt(2).
        columns = [[int(i == 2*j)-int(i == 2*j+1) for i in range(m)]
                   for j in range(rank)]
        vv = transpose(columns)
        total = [[0]*rank for _ in range(rank)]
        for t in ts:
            x = multiply(multiply(columns, t), vv)
            total = add(total, multiply(x, x))
        actual = scale(total, F(1, 4*denominator))
        scalar = tau/2*(rank+1+F(2, (m-1)*(m-2)))-tau*F(m, 2*(m-2))
        expected = [[scalar*int(i == j) for j in range(rank)]
                    for i in range(rank)]
        assert actual == expected, (m, s, "projected operator covariance", rank)
        projected_ranks.append(rank)

    a = [[int(j == 0)-int(j == m-1) for j in range(m)],
         [int(j == 1)+int(j == 2)-2*int(j == m-1) for j in range(m)]]
    b = transpose([[int(j == 0)+2*int(j == 1)-3*int(j == m-1)
                    for j in range(m)],
                   [int(j == 2)-int(j == m-2) for j in range(m)]])
    cc = multiply(a, b)
    g = multiply(b, transpose(b))
    diagonal = [[g[i][i] if i == j else 0 for j in range(m)]
                for i in range(m)]
    expected = add(add(scale(multiply(cc, transpose(cc)), aa),
                       scale(multiply(a, transpose(a)), bb*sum(g[i][i] for i in range(m)))),
                   scale(multiply(multiply(a, diagonal), transpose(a)), -kk))
    total = [[0]*len(a) for _ in a]
    for t in ts:
        z = multiply(multiply(a, t), b)
        total = add(total, multiply(z, transpose(z)))
    assert scale(total, F(1, denominator)) == expected, (m, s, "AMM left variance")
    return dict(m=m, s=s, partitions=len(ts), spanning_rank_one_tests=len(vectors),
                projected_operator_ranks=projected_ranks, amm_variance="PASS")


def determinant(a):
    n = len(a)
    total = 0
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i in range(n) for j in range(i+1, n))
        term = (-1)**inversions
        for i, j in enumerate(perm):
            term *= a[i][j]
        total += term
    return total


def positive_semidefinite(a):
    n = len(a)
    for size in range(1, n+1):
        for indices in combinations(range(n), size):
            minor = [[a[i][j] for j in indices] for i in indices]
            if determinant(minor) < 0:
                return False
    return True


def falling(a, n):
    answer = 1
    for j in range(n):
        answer *= a-j
    return answer


def birthday_case(m, s, degree, selected, epsilon):
    q, p = m//s, F(m//s-1, m-1)
    assert p/(1-p) <= epsilon
    assert F(1, degree) > p+epsilon*(1-p)
    ts = list(exact_t_numerators(m, s))
    rank = selected-1
    columns = [[int(i == j)-int(i == selected-1) for i in range(m)]
               for j in range(rank)]
    basis = transpose(columns)
    gram = multiply(columns, basis)
    restricted = [multiply(multiply(columns, t), basis) for t in ts]
    success = 0
    count = 0
    factor = F(1, degree*(m-q))
    for indices in product(range(len(ts)), repeat=degree):
        total = [[0]*rank for _ in range(rank)]
        no_collisions = True
        for index in indices:
            total = add(total, restricted[index])
            no_collisions &= all(ts[index][i][j] != m-q
                                 for i in range(selected) for j in range(i+1, selected))
        distortion = scale(total, factor)
        upper = add(scale(gram, epsilon), scale(distortion, -1))
        lower = add(scale(gram, epsilon), distortion)
        actual_success = positive_semidefinite(upper) and positive_semidefinite(lower)
        assert actual_success == no_collisions, (m, s, degree, selected, indices)
        success += actual_success
        count += 1
    expected = F(falling(s, selected)*q**selected, falling(m, selected))**degree
    actual = F(success, count)
    assert actual == expected, (m, s, degree, selected, actual, expected)
    return dict(m=m, s=s, d=degree, selected_coordinates=selected,
                epsilon=str(epsilon), partition_tuples=count, success_probability=str(actual))


def main():
    covariance = [covariance_case(m, s) for m, s in
                  [(4, 2), (4, 4), (6, 2), (6, 3), (6, 6), (8, 2), (8, 4), (8, 8)]]
    birthday = [birthday_case(*case) for case in
                [(4, 2, 1, 2, F(1, 2)), (4, 2, 1, 3, F(1, 2)),
                 (6, 3, 1, 3, F(1, 3)), (6, 3, 2, 3, F(1, 3)),
                 (8, 4, 1, 4, F(1, 4)), (8, 4, 2, 3, F(1, 4))]]
    print(json.dumps(dict(status="all exact assertions passed", covariance=covariance,
                         birthday=birthday,
                         scope="finite corroboration of exact formulas, not a concentration breakthrough"),
                     indent=2))


if __name__ == "__main__":
    main()
