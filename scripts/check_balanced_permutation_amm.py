#!/usr/bin/env python3
"""Exact finite checks for balanced-permutation-amm.txt; standard library only.

Enumerates unlabeled equal-size set partitions. Every such partition has
the same number s! (q!)^s of inducing permutations, so this computes the
same averages as a uniform permutation. No embedding theorem is tested.
"""

from fractions import Fraction as F
from itertools import combinations
import json


def partitions(items, q):
    if not items:
        yield ()
        return
    first, remaining = items[0], items[1:]
    for chosen in combinations(remaining, q-1):
        block = (first,) + chosen
        rest = tuple(x for x in remaining if x not in chosen)
        for tail in partitions(rest, q):
            yield (block,) + tail


def multiply(a, b):
    return [[sum(x*y for x, y in zip(row, column))
             for column in zip(*b)] for row in a]


def quadratic(a, v):
    return sum(v[i]*a[i][j]*v[j] for i in range(len(v)) for j in range(len(v)))


def check(m, s):
    q, p = m//s, F(m//s-1, m-1)
    denominator, lam, coefficient = m-q, F(m-1, s-1), F(m-s, s-1)
    sum_t, sum_t2 = [[0]*m for _ in range(m)], [[0]*m for _ in range(m)]
    vectors = [tuple([1, -1]+[0]*(m-2)),
               tuple([1]*(m//2)+[-1]*(m//2)),
               tuple([1]*(m-1)+[-(m-1)])]
    sums_z, sums_z2 = [0]*len(vectors), [0]*len(vectors)
    gram_variance_numerators = [0]*(m-1)
    count, collisions = 0, 0
    for partition in partitions(tuple(range(m)), q):
        bucket = {v: i for i, block in enumerate(partition) for v in block}
        t = [[0 if i == j else ((m-1)*int(bucket[i] == bucket[j])-(q-1))
              for j in range(m)] for i in range(m)]
        assert all(sum(row) == 0 for row in t), (m, s, "T1")
        t2 = multiply(t, t)
        # From W=J0+lambda Pi_H and T=W-I:
        # T^2=(lambda-2)T+(lambda-1)Pi0.
        for i in range(m):
            for j in range(m):
                expected = (lam-2)*F(t[i][j], denominator)
                expected += (lam-1)*(int(i == j)-F(1, m))
                assert F(t2[i][j], denominator**2) == expected, (m, s, "projection polynomial")
                sum_t[i][j] += t[i][j]
                sum_t2[i][j] += t2[i][j]
        for k, vector in enumerate(vectors):
            znum = quadratic(t, vector)
            sums_z[k] += znum
            sums_z2[k] += znum*znum
        for rank in range(1, m):
            # P projects onto zero-sum vectors in the first rank+1 coordinates.
            # Its entries are integer multiples of 1/(rank+1); no square
            # roots or numerical orthonormal basis are required.
            pnum = [[((rank+1)*int(i == j)-1)
                     if i <= rank and j <= rank else 0
                     for j in range(m)] for i in range(m)]
            tp = multiply(t, pnum)
            gram_variance_numerators[rank-1] += sum(
                tp[i][j]*tp[j][i] for i in range(m) for j in range(m))
        count += 1
        collisions += bucket[0] == bucket[1]
    assert all(value == 0 for row in sum_t for value in row), (m, s, "EW")
    for i in range(m):
        for j in range(m):
            actual = F(sum_t2[i][j], count*denominator**2)
            expected = coefficient*(int(i == j)-F(1, m))
            assert actual == expected, (m, s, "covariance", i, j, actual, expected)
    assert F(collisions, count) == p, (m, s, "collision probability")
    r3 = F((q-1)*(q-2), (m-1)*(m-2))
    r22 = p*F((q-2)*(q-3)+(m-q)*(q-1), (m-2)*(m-3))
    variances = []
    for k, vector in enumerate(vectors):
        norm2 = sum(x*x for x in vector)
        t4 = F(sum(x**4 for x in vector), norm2**2)
        expected = (2*p*(1-t4)+8*r3*(t4-F(1, 2))+r22*(3-6*t4)-p*p)/(1-p)**2
        actual = F(sums_z2[k], count*denominator**2*norm2**2)
        assert sums_z[k] == 0 and actual == expected, (m, s, "quadratic variance", k, actual, expected)
        variances.append(str(actual))
    tau = 2*coefficient*F(m-1, m*(m-3))
    gram_variances = []
    for rank in range(1, m):
        leverage_square_sum = F(rank*rank, rank+1)
        expected = tau/2*(rank*(rank+1)+F(2*rank, (m-1)*(m-2))
                          -F(2*m, m-2)*leverage_square_sum)
        actual = F(gram_variance_numerators[rank-1],
                   count*denominator**2*(rank+1)**2)
        assert actual == expected, (m, s, "projected Gram variance", rank, actual, expected)
        gram_variances.append(str(actual))
    return dict(m=m, s=s, q=q, partitions=count, collision_probability=str(p),
                covariance_coefficient=str(coefficient),
                unit_vector_quadratic_variances_contrast_balanced_spiked=variances,
                projected_gram_frobenius_variances_by_rank=gram_variances)


if __name__ == "__main__":
    cases = [(4, 2), (4, 4), (6, 2), (6, 3), (6, 6), (8, 2), (8, 4), (8, 8)]
    rows = [check(m, s) for m, s in cases]
    print(json.dumps(dict(status="all exact assertions passed", cases=rows,
                         scope="finite algebra checks; no embedding width or priority theorem"), indent=2))
