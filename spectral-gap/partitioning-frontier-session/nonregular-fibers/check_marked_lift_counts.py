#!/usr/bin/env python3
"""Exact checks for the marked-lift obstruction; no asymptotic inference."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import factorial, lgamma, log
from pathlib import Path
import json


def ordered_pair_partitions(vertices, b):
    if b == 0:
        yield ()
        return
    for pair in combinations(vertices, 2):
        rest = tuple(v for v in vertices if v not in pair)
        for tail in ordered_pair_partitions(rest, b-1):
            yield (pair,) + tail


def toy_counts(r=3, b=3):
    # N=2, with each matching represented by its two possible orientations.
    partitions = list(ordered_pair_partitions(tuple(range(2*b)), b))
    observed_marks = Counter()
    fixed_partition_observations = []
    for pi_index, partition in enumerate(partitions):
        for orientations in product((0, 1), repeat=r*b):
            maps = []
            for i in range(r):
                bitmask = 0
                for j, (u, v) in enumerate(partition):
                    chosen = v if orientations[i*b+j] == 0 else u
                    bitmask |= 1 << chosen
                maps.append(bitmask)
            graph = tuple(maps)
            observed_marks[graph] += 1
            if pi_index == 0:
                fixed_partition_observations.append(graph)
    T = factorial(2*b)*factorial(2)**((r-1)*b)
    U = (factorial(2*b)//factorial(b)**2)**r
    assert sum(observed_marks.values()) == T
    assert len(observed_marks) <= U
    assert all(z % factorial(b) == 0 for z in observed_marks.values())
    # Z counts ordered partitions, while W divides by base-label permutations.
    bayes_success = sum((Fraction(z, T)*Fraction(factorial(b), z)
                         for z in observed_marks.values()), Fraction(0))
    assert bayes_success == Fraction(factorial(b)*len(observed_marks), T)
    assert bayes_success <= Fraction(factorial(b)*U, T)
    mixed_W = Counter()
    for z in observed_marks.values():
        mixed_W[z//factorial(b)] += z
    fixed_W = Counter(observed_marks[g]//factorial(b)
                      for g in fixed_partition_observations)
    # Relabeling-invariance of W makes its fixed-planting law exactly the mixture law.
    assert {w: Fraction(c, T) for w, c in mixed_W.items()} == {
        w: Fraction(c, len(fixed_partition_observations)) for w, c in fixed_W.items()}
    return dict(r=r,b=b,N=2,ordered_marks=T,ambient_observations=U,
                supported_observations=len(observed_marks),
                exact_bayes_success=str(bayes_success),
                success_upper_bound=str(Fraction(factorial(b)*U,T)),
                fixed_vs_mixture_W_distribution="equal",
                W_distribution={str(w):str(Fraction(c,T)) for w,c in sorted(mixed_W.items())})


def main():
    threshold_rows = []
    for r in (3,4,5,6):
        first = None
        for b in range(3,1001):
            positive = factorial(b)**r > b**((r-1)*b)
            if positive:
                first = b
                break
        assert first is not None
        threshold_rows.append(dict(r=r,first_positive_b=first,
                                   gamma=r*lgamma(first+1)-(r-1)*first*log(first)))
    assert threshold_rows[0]['first_positive_b'] == 12
    numerator = factorial(12)**3
    denominator = 12**24
    assert numerator > denominator
    data = dict(status="PASS",scope="Exact finite checks only; the written proof supplies all limits.",
                witness=dict(r=3,b=12,integer_numerator=str(numerator),
                             integer_denominator=str(denominator),
                             ratio=str(Fraction(numerator,denominator)),
                             gamma=3*lgamma(13)-24*log(12)),
                thresholds=threshold_rows,toy=toy_counts())
    dest=Path(__file__).with_name('marked-lift-count-checks.json')
    dest.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(dict(status=data['status'],thresholds=threshold_rows,
                          toy_marks=data['toy']['ordered_marks'],
                          toy_observations=data['toy']['supported_observations'],
                          output=str(dest))))


if __name__=='__main__':
    main()
