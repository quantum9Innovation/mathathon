#!/usr/bin/env python3
"""Exact finite counting corroboration for d=4,p=3, including odd n.

Counts all configuration types using integer row generating coefficients.
This checks the all-target interface and factor p, not the asymptotic proof.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import factorial
from pathlib import Path
import json
import sys

D = int(sys.argv[1]) if len(sys.argv)>1 else 4
assert D in (3,4)
P = 3
ROOT = Path(__file__).resolve().parent

polys = []
for t in range(P):
    poly = Counter()
    for prefix in product(range(P), repeat=D-1):
        word = prefix + ((t-sum(prefix)) % P,)
        poly[(word.count(1), word.count(2))] += 1
    assert sum(poly.values()) == P**(D-1)
    polys.append(poly)

@lru_cache(None)
def rowcoeff(target_counts):
    out = {(0,0): 1}
    for t, count in enumerate(target_counts):
        for _ in range(count):
            nxt = defaultdict(int)
            for (a,b), c in out.items():
                for (da,db), mult in polys[t].items():
                    nxt[(a+da,b+db)] += c*mult
            out = nxt
    assert sum(out.values()) == P**((D-1)*sum(target_counts))
    return out

def double_fact_even_count(k):
    assert k % 2 == 0
    return factorial(k)//(2**(k//2)*factorial(k//2))

def point_count(n, targets):
    s = n//P
    assert n == P*s
    degree_sum = D*s
    coeff = [rowcoeff(tuple(c)) for c in targets]
    fs = [factorial(k) for k in range(degree_sum+1)]
    dfs = [double_fact_even_count(k) if k%2==0 else 0 for k in range(degree_sum+1)]
    numerator = 0
    baseline = 0
    row_fac = factorial(degree_sum)**P
    for a in range(degree_sum+1):
        for b in range(degree_sum-a+1):
            diag0 = degree_sum-a-b
            if diag0%2:
                continue
            for c in range(min(degree_sum-a,degree_sum-b)+1):
                diag1 = degree_sum-a-c
                diag2 = degree_sum-b-c
                if diag1%2 or diag2%2:
                    continue
                w = fs[a]*fs[b]*fs[c]*dfs[diag0]*dfs[diag1]*dfs[diag2]
                assignment = coeff[0].get((a,b),0)*coeff[1].get((diag1,c),0)*coeff[2].get((c,diag2),0)
                numerator += w*assignment
                baseline += row_fac//(fs[a]*fs[b]*fs[c]*2**((diag0+diag1+diag2)//2)*fs[diag0//2]*fs[diag1//2]*fs[diag2//2])
    denominator = double_fact_even_count(D*n)
    assert baseline == denominator
    normalized = Fraction(numerator*P**(n-1),denominator)
    return dict(n=n, normalized_atom=float(normalized), numerator=str(numerator), denominator=str(denominator))

result = []
for n in ((3,9,15,27,45,81) if D==4 else (6,12,24,48,84)):
    s = n//3
    cases = {
        'zero': [(s,0,0)]*3,
        'one': [(0,s,0)]*3,
        'r_equals_q': [(s,0,0),(0,s,0),(0,0,s)],
        'varied_within_each_q_class': [tuple(Counter(j%3 for j in range(s))[t] for t in range(3))]*3,
    }
    for name, targets in cases.items():
        assert sum(t*targets[a][t] for a in range(3) for t in range(3))%3 == 0
        rec = point_count(n,targets)
        rec['target_case'] = name
        result.append(rec)
        print(n,name,rec['normalized_atom'],flush=True)

name = 'balanced-exact-checks.json' if D==4 else 'balanced-exact-checks-d3-p3.json'
(ROOT/name).write_text(json.dumps(dict(d=D,p=P,expected_limit=1,checks=result),indent=2)+'\n')
print('PASS exact type counts: baseline equals all pairings in every example.')
