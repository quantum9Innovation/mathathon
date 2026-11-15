#!/usr/bin/env python3
"""Finite exact-law corroboration on K5 minus an edge; no asymptotic inference."""
from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import log
from pathlib import Path
import json


def entropy(law):
    return -sum(float(p)*log(float(p)) for p in law.values() if p)


def marginal(stars, coordinates):
    result=Counter()
    for star,p in stars.items():
        result[tuple(star[j] for j in coordinates)]+=p
    return result


def main():
    A=(0,1); B=(2,3,4)
    neighbors={i:tuple(j for j in range(5) if j!=i and not(i in A and j in A)) for i in range(5)}
    alpha=Fraction(1,5)
    q={}
    for i in range(5):
        for j in neighbors[i]:
            q[i,j]=Fraction(1,6) if i in B and j in B else Fraction(1,3)
        assert sum(q[i,j] for j in neighbors[i])==1
        assert all(0<q[i,j]<Fraction(1,2) and q[i,j]==q.get((j,i),q[i,j]) for j in neighbors[i])
    laws={}
    for i in range(5):
        stars=Counter()
        if i in A:
            for root in A:
                for ys in permutations(B):
                    stars[(root,)+ys]+=Fraction(1,12)
        else:
            for root in B:
                for ya in permutations(A):
                    for yb in permutations(tuple(j for j in B if j!=root)):
                        assignment=dict(zip(A,ya))
                        assignment.update(zip(tuple(j for j in neighbors[i] if j in B),yb))
                        stars[(root,)+tuple(assignment[j] for j in neighbors[i])]+=Fraction(1,12)
        assert sum(stars.values())==1
        for star in stars:
            assert Counter(star[1:])==Counter(neighbors[star[0]])
        laws[i]=stars
    rootlaws={i:marginal(laws[i],(0,)) for i in range(5)}
    pairs={}
    mutual={}
    j_terms={}
    for i in range(5):
        for t,j in enumerate(neighbors[i],start=1):
            pairs[i,j]=marginal(laws[i],(0,t))
            mutual[i,j]=entropy(rootlaws[i])+entropy(rootlaws[j])-entropy(pairs[i,j])
            retained=tuple(s for s in range(1,len(neighbors[i])+1) if s!=t)
            cond_sum=sum(entropy(marginal(laws[i],(0,s)))-entropy(rootlaws[i]) for s in retained)
            cond_joint=entropy(marginal(laws[i],(0,)+retained))-entropy(rootlaws[i])
            j_terms[i,j]=cond_sum-cond_joint
            assert j_terms[i,j]>-1e-12
    for (i,j),law in pairs.items():
        assert law==Counter({(b,a):p for (a,b),p in pairs[j,i].items()})
    edges=[(i,j) for i in range(5) for j in neighbors[i] if i<j]
    direct_phi=sum(float(alpha)*entropy(laws[i]) for i in range(5))-sum(float(alpha)*entropy(pairs[i,j]) for i,j in edges)
    negative_phi=sum(float(alpha)*(1-2*float(q[i,j]))*mutual[i,j] for i,j in edges)+sum(float(alpha*q[i,j])*j_terms[i,j] for i in range(5) for j in neighbors[i])
    assert abs(direct_phi+negative_phi)<1e-12
    delta=sum(alpha*(1-max(rootlaws[i].values())) for i in range(5))
    qmin=min(q.values()); cmin=min(1-2*x for x in q.values())
    C=max(1/qmin,2*(4-1)/cmin)
    gamma=Fraction(9,2*4**5)/C
    assert gamma==Fraction(1,4096)
    assert direct_phi<=-float(gamma*delta**2)
    # A sixth unused candidate label has a zero row/column and never enters
    # these laws. The original integer star equations remain valid with it.
    for i in range(5):
        for star in laws[i]:
            counts=[star[1:].count(a) for a in range(6)]
            expected=[int(a in neighbors[star[0]]) for a in range(6)]
            assert counts==expected
    result=dict(status='PASS',scope='Finite-law check only; not a recovery simulation or complexity benchmark.',
                frame='K5 minus edge01',degrees=[len(neighbors[i]) for i in range(5)],
                stars_per_type=[len(laws[i]) for i in range(5)],
                exact_q_min=str(qmin),exact_c_min=str(cmin),C_kappa=str(C),
                exact_gamma=str(gamma),exact_delta=str(delta),
                direct_phi=direct_phi,weighted_identity_loss=negative_phi,
                asserted_gap_upper=-float(gamma*delta**2),unused_sixth_label='PASS')
    dest=Path(__file__).with_name('strict-nonregular-law-checks.json')
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__=='__main__':
    main()
