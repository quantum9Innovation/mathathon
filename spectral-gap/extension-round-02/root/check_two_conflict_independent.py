"""Enumerate original permutation products independently of the kernel proof."""
from fractions import Fraction as F
from itertools import combinations, product, permutations
from functools import lru_cache
from math import comb, factorial, prod
from pathlib import Path
import json
import random

@lru_cache(None)
def falling(n,j):
    return prod(range(n-j+1,n+1))

@lru_cache(None)
def kernel(n,h,r):
    return sum((F(comb(h,j)*(-1)**(h-j)*n**(r+j),falling(n,r+j)) for j in range(h+1)),F(0))

@lru_cache(None)
def single_color(n, cells):
    total=0
    degree=sum(p for i,j,p,q in cells)
    for sigma in permutations(range(n)):
        total+=prod((n*int(sigma[i]==j)-1)**p * int(sigma[i]==j)**q for i,j,p,q in cells)
    return F(total,factorial(n)*n**degree)

def evaluate(n,support,roles):
    return prod(single_color(n,tuple((i,j,p,q) for (cc,i,j),(p,q) in zip(support,roles) if cc==c)) for c in {e[0] for e in support})

def counts(support,roles):
    h=b=0
    for t,((c,i,j),role) in enumerate(zip(support,roles)):
        if role!=(1,0):
            continue
        conflict=any(u!=t and cc==c and (ii==i or jj==j) for u,(cc,ii,jj) in enumerate(support))
        b+=int(conflict)
        h+=int(not conflict)
    return h,b

records={'exhaustive':0,'multicolor':0,'sampled_powers':0,'attainment':0,'b2':0,'b_above2':0,'full_support':0}

def check(n,support,roles,category):
    h,b=counts(support,roles)
    if b<2:
        return
    a=len(support)
    r=a-h-2
    bound=F(2**(b-2),n**a)*(2*kernel(n,h,r+1)-kernel(n,h,r))
    value=evaluate(n,support,roles)
    assert abs(value)<=bound,(n,support,roles,value,bound)
    records[category]+=1
    records['b2' if b==2 else 'b_above2']+=1
    records['full_support']+=int(a==n)

for n in range(2,5):
    cells=[(0,i,j) for i in range(n) for j in range(n)]
    for a in range(2,n+1):
        for support in combinations(cells,a):
            for roles in product([(0,1),(1,0)],repeat=a):
                check(n,support,roles,'exhaustive')
for n in range(2,4):
    cells=[(c,i,j) for c in range(2) for i in range(n) for j in range(n)]
    for a in range(2,n+1):
        for support in combinations(cells,a):
            for roles in product([(0,1),(1,0),(2,0)],repeat=a):
                check(n,support,roles,'multicolor')
rng=random.Random(21602)
for n in range(3,7):
    cells=[(c,i,j) for c in range(2) for i in range(n) for j in range(n)]
    for _ in range(3000):
        a=rng.randint(2,n)
        support=tuple(rng.sample(cells,a))
        roles=tuple(rng.choice([(1,0),(1,0),(0,1),(2,0),(3,0),(1,2)]) for _ in support)
        check(n,support,roles,'sampled_powers')
for n in range(2,8):
    for a in range(2,n+1):
        for h in range(a-1):
            r=a-h-2
            support=((0,0,0),(0,0,1))+tuple((0,i,i+1) for i in range(1,a-1))
            roles=((1,0),(1,0))+((0,1),)*r+((1,0),)*h
            value=evaluate(n,support,roles)
            bound=F(1,n**a)*(2*kernel(n,h,r+1)-kernel(n,h,r))
            assert value==-bound
            records['attainment']+=1
n=8
split_value=sum((F(comb(4,j)*(-2)**j*n**j,falling(n,j)) for j in range(5)),F(0))
assert split_value>7
result={'status':'passed','original_product_counts':records,'method':'Direct enumeration of permutations separately by color, exact rational arithmetic. Kernels computed by an alternating indicator sum, without the positive recurrence.','clique_counterexample':{'n':8,'a':8,'h':0,'b':8,'support':'Four disjoint rows, each with its own two requested columns, all centered','scaled_signed_expectation':str(split_value),'same_row_clique_scaled_absolute_expectation':'7'},'scope':'Finite corroboration and one exact counterexample, not a proof of the general envelope'}
Path(__file__).with_name('two-conflict-independent-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
