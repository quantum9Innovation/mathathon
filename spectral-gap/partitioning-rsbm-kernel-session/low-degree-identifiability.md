# The `(d1,d2)=(2,1)` case: rigorous partition rigidity, and its limits

This note concerns two independent uniform **simple** 2-regular graphs on
`N` vertices and an independent uniform perfect matching between them.
The adjacency matrix is `A`, and the planted vector is `sigma`, with values
`+1` and `-1` on the two blocks. Thus `A sigma = sigma`.

The conclusions below concern a second `{+1,-1}` eigenvector. They do not
establish that the real eigenspace at eigenvalue 1 is one-dimensional.
The counting argument is an independent derivation; it should not be
advertised as a new rigidity theorem without checking earlier RSBM work.

## Precise conclusion

Let `B_N` be the event that there is a balanced partition, different from
the planted partition up to exchange of its two classes, such that every
vertex has exactly two neighbors in its own class and one neighbor across.
Then there are absolute constants `0<c<C<infinity` such that, for all
sufficiently large `N`,

`c N^{-2} <= P(B_N) <= C N^{-2}`.

Equivalently, with probability `1-O(N^{-2})`, the only `{+1,-1}`
eigenvectors of `A` at eigenvalue 1 are `sigma` and `-sigma`. Balance need
not be imposed separately: if `A z=z` and `z` has values `{+1,-1}`, then
`3 <1,z> = <1,Az> = <1,z>`, so `<1,z>=0`.

There is also the rigorous lower bound

`P(dim ker(A-I) >= 2) >= c N^{-2}`.

This lower bound is compatible with a high-probability simplicity theorem.
No upper bound on the probability of an arbitrary extra real eigenvector
is proved here.

## Deterministic characterization of another partition

Given an alternative assignment, mark the vertices whose sign has changed
relative to `sigma`. Write its two sets of marked vertices as `S_A,S_B`.
At a vertex let `r` be the number of its two internal edges whose endpoints
have different marks, and let `m` be 1 if its matching edge has differently
marked endpoints and 0 otherwise. The new number of cross-class neighbors
is `r+1-m`. Hence the alternative partition is admissible exactly when

`r=m` at every vertex.

In particular, the internal edges that cross the marked/unmarked cut form
a matching. A vertex lies on one of these internal boundary edges exactly
when its original cross-block matching edge crosses the marks.

Balance gives `|S_A|=|S_B|=k`. By replacing the alternative assignment by
its negative, one may assume `1<=k<=N/2`.

## Exact first-moment formula

First use the 2-regular configuration model in each block, permitting loops
and parallel edges. Fix a subset of size `k` in one block. The probability
that its internal boundary is a matching of exactly `t` edges is

```
P_t = binom(k,t) binom(N-k,t) 2^(2t) t!
      (2k-t-1)!! (2(N-k)-t-1)!! / (2N-1)!! .
```

Here `t` must be even, `0<=t<=k`, and `(-1)!!=1`. To see the formula,
choose the `t` boundary vertices on each side, choose one of the two stubs
at each, pair the selected stubs across the cut, and pair all remaining
stubs within their respective sides.

If the two blocks have internal boundary sizes `t_A,t_B`, compatibility
with the cross-block matching requires `t_A=t_B=t`. Conditional on this,
the matching compatibility probability is

```
Q_t = (t!)^2 (k-t)! (N-k-t)! / N! .
```

Indeed, the four types in each block are marked boundary, marked interior,
unmarked boundary, and unmarked interior. The matching must interchange
the two boundary types across blocks and preserve the two interior types.

Consequently a union bound for alternatives of overlap size `k` is

```
E_k = binom(N,k)^2 sum_{0<=t<=k, t even} P_t^2 Q_t .
```

This is an exact first-moment count in the configuration model. For simple
graphs, `k=1` is impossible, because the sole marked vertex in either
block has two internal neighbors outside the marked set.

## Uniform small-overlap estimate

For `2<=k<=N/8`, the ratio of double factorials in `P_t` is at most
`N^(-k-t/2)`: the removed denominator factors are all at least `N`.
Using

```
binom(k,t) <= 2^k,
binom(N-k,t)t! <= N^t,
(2k-t-1)!! <= (2k)^(k-t/2),
```

gives

`P_t <= 16^k (k/N)^(k-t/2)`.

Also, since `N-k-t>=N/2`,

`Q_t <= 4^k k^(k+t) N^(-k-t)`.

Together with `binom(N,k)<=(eN/k)^k`, this yields, for the individual
summand `E_{k,t}=binom(N,k)^2 P_t^2 Q_t`,

`E_{k,t} <= (C0 k/N)^k`, where one may take `C0=1024 e^2`.

Choose the absolute constant `delta=1/(100 C0)`. Then

`sum_{k=2}^{floor(delta N)} E_k = O(N^{-2})`.

For example, the ratio of consecutive terms
`(k+1)(C0 k/N)^k` is bounded by
`(3/2)e C0(k+1)/N`, which is less than `1/2` throughout this range
for sufficiently large `N`. The first term is `O(N^{-2})`.

## Macroscopic-overlap estimate without a numerical entropy assumption

Put `alpha=k/N`, `beta=t/N`, and `s(x)=x log x`, with `s(0)=0`.
Uniform Stirling bounds give

`log E_{k,t} = N F(alpha,beta)+O(log N)`,

where

```
F(alpha,beta) = -s(alpha-beta)-s(1-alpha-beta)
               +s(2alpha-beta)+s(2-2alpha-beta)
               +(4beta-2)log 2 .
```

The error is uniform over `delta<=alpha<=1/2`, `0<=beta<=alpha`.
The following gives a direct proof that its maximum is negative there.

For fixed `alpha` in `(0,1/2]`,

```
dF/dbeta = log[16(alpha-beta)(1-alpha-beta)
                 / ((2alpha-beta)(2-2alpha-beta))].
```

Its derivative is strictly negative, since each negative reciprocal has
a smaller denominator than its corresponding positive reciprocal.
The unique maximizing value is

`beta*(alpha)=(7-sqrt(49-180alpha(1-alpha)))/15`.

This lies in `(0,1/3]`, with equality `1/3` only at `alpha=1/2`.
Set `f(alpha)=F(alpha,beta*(alpha))`. To determine its derivative, put

```
u=alpha-beta*, v=1-alpha-beta*,
x=2u+beta*,   y=2v+beta*.
```

The stationarity equation is `xy=16uv`, and the envelope derivative is

`f'(alpha)=log(x^2 v/(y^2 u))`.

The difference in numerator and denominator has the factorization

`x^2 v-y^2 u=(u-v)(4uv-beta*^2)`.

Stationarity gives

`4uv-beta*^2=2 beta*(1/3-beta*)`.

Thus `f'(alpha)<0` for `0<alpha<1/2`. Finally `f(alpha)->0` as
`alpha->0`. It follows that

`F(alpha,beta)<=f(delta)<0`

uniformly in the macroscopic range. Summing at most `N^2` terms with the
uniform polynomial Stirling prefactor proves an exponentially small bound
for `delta N<=k<=N/2`.

## Conditioning on simplicity

Each simple labeled 2-regular graph corresponds to exactly `2^N`
configurations, so conditioning gives the desired uniform simple model.
The one-block simplicity probability tends to `exp(-3/4)>0`; hence
conditioning the two independent blocks costs a bounded factor.

For a direct enumeration of this standard fact, the number of simple
labeled 2-regular graphs divided by `N!` is the coefficient of `z^N` in

`exp(-z/2-z^2/4)(1-z)^(-1/2)`.

Its coefficient is asymptotic to `exp(-3/4)/sqrt(pi N)`, whereas
`(2N-1)!!/(2^N N!)=binom(2N,N)/4^N~1/sqrt(pi N)`.
Equivalently, the probability follows from the standard configuration
model Poisson limits for loops and double edges.

For the upper bound, omit `k=1` before conditioning, since it cannot
produce an alternative in the simple model. The preceding estimates then
give `P(B_N)=O(N^{-2})`.

## A matching lower bound and a localized extra eigenvector

Suppose the internal graphs contain four-vertex paths, in the following
orders,

```
a3 -- a1 -- a2 -- a4,
b3 -- b1 -- b2 -- b4,
```

and the cross-block perfect matching contains

`a1-b3, a2-b4, a3-b1, a4-b2`.

Define `x=1` on `a1,a2`, `x=-1` on `b1,b2`, and zero elsewhere.
Checking the eight affected vertices proves `Ax=x` exactly. The vertices
outside the paths receive no contribution, because the four nonzero
vertices have all their neighbors among the eight listed vertices.
The four zero path endpoints each receive one `+1` and one `-1`.

Moreover, `sigma-2x` is another balanced `{+1,-1}` eigenvector. This
construction works when a four-vertex path closes into a four-cycle too.

A simple 2-regular graph has a collection of at least `(N-3T)/7`
vertex-disjoint four-vertex paths, where `T` is its number of triangle
components: on each cycle of length `ell>=4`, use `floor(ell/4)>=ell/7`
disjoint consecutive paths. In the uniform simple 2-regular model,
`E T=O(1)`. One elementary way to see the bound is to count triangle
cycles in the configuration model, whose expectation is

`(N)_3 2^3 / [6(2N-1)(2N-3)(2N-5)]=O(1)`,

and then condition on simplicity with its bounded cost. Thus, with
probability `1-O(1/N)`, both blocks provide at least `c1 N` disjoint
four-vertex paths for an absolute `c1>0`.

Fix such path collections of sizes `m_A,m_B`. For each pair `(i,j)`, let
`E_ij` be the event that the matching makes the four prescribed edges.
Then `P(E_ij)=1/(N)_4`. Two different events sharing an A-path or a B-path
are incompatible, because all paths in a collection are vertex-disjoint.
Two events using different paths in both blocks have joint probability
`1/(N)_8`. Bonferroni therefore gives

```
P(union E_ij | internal graphs)
 >= m_A m_B/(N)_4 - (m_A m_B)^2/[2(N)_8]
 = Omega(N^{-2}).
```

This proves both the `Omega(N^{-2})` lower bound for `B_N` and the same
lower bound for an extra real eigenvector at eigenvalue 1.

## Remaining kernel issue

After relabeling the matched pairs, write the two internal adjacency
matrices as `C,D`. Then

```
A = [[C,I],[I,D]],
dim ker(A-I)=dim ker((D-I)(C-I)-I).
```

The planted solution is `x=1,y=-1`. Excluding other sign vectors does not
exclude other real solutions of this product equation. Establishing that
no such solution exists with high probability requires an additional
random-matrix argument. The partition counting theorem above supplies no
such argument.

## Exact finite example: unique partition but a two-dimensional kernel

There is even a deterministic example in this model's support showing why
partition rigidity cannot be substituted for a real-kernel theorem.
Take `N=8`, use vertex indices `0,...,7` in each block, identity matching,
and the internal cycles

```
C: (0,1,2,3,4,5,6,7),
D: (5,6,7,0,4,1,2,3).
```

The following two integer vectors are independent and satisfy `Av=v`,
`Aw=w`, as direct substitution verifies:

```
v=(-1, 0,-1,-2,-1, 0, 0,-1; 0, 2, 1, 0, 1, 1, 1, 0),
w=( 0,-1, 0, 1, 0,-1,-1, 0; 1,-1, 0, 1, 0, 0, 0, 1).
```

The matrix `K=(D-I)(C-I)-I` has the following leading `6x6` minor:

```
 1 -1  0  1 -1  1
-1  1 -2  2 -1  1
 1 -2  2 -2  1  0
 0  1 -2  1  0 -1
 0  0  1 -1  0 -1
 0  0  1 -1  0  1
```

Its determinant is `-4`, so `rank K>=6`. The independent vectors above
give `dim ker(A-I)>=2`, and the block reduction therefore proves
`dim ker(A-I)=2` exactly.

Every eigenvector at 1 has the form `s v+t w`. If it is a sign vector,
its coordinates at A-vertices 0 and 1 force `s,t` each to belong to
`{+1,-1}`. Its coordinate at A-vertex 3 is `-2s+t`; this has magnitude 1
only if `s=t`. Since `v+w=-sigma`, the only sign vectors in the kernel
are `sigma` and `-sigma`.

This is a finite exact certificate, not a probabilistic obstruction to
high-probability simplicity. It rules out the deterministic inference
“unique admissible partition implies one-dimensional planted eigenspace.”
