# Sparse finite-field perturbations of the planted line

Prepared 2026-11-15. This is a self-contained combinatorial bound; it does
not use a contiguity substitution for the degree-two model.

Fix a finite field `F_q` (in particular any odd prime field). Independently
pair the `2N` internal stubs in each of two blocks, with two distinguished
stubs per vertex. Let `C_1,C_2` be the resulting degree-two configuration
adjacency matrices, counting a loop twice on the diagonal, and set

```
A = [ C_1  I ],    sigma = (1_N,-1_N).
    [ I   C_2]
```

Thus `A sigma = sigma`, including when there are loops or multiple edges.
For a vector `w=(x,y)`, let `|supp w|` count nonzero *individual* coordinates
among its `2N` coordinates.

## Result

There is an absolute constant `D` such that, for every fixed `q`, one can
choose `epsilon_q>0` with

```
E #{w in ker_Fq(A-I): 0<|supp w|<=epsilon_q N} = O_q(N^-1).
```

Consequently the contribution to the expected kernel size from the union
of these neighborhoods of the `q` planted constants is

```
q + O_q(N^-1).
```

Both conclusions hold as stated also when the internal graphs are
independent uniform **simple** degree-two graphs. The choice of
`epsilon_q` may depend on `q`; the limiting contribution `q` has coefficient
one independent of `q`.

The same proof works for all sufficiently large `N`, with no parity
restriction. It only bounds the near-constant sector, not the uniform
sector or the whole expected kernel size.

## 1. A dense certificate after collapsing the matching

Suppose `w=(x,y)` is a nonzero solution with support `S` of size `k`.
Collapse the deterministic matching pairs `{i_+,i_-}` into `N` supervertices.
Let `m` be the number of supervertices meeting `S`, and `s` the number
meeting `S` in exactly one vertex. Then

```
m=(k+s)/2,       k/2<=m<=k.
```

Let `H` consist of **all internal edges incident to S**, keeping colors
(block 1 or block 2), loops, and multiplicities. Write `E=|E(H)|`. Let `e`
count its edges having both ends in `S` and `B` its edges with exactly one
end in `S`. Counting internal stubs gives

```
2k=2e+B,       E=e+B=k+B/2,       E<=2k.
```

Every singleton support pair has a zero coordinate on its other side.
At that zero coordinate the eigenvector equation is

```
sum of internal neighbor values = -(nonzero matching partner).
```

Hence it receives at least one internal edge from `S`. These give at
least `s` boundary edges.

Now consider zero coordinates at supervertices disjoint from `S`. Their
matching partners are also zero. If one such coordinate receives any
edge from `S`, its equation says that the sum of these neighbors' values
is zero. It cannot receive exactly one such edge. Since its internal
degree is two, it receives exactly two. Let `t` count these touched
*individual* zero coordinates. Then

```
B>=s+2t.
```

Let `r` be the number of additional supervertices used by `H` outside
the `m` support supervertices. Each contains at least one of these `t`
coordinates, so `r<=t<=k`. The number of supervertices in the certificate
is `v=m+r<=2k`. Consequently

```
E-v >= k+s/2+t-(k+s)/2-r >= k/2.                 (1)
```

This inequality is insensitive to the actual nonzero field values.
In particular it allows cancellation, unlike a Boolean flip-set count.

## 2. Uniform enumeration for all small support sizes

Let `Z_k` count kernel vectors of support size exactly `k`. For
`1<=k<=N/4`, enumerate possible certificates by `m,r,E`.

* Choose the `m` support supervertices and the `r` additional
  supervertices in at most `N^(m+r)/(m! r!)` ways.
* Give every support supervertex one of the three occupancy patterns
  (first coordinate only, second only, both). This costs at most `3^m`.
  Restricting to patterns with exactly `k` occupied coordinates only
  decreases the count.
* Assign nonzero field values in at most `q^k` ways.
* There are `4v` distinguishable internal stubs among all selected
  supervertices. The number of partial matchings with `E` pairs is at most

  `binom(4v,2E)(2E-1)!! <= 2^(4v)(2E)^E <= 2^(8k)(4k)^E`.

  Counting invalid cross-color pairs here is harmless: discard those
  partial matchings when evaluating probabilities.
* A prescribed valid colored partial matching with `E_j` pairs in block
  `j` has probability

  `prod_(j=1,2) prod_(h=0,...,E_j-1) (2N-2h-1)^(-1)`.

  Since `E_j<=E<=2k` and `k<=N/4`, every denominator is at least `N`.
  The probability is at most `N^(-E)`.

The enumeration can overcount a kernel vector many times, which is valid
for an upper bound. It includes every actual kernel vector by taking its
full incident-edge certificate from Section 1. By (1), the enumerated
parameters satisfy `E-m-r>=k/2`.

Set `D=12288 exp(2)`. Since `k/N<=1`, for each such parameter triple,

```
(4k)^E N^(m+r-E)/(m!r!)
 =4^E (k/N)^(E-m-r) k^(m+r)/(m!r!)
 <=16^k (k/N)^(k/2) k^m/m! k^r/r!.
```

There are at most `2k` choices for `E`. Summing `m` and `r` using
`sum_(j>=0) k^j/j! = exp(k)` gives the completely uniform bound

```
E Z_k <= 2k (D q)^k (k/N)^(k/2),       1<=k<=N/4.        (2)
```

No constants in (2) depend on `q`, `N`, or `k`.

## 3. Sum up to a field-dependent linear scale

Choose

```
epsilon_q = min{1/8, 1/[128 exp(1) D^2 q^2]}.
```

Put `a_k=2k(Dq)^k(k/N)^(k/2)`. For `k>=1`,

```
a_(k+1)/a_k
 =(k+1)/k * Dq * sqrt((k+1)/N) * (1+1/k)^(k/2)
 <=2 sqrt(exp(1)) Dq sqrt((k+1)/N).
```

Uniformly for `k<epsilon_q N`, this ratio is at most `1/2` for all
sufficiently large `N` (depending on fixed `q`). Thus the whole range is
summable geometrically.

A nonzero solution cannot have support size one: if either `x` or `y`
is identically zero, the equation in that block immediately forces the
other to be zero, because the cross matrix is `I`. Therefore `Z_1=0`.
Using (2) from `k=2` onward,

```
sum_(2<=k<=epsilon_q N) E Z_k
 <=2a_2 =16D^2 q^2/N.                                (3)
```

This proves the sparse-support result for the configuration model.

For each planted vector `a sigma`, subtraction is a bijection of the
kernel with itself. The `q` neighborhoods of radius `epsilon_q N` in
individual coordinates are disjoint, because two different planted
vectors differ at all `2N` coordinates and `epsilon_q<1`. Adding (3)
over `a` gives their total expected contribution

```
q + O_q(N^-1).
```

If types are recorded instead as pair labels `(x_i,y_i)`, a neighborhood
with at most `delta_q N` pairs differing from `(a,-a)` is contained in
this individual-coordinate neighborhood whenever `2delta_q<=epsilon_q`.

## 4. Exact transfer by conditioning simplicity

For a degree-two configuration graph, the probability of simplicity
tends to `exp(-3/4)>0`. This can be checked directly from the labeled
generating functions: the ratio of the coefficients of

```
(1-z)^(-1/2) exp(-z/2-z^2/4)
```

and `(1-z)^(-1/2)` tends to `exp(-3/4)`. For completeness, write
`f_n=binom(2n,n)/4^n` and `g(z)=exp(-z/2-z^2/4)`. For each fixed `j`,
`f_(N-j)/f_N ->1`; the ratio is bounded by an absolute constant for
`j<=N/2`, and by `O(sqrt N)` for all `j<=N`. Since the Taylor coefficients
of the entire function `g` have tails smaller than every inverse power,
splitting `sum_(j<=N) g_j f_(N-j)/f_N` at `N/2` and applying dominated
convergence gives `sum_j g_j=g(1)=exp(-3/4)`.

The two independent internal
graphs are simultaneously simple with probability tending to
`exp(-3/2)>0`. Conditional on this event, the internal graphs are
exactly independent uniform simple degree-two graphs.

For the nonnegative sparse count `Z`,

```
E[Z | both simple] <= E Z / P(both simple) = O_q(N^-1).
```

The planted vectors are deterministic, so their expected contribution
remains exactly `q`; only the vanishing sparse correction is divided by
the simplicity probability. This establishes `q+o_q(1)` in the requested
simple model without inflating its leading coefficient.

