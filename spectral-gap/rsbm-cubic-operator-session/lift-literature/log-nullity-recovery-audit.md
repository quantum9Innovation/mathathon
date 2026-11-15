# Independent audit: polynomial kernel moment is enough for recovery

Audited on 2026-11-15 against
`spectral-gap/partitioning-rsbm-obstruction-session/finite-field-21-entropy.txt`
and the existing Boolean-rigidity proof in
`spectral-gap/partitioning-rsbm-kernel-session/low-degree-identifiability.md`.

The exact type count and its nonpositive entropy exponent give a complete
polynomial-time-recovery route, without proving one-dimensionality of the
real eigenspace. No new probabilistic estimate beyond those ingredients is
needed. This audit independently checks the type count, supplies an
explicit loose polynomial moment bound, and checks algorithmic access and
bit complexity.

## 1. The exact type formula is consistent

After matching relabeling and planted sign conjugation,

```
M = [[C_+-I,-I],[-I,C_--I]],
M(x,z)=0 iff C_+ x=x+z and C_- z=x+z.
```

Work over `F_2`. At each matched coordinate choose ordered stub labels
`(a,d,b,e) in F_2^4`. The other two neighbor labels are uniquely
`c=a+d-b` and `f=a+d-e`. A profile assignment fixes the value of `(x,z)`
and the desired endpoint labels on every distinguished stub. A pairing is
compatible precisely when it pairs a stub of endpoint type `(u,v)` to one
of type `(v,u)`. This gives `m_{uv}!` choices for each `u<v`, and
`(m_{uu}-1)!!` choices on each diagonal. Each compatible pairing together
with a kernel vector induces exactly one such ordered profile assignment.
Thus neither an overcount nor an orientation factor is missing.

In particular the exact expected size of the kernel is the type sum (1)
in the cited file. The two simple-graph conditioning events have a
probability bounded away from zero and therefore preserve polynomial
moment bounds.

## 2. Entropy nonpositivity needs no equality analysis

The two commuting swaps `b<->c` and `e<->f` preserve both edge-stub
tables. Averaging a profile law `T` over these swaps weakly increases its
entropy. For the resulting law `Tbar`,

```
Q^+ = law(A,B),   Q^- = law(D,E).
```

Therefore the entropy exponent satisfies

```
Phi(T) <= Phi(Tbar)
       = H(A,D,B,E)-H(A,B)-H(D,E)
       = -I((A,B);(D,E)) <= 0.
```

This directly checks the four-term chain-rule identity in the source.
Its equality classification and saddle-point asymptotics are not needed
for a polynomial moment bound.

## 3. An explicit loose bound: E[2^nullity] <= C(N+1)^24

Here is a zero-safe factorial argument, avoiding any unstated uniformity
in the Stirling error. Put `h(k)=k log k-k`, with `h(0)=0`, and write

```
log(k!) = h(k)+epsilon(k),
0 <= epsilon(k) <= 1+log(k+1)   for every integer k>=0.
```

These bounds follow by comparing `sum_{j=1}^k log j` with the integral of
`log x`; they also hold at zero. For a diagonal table entry `m=2l`, use

```
log((m-1)!!) = h(m)-h(l)-l log 2 + epsilon(m)-epsilon(l).
```

For `p=2`, each of the two symmetric tables has one off-diagonal factorial
and two diagonal double factorials. Thus the upper error contributed by
the two `W` factors is at most
`6(1+log(2N+1))`. The multinomial numerator contributes at most
`1+log(N+1)`; errors from its denominator are nonpositive. Finally

```
log((2N-1)!!) = h(2N)-h(N)-N log 2
               +epsilon(2N)-epsilon(N),
```

so dividing by its square costs at most `2(1+log(N+1))` beyond the
leading entropy calculation. Consequently every valid type summand is
at most

```
exp(N Phi(T)) * exp(9) (N+1)^3 (2N+1)^6
 <= 64 exp(9) (N+1)^9.
```

There are 16 profile categories. The number of all types is
`binom(N+15,15)<=(N+1)^15`, and imposing validity only decreases that
number. Hence, in the configuration model,

```
E |ker_F2 M| <= 64 exp(9) (N+1)^24.
```

Conditioning both internal graphs to be simple changes only the absolute
constant. Since `|ker_F2 M|=2^{nu_2}`, Markov gives

```
P(nu_2 > 26 log_2(N+1)) <= C (N+1)^{-2}.
```

The exponent 26 is deliberately loose and not optimized.

## 4. No unknown planted information enters the algorithm

For every integer matrix, a minor nonzero modulo 2 is also nonzero over
the reals. Thus

```
nu_R(A-I) <= nu_F2(A-I).
```

Relabeling by the cross matching conjugates by a permutation matrix and
does not change either rank. Planted sign conjugation is invertible over
both fields; over `F_2` it is just the identity. Therefore the moment
bound proved in the planted matching gauge bounds the nullity of the
ordinary, observable matrix `A-I`. The algorithm computes this matrix
directly from the input graph and needs no matching, planted split,
vertex labels inherited from the model, or sign gauge.

## 5. Exact polynomial algorithm

Given the graph on `2N` vertices:

1. Compute a rational basis matrix `B` for `U=ker_Q(A-I)` and put
   `r=dim U`.
2. If `r>26 log_2(N+1)`, return failure.
3. Choose `r` row indices `J` such that the square matrix `B_J` is
   nonsingular.
4. For each `s in {+1,-1}^r`, compute `v=B B_J^{-1}s` exactly. Retain it
   if every coordinate is `+1` or `-1`.
5. Return the unordered partition encoded by the retained vectors if they
   are exactly one opposite pair; otherwise return failure.

Every vector in `U` is determined by its coordinates on `J`, so this
enumerates every Boolean eigenvector and no others. The existing
rigidity theorem says that, except on probability `O(N^{-2})`, the only
Boolean eigenvectors at eigenvalue 1 are `+sigma,-sigma`. The moment
bound says that the size cap fails with probability `O(N^{-2})` too.
Thus this deterministic algorithm succeeds with probability
`1-O(N^{-2})` and always runs in polynomial time.

There are at most `(N+1)^26` sign patterns under the cap. All matrices have
integer entries of bounded size before elimination. Rational basis
entries can be represented as ratios of minors, whose bit lengths are
`O(N log N)` by Hadamard's bound. Standard exact Gaussian elimination,
matrix products, and equality checks therefore cost polynomial bit
time per pattern. No real-number oracle or numerical tolerance is
required.

This establishes recovery, assuming the already proved Boolean-rigidity
bound, and does not establish `nu_R(A-I)=1` with high probability.

## Independent finite-size check

`verify_small_types.py` independently enumerates all pairs of stub
pairings, computes their matrix ranks over `F_2`, and compares the exact
expected kernel size with the profile-type formula. Running it with
`nix-shell -p python3 --run 'python3 spectral-gap/rsbm-cubic-operator-session/lift-literature/verify_small_types.py'`
gave exact agreement:

```
N=1: 2
N=2: 4
N=3: 248/75
N=4: 2896/525
```

These include loops and parallel edges, as required by the configuration
count. This check supports the exact enumeration and is not used as a
proof of its general validity.
