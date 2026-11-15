# A universal polynomial kernel moment by aggregate-fiber entropy

Derived and independently audited by three agents on 2026-11-15. This
strengthens the degree-dependent exponent in
`GENERAL-POLYNOMIAL-RECOVERY.md`: the exponent can be **24 for every
fixed degree pair**, by avoiding a count of individual local types.

Fix `a>=2`, `b>=1`, and `lambda=a-b`. The intended assortative model has
`a>b`. Work first in the independent internal and bipartite cross
configuration models on two blocks of size `N`; require only the usual
admissibility `aN` even. Over a prime field `F_p`, let
`q=p(p+1)/2`.

## The exact count, grouped by three aggregate edge tables

A plus-star profile is

\[
 (x,A_1,\ldots,A_a,B_1,\ldots,B_b),\qquad
 \sum_i A_i+\sum_jB_j=\lambda x\quad\text{in }\mathbb F_p,
\]

and a minus-star is defined similarly, with root `y`, internal labels
`C_i`, and cross labels `D_j`. Every slot is distinguished.

For each pair of symmetric, diagonal-even internal tables `m^+,m^-`
with total `aN`, and each cross table `h` with total `bN`, define
`Omega(m^+,m^-,h)` to be the set of **all ordered arrays** of `N` plus
stars and `N` minus stars such that:

- Each star satisfies its local field equation.
- The plus internal directed-edge table is `m^+` and the minus internal
  table is `m^-`.
- The plus cross table is `h`, and the minus cross table is `h^T`.

The root label and requested partner label determine every directed
edge-table contribution. This is the same table definition as in the
general note. Empty fibers contribute zero. Put

\[
 W(m)=\prod_{u<v}m_{uv}!\prod_u(m_{uu}-1)!!.
\]

Counting distinguished-stub pairings for each ordered profile array
gives the exact identity

\[
 \mathbb E|\ker_{\mathbb F_p}(A-\lambda I)|
 =\sum_{m^+,m^-,h}|\Omega(m^+,m^-,h)|
 \frac{W(m^+)W(m^-)}{((aN-1)!!)^2}
 \frac{\prod_{u,v}h_{uv}!}{(bN)!}.                    \tag{1}
\]

Every kernel vector and graph configuration produce exactly one ordered
profile array. For any fixed array, the pairing count depends only on
its three tables. Thus (1) includes every multinomial choice of local
types already; **no additional local-type count or multinomial factor
may be inserted**.

## Entropy bounds the fiber cardinality without a prefactor

For one nonempty fiber, choose its entire ordered profile array
uniformly. Its entropy is exactly `log|Omega|`.

The fiber is invariant under independent permutations of the `N` vertex
positions in each block. It is also invariant under arbitrary
permutations of the internal slots and of the cross slots at each
vertex. The local field equation depends only on sums; each table
depends only on the corresponding neighbor multiset. All these maps
are bijections of the fiber.

Consequently, every plus vertex has a common, slot-symmetric profile law
`T_+`, and every minus vertex has a common law `T_-`. Their one-slot edge
laws are **exactly**

\[
 F_+=\frac{m^+}{aN},\qquad F_-=\frac{m^-}{aN},\qquad
 G=\frac h{bN}.
\]

Subadditivity across the `2N` vertex profiles gives

\[
 \log|\Omega|\le N\{H(T_+)+H(T_-)\}.                  \tag{2}
\]

No independence of vertices or of blocks is asserted. The already proved
star entropy inequality, valid for every such pair of laws when `a>=2`,
is

\[
 H(T_+)+H(T_-)
 \le\frac a2\{H(F_+)+H(F_-)\}+bH(G).                 \tag{3}
\]

For completeness, it follows by deleting the one internal neighbor
determined by the local equation and applying conditional
subadditivity. Subtraction leaves

\[
 -\left(\frac a2-1\right)
    \{I(X;A_1)+I(Y;C_1)\}-bI(X;B_1)\le0.
\]

Equations (2)--(3) therefore bound the fiber cardinality by the exact
exponential factor canceled by the pairing weights:

\[
 |\Omega|\le
 \exp\!\left[N\left\{\frac a2(H(F_+)+H(F_-))+bH(G)\right\}\right].
                                                               \tag{4}
\]

This is an entropy bound on a finite uniform fiber, so it requires
neither Stirling approximations for local-profile multinomials nor
large-deviation duality.

## Only polynomially many aggregate tables remain

The elementary factorial estimates from the general note imply

\[
 \frac{W(m)}{(aN-1)!!}
 \le e^{q+1}(aN+1)^{q+1}\exp[-(aN/2)H(F)]
\]

and

\[
 \frac{\prod h_{uv}!}{(bN)!}
 \le e^{p^2}(bN+1)^{p^2}\exp[-bNH(G)].
\]

After multiplying (4), every summand of (1) is at most

\[
 e^{2(q+1)+p^2}(aN+1)^{2(q+1)}(bN+1)^{p^2}.
\]

There are at most `(aN+1)^{2p^2}(bN+1)^{p^2}` table triples: bound each
entry independently, generously ignoring symmetry, parity, and fixed
totals. Therefore

\[
\boxed{
 \mathbb E|\ker_{\mathbb F_p}(A-\lambda I)|
 \le e^{p(p+1)+2+p^2}
       (aN+1)^{p(p+1)+2+2p^2}(bN+1)^{2p^2}.}         \tag{5}
\]

The power of `N` is `5p^2+p+2`, independent of `a,b`. In particular,

\[
\boxed{
 \mathbb E\,2^{\dim_{\mathbb F_2}\ker(A-\lambda I)}
 \le e^{12}(aN+1)^{16}(bN+1)^8=O_{a,b}(N^{24}).}      \tag{6}
\]

The coefficient in the last asymptotic may depend on the fixed degrees.
Conditioning the three configuration factors on simplicity has
probability tending to a positive constant at fixed `a,b` and gives
exactly the requested independent uniform simple factors. Thus the
same `O_{a,b}(N^24)` bound holds in the target model, along every
admissible block size, including odd sizes when `a` is even.

## The same fibers directly bound Boolean alternatives

The counting identity (1) also applies to actual integer sign profiles,
with alphabet `{+1,-1}` and local equation
`sum A_i+sum B_j=lambda X` over the integers. Here the two signs are
distinct symbols; this is not their reduction modulo two. All factorial
weights and table-count bounds depend only on the alphabet size, not on
the numerical interpretation of its symbols.

Let `Z_k` count Boolean eigenvectors that flip exactly `k` signs in each
planted block, and set `alpha=k/N`. Restrict each fiber to these root
counts. Vertex and slot permutations still preserve it, so its root laws
are fixed and the same entropy bound applies. The independently checked
variance-gap argument in `BOOLEAN-VARIANCE-GAP-AUDIT.md` strengthens (3)
by

\[
 H(T_+)+H(T_-)
 \le\frac a2\{H(F_+)+H(F_-)\}+bH(G)
       -\frac{2b^2}{a^4}\alpha^2(1-\alpha)^2.
\]

The same cancellation and count of table triples therefore give the
explicit configuration-model bound

\[
\boxed{\mathbb E Z_k\le
 e^{12}(aN+1)^{16}(bN+1)^8
 \exp\!\left[-\frac{2b^2}{a^4}
                N\alpha^2(1-\alpha)^2\right].}       \tag{7}
\]

Every choice of root signs, including its usual binomial factors, is
already counted in the restricted fiber; no additional multiplicity
factor is missing in (7).

For any fixed `eta>0`, summing over `eta N<=k<=N/2` is exponentially
small after the polynomial prefactor. The existing small-support
eigenvector proposition handles `k<eta N` for sufficiently small fixed
`eta`: the difference from the planted sign vector is an eigenvector
supported on `2k` vertices. Thus the entire Boolean rigidity proof also
uses only aggregate fibers, without counting individual local types.

## A single polynomial cutoff for every fixed assortative pair

Set `n=2N`, `d=a+b`, and solve the binary affine system

\[
 (A+dI)z=(b\bmod2)\mathbf1.
\]

Its homogeneous matrix is `A-lambda I` modulo two. If its nullity is
`k`, abort when `2^k>n^{27}`. Otherwise enumerate the affine space in
Gray-code order and verify exactly `b` opposite neighbors per vertex.
Equation (6) bounds the abort probability by `O_{a,b}(N^-3)`.

The previously proved Boolean entropy gap and small-support estimate
give uniqueness with high probability for every fixed `a>b>=1`. Thus
this **single cutoff** proves polynomial exact recovery at every fixed
degree pair. Its running time is `O_d(n^28)` at fixed degree. Even on
inputs with arbitrary degree at most `n-1`, the enumeration cutoff and
integer checks give a universal worst-case polynomial bound
`O(n^29)`; the high-probability success guarantee here is for fixed
degrees only.

The proof uses no real-eigenvalue simplicity, sharp `Cp` moment,
matching-sum contiguity, or additional even-block-size assumption.
