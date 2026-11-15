# General fixed-degree recovery by a polynomial kernel moment

Derived and audited 2026-11-15 after freezing the separate cubic recovery
manuscript. This extends the coarse-moment route at the root task's
explicit request. Historical priority is not asserted. The result below
does not assert simplicity of the planted real eigenvalue.

Let `a=d1>b=d2>=1` be fixed integers. Each planted block has size `N`.
The internal graphs are independent uniform simple `a`-regular graphs,
and the cross graph is an independent uniform simple `b`-regular
bipartite graph. All limits are through admissible `N`; no extra parity
condition is imposed. Write `d=a+b`, `lambda=a-b`, and `n=2N`.

**Claim proved below for `a>=3`.** A deterministic algorithm with a fixed
polynomial worst-case running time recovers the planted partition, up to
global sign, with probability tending to one. The cubic case `a=2,b=1`
is covered separately in `POLYNOMIAL-RECOVERY.md`. Together these cover
every fixed `d1>d2>0`, including odd admissible block sizes.

The two ingredients are a polynomial finite-field kernel moment and
Boolean rigidity. Both use exact configuration enumeration, without
matching-sum contiguity or a local central limit theorem.

## 1. Exact two-star configuration formula

Use independent internal pairings of `aN` distinguished stubs in each
block, and an independent uniform bijection between the `bN` cross stubs
in the two blocks. The condition `aN` even is already necessary for the
requested internal regular graphs. Loops have diagonal weight two.

Over a fixed prime field `F_p`, a plus-star profile is

\[
 s=(x,A_1,\ldots,A_a,B_1,\ldots,B_b),\qquad
 \sum_{i=1}^{a} A_i+\sum_{j=1}^{b}B_j=\lambda x.
\]

Its root is the kernel coordinate in the first block; the `A` labels
are internal neighbor coordinates and the `B` labels are cross neighbor
coordinates. There are `p^d` profiles, since one internal neighbor is
determined by the root and the other `d-1` neighbor labels. A minus-star
is similarly

\[
 t=(y,C_1,\ldots,C_a,D_1,\ldots,D_b),\qquad
 \sum_i C_i+\sum_jD_j=\lambda y.
\]

Let `n_s^+,n_t^-` be the two profile-count arrays, each with total `N`.
Define integer tables

\[
\begin{split}
 m^+_{uv}&=\sum_s n_s^+1_{x=u}\sum_i1_{A_i=v},&
 m^-_{uv}&=\sum_t n_t^-1_{y=u}\sum_i1_{C_i=v},\\
 h^+_{uv}&=\sum_s n_s^+1_{x=u}\sum_j1_{B_j=v},&
 h^-_{vu}&=\sum_t n_t^-1_{y=v}\sum_j1_{D_j=u}.
\end{split}
\]

Validity requires `m^+,m^-` symmetric with even diagonals and
`h^+=h^-`; denote the common cross table by `h`. Put

\[
 W(m)=\prod_{u<v}m_{uv}!\prod_u(m_{uu}-1)!!.
\]

Distinguished-stub counting gives the exact identity

\[
\mathbb E|\ker_{\mathbb F_p}(A-\lambda I)|
=\sum_{\mathrm{valid}\ n^+,n^-}
 \frac{N!}{\prod_s n_s^+!}\frac{N!}{\prod_t n_t^-!}
 \frac{W(m^+)W(m^-)}{((aN-1)!!)^2}
 \frac{\prod_{u,v}h_{uv}!}{(bN)!}.                    \tag{1}
\]

The last numerator counts bijections between the cross-stub pools with
each pair of endpoint labels. Every pairing, cross bijection, and kernel
vector determine their profile assignments uniquely. Thus no
factorization multiplicity or orientation factor is missing in (1).

Let `S_+,S_-` be the profile laws `n^+/N,n^-/N`. Define probability tables
`F_+=m^+/(aN)`, `F_-=m^-/(aN)`, `G=h/(bN)`. Uniform factorial bounds show
that the entropy exponent of a summand of (1), divided by `N`, is

\[
 \Phi=H(S_+)+H(S_-)-\frac a2\{H(F_+)+H(F_-)\}-bH(G).
                                                               \tag{2}
\]

Here all entropies use natural logarithms and `0 log0=0`.

## 2. The entropy exponent is nonpositive for every `a>=2`

Average each star law under all permutations of its internal slots and
all permutations of its cross slots. This preserves the constraints,
the four tables, and the root laws, and increases star entropy. It
suffices to prove the bound for the symmetrized laws. Write

\[
\begin{split}
 P&=\mathcal L(X)=\mathcal L(A_i)=\mathcal L(D_j),\\
 Q&=\mathcal L(Y)=\mathcal L(C_i)=\mathcal L(B_j).
\end{split}
\]

These marginal identities follow from internal table symmetry and cross
table consistency. For a generic internal and cross slot,

\[
 F_+=\mathcal L(X,A),\quad F_-=\mathcal L(Y,C),\quad
 G=\mathcal L(X,B)=\mathcal L(D,Y).
\]

One internal label is determined by the root and all other neighbor
labels. Conditional subadditivity therefore gives

\[
\begin{split}
 H(S_+)&\le H(X)+(a-1)H(A\mid X)+bH(B\mid X),\\
 H(S_-)&\le H(Y)+(a-1)H(C\mid Y)+bH(D\mid Y).
\end{split}
\]

Substitute these bounds into (2), and use the marginal identities. The
result is

\[
 \boxed{\Phi\le
 -\left(\frac a2-1\right)\{I(X;A)+I(Y;C)\}
 -bI(X;B)\le0\qquad(a\ge2).}                         \tag{3}
\]

This argument works over `F_2`, and is independent of parity of `N`.

## 3. An explicit polynomial moment and logarithmic multiplicity

Let `q=p(p+1)/2`. The same zero-safe factorial bounds as in the cubic
proof give

\[
 \frac{W(m)}{(aN-1)!!}
 \le e^{q+1}(aN+1)^{q+1}\exp[-(aN/2)H(F)],
\]

and

\[
 \frac{\prod h_{uv}!}{(bN)!}
 \le e^{p^2}(bN+1)^{p^2}\exp[-bNH(G)].
\]

There are at most `(N+1)^{2p^d}` pairs of profile types. Using multinomial
entropy bounds and (3) yields

\[
\boxed{
 \mathbb E|\ker_{\mathbb F_p}(A-\lambda I)|
 \le e^{2(q+1)+p^2}(aN+1)^{2(q+1)}(bN+1)^{p^2}
             (N+1)^{2p^d}.}                           \tag{4}
\]

This is in the configuration model. Conditioning all three independent
factors on simplicity has probability bounded away from zero for fixed
`a,b`. Every simple internal graph has exactly `(a!)^N` configuration
realizations and every simple cross graph exactly `(b!)^{2N}` cross-stub
bijection realizations. The conditioned factors are therefore exactly
the requested independent uniform simple factors. A nonnegative moment
increases by at most the reciprocal simplicity probability. Thus (4),
up to a fixed multiplicative constant, holds in the target model.

Taking `p=2`, set

\[
 C_d=2^{d+1}+12.
\]

Then

\[
 \mathbb E\,2^{k_2}=O_{a,b}(N^{C_d}),\qquad
 k_2=\dim_{\mathbb F_2}\ker(A-\lambda I).                \tag{5}
\]

The exponent is deliberately coarse. In particular, `k_2=O(log N)`
with high probability, for all admissible block sizes. Since
`dim_Q ker(A-lambda I)<=k_2`, this also bounds real multiplicity.

## 4. Equality phases when `a>=3`

Fix an odd prime `p` not dividing `b`. Suppose a valid type has `Phi=0`.
Equality must hold in star symmetrization and conditional
subadditivity. Since `a/2-1>0`, (3) forces all three displayed mutual
informations to vanish. Consequently, conditional on a plus root, the
`a-1` retained internal neighbors and the `b` cross neighbors are
independent; their laws are respectively `P` and `Q`, independent of the
root. Therefore, for independent

\[
 X,U_1,\ldots,U_{a-1}\sim P,\qquad V_1,\ldots,V_b\sim Q,
\]

the random variable `lambda X-sum U_i-sum V_j` has law `P` (it is the
omitted internal neighbor). Writing `hat P,hat Q` for additive Fourier
transforms gives, for each `t in F_p`,

\[
 \widehat P(t)=\widehat P(\lambda t)
              \widehat P(-t)^{a-1}\widehat Q(-t)^b.
\]

Thus `r=|hat P(t)|` obeys `r<=r^{a-1}`. For `a>=3` this forces
`r in {0,1}`. Every nonzero character of `F_p` is injective, so if `P`
is not a point mass, then `|hat P(t)|<1` at each nonzero `t`; it must
therefore vanish at each nonzero `t`. Hence `P` is uniform. The same
argument applies to `Q`.

If `P` is a point mass at `c`, all internal plus labels are `c`.
Conditional independence of the cross labels forces a sum of `b`
independent `Q` variables to be constant. Holding all but one of these
variables fixed shows that `Q` must be a point mass, say at `e`. The
root constraint is then `b(c+e)=0`, so `e=-c`. If `P` is uniform, `Q`
cannot be a point mass, by the same argument with the blocks reversed;
thus both are uniform. Conditional independence and the determined
omitted label then identify the full star laws.

The zero phases are exactly:

- Both stars uniform on their `p^d` profiles.
- For some `c in F_p`, every plus label is `c` and every minus label
  is `-c`.

For Boolean kernel vectors, the root laws are supported on `{+1,-1}`.
The full uniform phase is impossible when `p>=3`, and the only remaining
zero phases are the two planted sign assignments.

## 5. Boolean rigidity from compactness and the support estimate

Let `sigma` be planted and let `tau in {+1,-1}^{2N}` satisfy
`A tau=lambda tau`. Since `A 1=d 1` and `lambda!=d`, symmetry forces
`sum tau=0`. Consequently, if `k` signs in the first block differ from
`sigma`, exactly `k` differ in the second. Replacing `tau` by `-tau`
allows `k<=N/2`.

Choose a sufficiently small fixed `epsilon>0` as in the support estimate
below. For `epsilon N/2<=k<=N/2`, the two root laws are

\[
 P=(1-\alpha)\delta_{+1}+\alpha\delta_{-1},\qquad
 Q=\alpha\delta_{+1}+(1-\alpha)\delta_{-1},\qquad
 \epsilon/2\le\alpha=k/N\le1/2.
\]

These laws are a fixed positive distance from both planted constant
phases and from the uniform `F_p` phase. By the zero-phase
classification and compactness of the finite-dimensional feasible
profile space, `Phi<=-c_{a,b,p,epsilon}<0` uniformly on these Boolean
types. Equation (1), with its polynomial number of types and polynomial
factorial errors, therefore gives an exponentially small expected
number of such alternatives. A real Boolean eigenvector is a modular
kernel vector, so the modular type count is a valid upper bound.

For `1<=k<epsilon N/2`, the nonzero vector `tau-sigma` is an eigenvector
at `lambda` supported on `2k<epsilon N` vertices. The following
proposition, already proved in
`../partitioning-rsbm-kernel-session/deterministic-reductions.md`, rules
this out with high probability:

> For every fixed `a>b>=1`, some `epsilon(a,b)>0` satisfies
> `P[exists nonzero real v: Av=(a-b)v, |supp v|<=epsilon N]`
> `=O_{a,b}(N^{-(a+b-2)(a-b+1)})`.

For clarity, its proof uses only a standard configuration exposure
count. Every exterior neighbor of an eigenvector's support has at least
two support neighbors. Exposing the `ds` support stubs thus requires at
least `ds/2` collisions, each of conditional probability `O(s/N)`.
Union bounding support sets gives `[K(s/N)^{(d-2)/2}]^s`. A positive
maximum and a negative minimum of the eigenvector each require at least
`lambda+1` vertices, so `s>=2(lambda+1)`; summing the geometric bound
through `epsilon N` proves the stated rate. Simplicity conditioning
costs only a constant. This applies to all three independent regular
configuration factors, for every admissible `N`.

Combining the small- and large-overlap ranges proves, for `a>=3`,

\[
 \Pr\{\exists\tau\ne\pm\sigma:\tau\in\{\pm1\}^{2N},
                  A\tau=\lambda\tau\}
 =O_{a,b}(N^{-(d-2)(\lambda+1)}).                       \tag{6}
\]

The exponential macroscopic error is absorbed into this bound.

## 6. Deterministic polynomial recovery

For bits `z` and signs `tau_i=(-1)^{z_i}`, having exactly `b` opposite
neighbors implies

\[
 (A+dI)z=(b\bmod2)\mathbf1\quad\text{over }\mathbb F_2. \tag{7}
\]

Since `d-lambda=2b`, the matrix on the left is `A-lambda I` modulo two.
The planted assignment guarantees consistency. Its affine solution
space has exactly `2^{k_2}` points.

Solve (7) exactly. Abort if
`2^{k_2}>n^{C_d+3}`. Otherwise enumerate all affine solutions in
Gray-code order, and test each over the integers for exactly `b`
opposite neighbors at every vertex. By (5), the abort probability is
`O(N^-3)`. Enumeration and verification take a fixed polynomial number
of bit operations, since `d` is fixed and one candidate takes `O(n)`
operations after its binary representation is unpacked. Boolean
rigidity (6) ensures that every accepted candidate is planted up to
global sign with probability tending to one.

Alternatively, compute a rational basis for `ker(A-lambda I)`, cap its
dimension at the corresponding logarithmic threshold, and enumerate the
two sign choices on pivot coordinates. Integer minors of this bounded
degree, bounded diagonal matrix have polynomial bit lengths, so exact
reconstruction and verification have polynomial bit complexity.

This proves the claim for `a>=3`. The separately frozen cubic proof
handles the only remaining case `a=2>b>=1`, namely `(2,1)`.

## What is and is not used

This route uses exact configuration type enumeration, elementary entropy
and Fourier arguments, constant-probability simplicity conditioning,
and the proved small-support estimate. It avoids a sharp finite-field
moment, a growing-prime limit, and any even-block-size matching-sum
assumption. It proves polynomial exact recovery, with coarse running-time
exponents depending on the fixed degrees; it does not prove real
eigenvalue simplicity in the general model.
