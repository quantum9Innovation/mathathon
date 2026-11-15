# Independent audit of the general star-type argument

The cubic manuscript is unchanged. This note audits the later general
argument in `../../GENERAL-POLYNOMIAL-RECOVERY.md` and records a shorter
integer-profile proof of its Boolean rigidity step.

**Conclusion.** The exact count, entropy inequality, polynomial
prefactors, uniform-simple conditioning, and recovery argument check.
They apply to all admissible block sizes for every fixed `a>b>=1` with
`a>=3`. Together with the separate `(2,1)` proof, this covers all fixed
`a>b>0`. No real eigenspace simplicity statement follows or is needed.

## 1. Model, signs, and admissibility

Set `d=a+b`, `lambda=a-b`, and use two independent internal pairings of
`aN` distinguished stubs and a uniform bijection between the two sets of
`bN` cross stubs. There are

\[
 ((aN-1)!!)^2(bN)!
\]

equally likely configurations. The internal pairings are defined when
`aN` is even. For the requested simple model the full conditions are
`N>=a+1`, `aN` even, and `b<=N`. Since `a>b`, the last condition is
automatic from the first. In particular, even `a` allows odd `N`.
For odd `a`, even `N` is necessary for the model itself.

The parent proof uses the original matrix `A-lambda I` and the local
constraint `sum A_i+sum B_j=lambda X`. Equivalently, conjugate by the
planted sign diagonal and use

\[
 M=\begin{pmatrix}C_+-\lambda I&-B\\-B^T&C_--\lambda I\end{pmatrix},
 \qquad \sum_{i=1}^a A_i-\sum_{j=1}^b B_j=\lambda X.
\tag{1}
\]

Changing the signs of all minus-block coordinates is a bijection
between these conventions and preserves all the counting factors and
entropies. The entropy argument works in either convention, including
characteristic two.

## 2. Exact type count

A full plus profile consists of its root `X`, its `a` ordered internal
neighbor labels, and its `b` ordered cross neighbor labels, subject to
(1). A minus profile has the corresponding root `Y` and neighbor slots
`C_1,...,C_a,D_1,...,D_b`. Over `F_p`, there are exactly `p^d` profiles
in each block: the root and all but one internal neighbor label are
free, and the omitted internal label is uniquely determined. This
does not depend on the value of `lambda` modulo `p`.

Let `n^+,n^-` be the two profile-count tables. Let `m^+,m^-` count
internal stubs by ordered host and requested partner labels, and let
`h^+,h^-` count cross stubs in the corresponding orientation. Validity
means

\[
 m^\pm=(m^\pm)^T,\quad m^\pm_{uu}\ \text{even},\qquad
 h^+=(h^-)^T=:h.
\]

Here the minus cross table has its host label first. The parent proof
indexes that table in reversed order, so its displayed condition is
`h^+=h^-`; the two notations agree.

Put

\[
 W(m)=\prod_{u<v}m_{uv}!\prod_u(m_{uu}-1)!!.
\]

The exact identity is

\[
\begin{split}
\mathbb E|\ker_{\mathbb F_p}M|
=\sum_{\text{valid }n^+,n^-}
&\frac{N!}{\prod_s n^+_s!}\frac{N!}{\prod_t n^-_t!}\\
&\times\frac{W(m^+)W(m^-)}{((aN-1)!!)^2}
\frac{\prod_{u,v}h_{uv}!}{(bN)!}.
\end{split}
\tag{2}
\]

The last numerator is a product over **all ordered** label pairs:
cross matching is a bijection between the corresponding plus and minus
stub pools, not an unordered pairing. The internal factors use
unordered label pairs and even diagonal pairings. Distinguished slots
make each configuration and kernel vector determine one profile
assignment, so no factors involving `a!`, `b!`, or orientations belong
in (2). Loops contribute twice on the internal adjacency diagonal and
are counted correctly.

## 3. Entropy inequality

Let `S_+,S_-` be the two profile laws and put

\[
 F_+=m^+/(aN),\quad F_-=m^-/(aN),\quad G=h/(bN).
\]

The exponential rate of a summand of (2), divided by `N`, is

\[
 \Phi=H(S_+)+H(S_-)
 -\frac a2\{H(F_+)+H(F_-)\}-bH(G).
\tag{3}
\]

Average each profile law over all permutations of its internal slots
and separately all permutations of its cross slots. This leaves the
stub tables, local equation, and root laws unchanged, and increases
profile entropy. It therefore suffices to bound the symmetrized laws.
Write `P=law(X)`, `Q=law(Y)`. Validity implies

\[
 \mathcal L(A)=\mathcal L(D)=P,\qquad
 \mathcal L(C)=\mathcal L(B)=Q,
\]

and the pair laws are

\[
 F_+=\mathcal L(X,A),\quad F_-=\mathcal L(Y,C),\quad
 G=\mathcal L(X,B)=\mathcal L(D,Y).
\]

Omitting one internal neighbor in (1), then using conditional
subadditivity, gives

\[
\begin{split}
H(S_+)&\le H(X)+(a-1)H(A\mid X)+bH(B\mid X),\\
H(S_-)&\le H(Y)+(a-1)H(C\mid Y)+bH(D\mid Y).
\end{split}
\]

For example, the first bound equals

\[
 aH(P)+bH(Q)-(a-1)I(X;A)-bI(X;B).
\]

Substitution into (3) cancels the marginal entropies and yields

\[
\boxed{\quad
 \Phi\le-\left(\frac a2-1\right)
             \{I(X;A)+I(Y;C)\}-bI(X;B)\le0.
\quad}
\tag{4}
\]

This checks the stated coefficients exactly. It holds for `a>=2`.
The argument needs neither `a>b` nor a nonzero `lambda` for the
nonpositive moment exponent itself.

## 4. Explicit prefactors

Let `q=p(p+1)/2`. The zero-safe bounds

\[
 r\log r-r\le\log r!
 \le r\log r-r+1+\log(r+1)
\]

give, for every valid internal table,

\[
 \frac{W(m)}{(aN-1)!!}
 \le e^{q+1}(aN+1)^{q+1}e^{-(aN/2)H(F)}.
\]

Similarly, using the lower bound for `(bN)!` and the upper bound for
each of the `p^2` numerator factorials,

\[
 \frac{\prod h_{uv}!}{(bN)!}
 \le e^{p^2}(bN+1)^{p^2}e^{-bNH(G)}.
\]

Each multinomial is bounded above by the exponential of its profile
entropy times `N`. There are at most `(N+1)^{2p^d}` pairs of profile
types. Consequently

\[
\boxed{\quad
\mathbb E|\ker_{\mathbb F_p}M|
\le e^{2(q+1)+p^2}(aN+1)^{2(q+1)}(bN+1)^{p^2}
      (N+1)^{2p^d}.
\quad}
\tag{5}
\]

Thus the binary moment is `O_{a,b}(N^{C_d})`, where

\[
 C_d=12+2^{d+1}.
\]

The type count is deliberately loose but finite-degree polynomial.
There is no uniform-in-growing-`p` assertion.

## 5. Exact transfer to uniform simple factors

Every simple internal `a`-regular labeled graph has exactly `(a!)^N`
distinguished-stub pairing realizations. Every simple cross
`b`-regular bipartite graph has exactly `(b!)^{2N}` cross-stub
bijection realizations. Because the three configurations are
independent, conditioning each on simplicity gives exactly the three
independent uniform simple factors in the question.

For fixed degrees, the internal simplicity probability tends to
`exp(-(a^2-1)/4)`, and the bipartite simplicity probability tends to
`exp(-(b-1)^2/2)`. In particular their joint probability is bounded
away from zero. These are fixed-degree specializations of the
configuration-model simplicity results, including the bipartite case,
in [Janson, *The probability that a random multigraph is simple,
II*](https://arxiv.org/abs/1307.6344). Therefore conditioning changes
the nonnegative moment bound by only a degree-dependent constant.

## 6. Audit of the parent's modular equality classification

For `a>=3`, the parent proof's classification is valid when `p` is an
odd prime with `p` not dividing `b`.

At equality, all the mutual informations in (4) vanish. Equality in
the conditional entropy bound makes the retained neighbors jointly
independent with their respective marginal laws, independently of the
root. For the parent's unconjugated convention this gives

\[
 \widehat P(t)=\widehat P(\lambda t)
              \widehat P(-t)^{a-1}\widehat Q(-t)^b.
\]

Thus `r=|P_hat(t)|` satisfies `r<=r^{a-1}`, so `r` is zero or one.
Every nonzero additive character of a prime field is injective. A
non-point law therefore has no nonzero Fourier coefficient of modulus
one, and must be uniform. If one root law is a point mass, the
independent cross-neighbor sum being constant forces the other root
law to be a point mass. The local equation then yields
`b(c+e)=0`, and `p` not dividing `b` gives `e=-c`.

The prime restriction matters: if `p` divides `b`, arbitrary independent
constants on the two planted blocks are modular kernel vectors, giving
additional constant phases. This causes no difficulty for (5) or its
use at `p=2`; it matters only if one wants that particular phase
classification.

## 7. A shorter Boolean rigidity proof using integer profiles

One can avoid the modular equality classification entirely for the
Boolean rigidity step. Let `tau` be a Boolean eigenvector at `lambda`
and define its mark vector by

\[
 \tau=\sigma(1-2z),\qquad z\in\{0,1\}^{2N}.
\]

Since `A sigma=lambda sigma`, the marks satisfy the **integer** equation

\[
 Mz=0.
\]

Thus the exact local mark constraint is (1), with all labels restricted
to the integer alphabet `{0,1}`. Formula (2) counts such mark vectors
exactly if the local profile set is restricted to this integer
constraint. There are at most `2^d` allowed profiles per block, because
the omitted internal bit is determined and may sometimes fall outside
the bit alphabet. The entropy proof (3)--(4) still applies: it only
uses that this slot is determined, slot permutation invariance, and
edge consistency.

Balance of the Boolean eigenvector implies equal marked proportions
`alpha=k/N` in the two blocks. For alternatives, choose the global
orientation so `0<alpha<=1/2`. Both root laws are Bernoulli(`alpha`).
If `Phi=0` and `a>=3`, (4) forces all displayed pair mutual
informations to vanish. In particular, conditional on the plus root
`X=0`, every internal and every cross neighbor still has mean `alpha`.
Taking the conditional expectation of (1) gives

\[
 (a-b)\alpha=\lambda\,0=0,
\]

which is impossible because `lambda=a-b>0` and `alpha>0`. The event
`X=0` has positive probability since `alpha<=1/2`.

For any fixed `epsilon>0`, compactness of the finite-dimensional
feasible profile-law set with
`epsilon/2<=alpha<=1/2` now gives a uniform strictly negative entropy
gap. Polynomial type counts and factorial errors give an exponentially
small expected number of alternatives in this overlap range. The
already proved small-support proposition handles
`0<2k<epsilon N`, with probability

\[
 O_{a,b}\bigl(N^{-(d-2)(\lambda+1)}\bigr).
\]

Simplicity conditioning again costs a constant. This recovers the
parent's Boolean rigidity conclusion directly, without Fourier
analysis or any restriction on a prime.

## 8. Recovery and scope

For labels `z` representing a sign partition, the necessary parity
equation is

\[
 (A+dI)z=(b\bmod2)\mathbf1\quad\text{over }\mathbb F_2.
\]

Since `d-lambda=2b`, its homogeneous matrix is `A-lambda I` modulo two.
The planted assignment makes it consistent. The affine solution set
has `2^k` members, where the moment in (5) bounds `E 2^k` polynomially.
A cutoff at `n^{C_d+3}` fails with probability `O(N^-3)`; Gray-code
enumeration and checking exactly `b` opposite neighbors give a fixed
polynomial worst-case algorithm. Boolean rigidity identifies every
accepted assignment with the planted partition, up to exchange, with
probability tending to one. No cutoff is needed for expected polynomial
listing of every equitable partition.

The boundary `a=2,b=1` needs its separate Boolean rigidity argument,
because the internal mutual-information coefficient in (4) vanishes.
That case is supplied by the frozen cubic proof. No further pairs
`a>b>0` remain.
