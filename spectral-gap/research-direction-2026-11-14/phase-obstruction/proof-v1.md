# A phase-insensitive tangle in the single-phase K4 lift

Date: November 14, 2026, America/Los_Angeles.

Status: frozen candidate proof, awaiting separate exact-revision review. This is a bounded obstruction to the original one-phase proposal. It is not an end-to-end formal proof, a priority claim, or a classification of all tangles.

## 1. Model and statement

Let the base graph be K4 on colors 1, 2, 3, 4. For every unordered base edge choose an independent uniform bijection between its two fibers of size n. This defines the ordinary permutation n-lift, with 4n vertices. Orient each base edge once. Give all lifted edges above 34 the same scalar phase zeta of modulus one, give the other edges phase one, and use the conjugate coefficient in the reverse direction. Write A_zeta,n for the resulting Hermitian adjacency matrix.

Let P be the orthogonal projection onto vectors constant on each of the four fibers, and Q=I-P. Both sectors are invariant under A_zeta,n. The normalized adjacency is A_zeta,n/3. No conditioning on connectivity is imposed.

Let r be the unique positive root of

\[
r^3-r-2=0,
\]

and set

\[
\lambda_*=r+\frac2r,
\qquad \delta_*=\lambda_*-2\sqrt2>0.
\]

For every fixed raw-adjacency excess delta with 0<delta<delta_*, there are finite constants C_delta and N_delta such that, for all n>=N_delta and every unit phase zeta,

\[
\Pr\left\{\lambda_{\max}\left(A_{\zeta,n}|_{\operatorname{ran}Q}\right)
>2\sqrt2+\delta\right\}
\ge \frac1n-\frac{C_\delta}{n^2}.
\tag{1}
\]

The good graph event used below works for every phase simultaneously. In particular, (1) remains valid for any deterministic n-dependent sequence of phases. It also applies if a phase is selected after seeing the lift, because the implication from the good event is simultaneous.

For normalized adjacency, the allowed excess is 0<epsilon<delta_*/3 and the threshold is 2sqrt(2)/3+epsilon. The same lower bound applies to the operator norm, since that norm dominates the largest eigenvalue.

Numerically, r is approximately 1.521379706805, lambda_* is approximately 2.835975919081, and delta_*/3 is approximately 0.002516264778. These decimals are orientation only. The exact algebraic definitions determine the theorem.

## 2. A local state above the tree edge

Let S be K4 with edge 34 removed. Complete each degree-two vertex, 3 and 4, with one infinite binary-tree branch. More explicitly, attach one new neighbor to each of 3 and 4, and give every added vertex two further children. The resulting infinite graph H is 3-regular. Its only cycles lie in S.

The cubic has exactly one positive root. Its value at sqrt(2) is sqrt(2)-2<0, and its value at 2 is 4>0. Its derivative is positive on [sqrt(2),infinity), so

\[
\sqrt2<r<2.
\]

Consequently lambda_*>2sqrt(2), since r+2/r is strictly increasing for r>sqrt(2).

Put

\[
b=\frac{\lambda_*-1}{2},\qquad q=\frac2{r^2}<1.
\]

Define f to equal 1 at colors 1 and 2 in the core, b at core vertices 3 and 4, and b r^{-k} at every added vertex at distance k>=1 from the core. At a branching vertex, the eigenvalue equation is

\[
\lambda_* b r^{-k}=b r^{-(k-1)}+2b r^{-(k+1)}.
\]

At core vertices 1 and 2 it is lambda_*=1+2b. At core vertices 3 and 4 it is lambda_* b=2+b/r. The latter identity follows from

\[
(\lambda_*-1)(\lambda_*-r^{-1})-4
=\frac{(r-1)(r^3-r-2)}{r^2}=0.
\]

There are 2^k added vertices at depth k. Hence

\[
\|f\|^2=2+2b^2+b^2\sum_{k\ge1}q^k<\infty.
\]

Thus f is a genuine square-summable eigenfunction of H with eigenvalue lambda_*. This is the standard localized-state mechanism associated with a supercritical tangle.

Let f_R be its truncation to the core and vertices of depth at most R, allowing R=0. Its support has

\[
M_R=4+\sum_{k=1}^{R}2^k=2^{R+1}+2
\]

vertices. Set

\[
S_R=\|f_R\|^2=2+2b^2+b^2\sum_{k=1}^{R}q^k.
\]

There are 2^{R+1} edges crossing from depth R to depth R+1. Therefore its exact Rayleigh quotient is

\[
\mathcal R_R
=\frac{\langle f_R,A_H f_R\rangle}{S_R}
=\lambda_*-\frac{2b^2q^R}{r S_R}
\longrightarrow\lambda_*.
\tag{2}
\]

This formula includes R=0, where the two crossing edges leave core vertices 3 and 4.

## 3. Occurrence probability of the colored core

A colored copy of S is a tuple (x_1,x_2,x_3,x_4), choosing one vertex in each fiber and satisfying the five prescribed edge matches in S. Let X count these copies. Each tuple has probability n^{-5}, because it prescribes one match in each of five independent permutations. There are n^4 tuples, so

\[
\mathbb E X=\frac1n.
\tag{3}
\]

Two distinct realized colored copies cannot share a vertex. Equality at one color forces equality at adjacent colors by the bijection along that edge. Since S is connected, it forces equality at all colors.

The ordered pairs of disjoint tuples number [n(n-1)]^4. On each of the five independent base edges, the two required matches have probability 1/[n(n-1)]. Therefore, for n>=2,

\[
\mathbb E[X(X-1)]=\frac1{n(n-1)}.
\tag{4}
\]

## 4. Clean finite neighborhoods

Fix R. Conditional on the five matches of a specified core, expose all edges out to depth R+1 from the two missing core ports. Require every newly exposed target to be a fresh vertex outside the previously discovered vertices. This event realizes the truncated graph H through depth R+1 with no additional identifications. In particular, the induced graph on the support of f_R contains exactly the core edges and the attached tree edges. Exposing the extra layer prevents hidden edges between support boundary vertices.

The total number of vertices in the successful exposure is

\[
B_R=2^{R+2}+2.
\]

At most 3B_R permutation entries are fixed or queried during this exposure, including the original constraints. Conditional on all earlier queries and on their consistency, a new image or preimage is uniform over the unused vertices in its target fiber. At most B_R candidates are forbidden. For n>=6B_R, the conditional probability of a collision at any particular query is at most 2B_R/n. A union bound gives

\[
\Pr\{\text{clean radius }R+1\mid\text{specified core}\}
\ge 1-\frac{6B_R^2}{n}.
\tag{5}
\]

The constant is deliberately loose. No logarithmically growing neighborhood is being exposed.

Let Y count cores whose radius R+1 exposure is clean. Equations (3) and (5) imply

\[
\mathbb E Y\ge\frac1n-\frac{6B_R^2}{n^2}.
\]

Since Y<=X, equation (4) and the elementary inequality 1_{y>=1}>=y-y(y-1)/2 for nonnegative integers y yield

\[
\Pr\{Y\ge1\}
\ge\frac1n-\frac{6B_R^2}{n^2}-\frac1{2n(n-1)}
\ge\frac1n-\frac{6B_R^2+1}{n^2}.
\tag{6}
\]

All these graph events are independent of the phase parameter.

## 5. Gauge and the new sector

On the clean support, all cycles are in S, whose edge phases are one. A diagonal unitary change of coordinates can remove every phase on its attached trees while leaving the core unchanged. Transfer the normalized truncated vector f_R/sqrt(S_R) through this gauge to the finite lift and extend it by zero. Call the resulting unit vector u_zeta. Its support has M_R vertices and

\[
\langle u_\zeta,A_{\zeta,n}u_\zeta\rangle=\mathcal R_R
\]

for every zeta.

Let s=||P u_zeta||^2. Fiberwise Cauchy-Schwarz gives

\[
s=\frac1n\sum_{i=1}^{4}\left|\sum_{x\text{ in fiber }i}u_\zeta(x)\right|^2
\le\frac{M_R}{n}.
\tag{7}
\]

The old and new sectors are invariant because each edge block is a scalar multiple of a permutation matrix. Also ||A_zeta,n||<=3, by the absolute row-sum bound for this Hermitian matrix. Thus, when n>=2M_R, Q u_zeta is nonzero and

\[
\frac{\langle Q u_\zeta,A_{\zeta,n}Q u_\zeta\rangle}
{\|Q u_\zeta\|^2}
\ge\frac{\mathcal R_R-3s}{1-s}
\ge\mathcal R_R-\frac{6M_R}{n}.
\tag{8}
\]

This estimate is uniform over all unit phases.

## 6. Completion

Fix delta in (0,delta_*) and let Delta=lambda_*-2sqrt(2)-delta>0. Choose R so that

\[
\frac{b^2}{r}q^R<\frac{\Delta}{4}.
\]

Since S_R>=2, equation (2) then gives R_R>lambda_*-Delta/4. Choose

\[
N_\delta\ge\max\{2,6B_R,2M_R,24M_R/\Delta\}.
\]

For n>=N_delta, equation (8) exceeds 2sqrt(2)+delta on the event Y>=1. The variational principle on the invariant new sector now gives (1) from (6), with C_delta=6B_R^2+1. Every step holds simultaneously for all phases. This completes the candidate argument.

## 7. Interpretation and limits

The single phase cannot improve the order 1/n fixed-excess upper tail to o(1/n) throughout the interval 0<delta<delta_*. This conclusion is stronger than the familiar fact that tree phases can be gauged away. It identifies a phase-insensitive rare obstruction at finite n.

It does not rule out better multiplicative constants, larger-threshold gains, a better dependence on the excess, conditional estimates excluding the offending tangles, changes to several independent base-cycle phases, or improvements in the small old sector. It does not show that this core is the only obstruction, classify the exact tail coefficient, or give a useful numerical n threshold. The conservative truncation constants are very large near the tree edge.

For each fixed phase, the O(1/n) upper bound at fixed positive excess follows from the existing matrix-polynomial strong-convergence theorem described in SOURCES.md. Combining that external theorem with (1) gives order 1/n in the displayed excess range. The lower bound itself is proved here without that upper theorem.
