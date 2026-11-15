# Sharp transition between collective and close-pair spectral effects

November 15, 2026. Integrator: root. Revision 1, frozen for independent synthesis review.

## Model

Let A_n be the adjacency matrix of a uniformly random simple labelled d-regular graph, with fixed d>=3 and nd even. Choose m=m(n)>=1 distinct labels before sampling the graph, and let E select their coordinates. Define

\[
\mathcal A_H=\begin{pmatrix}A_n&\sqrt{d-2}A_nE\\
\sqrt{d-2}E^\top A_n&sH\end{pmatrix},\qquad
s=\sqrt{m/n},\quad a=m^2/n,\quad\theta=a/s=\sqrt{m^3/n}.
\]

Here H is real symmetric and bounded in operator norm independently of n. The original cubic graph construction is d=3 and H=0: each added vertex is joined to all original neighbours of one marked vertex. For other d the critical attachment is weighted.

Write the augmented eigenvalues in descending order as mu_j. Put

\[
D_d=\frac{2(d-1)^2}{(d-2)^2},\quad
\kappa_d=\frac{d(d-2)^{3/2}}{\sqrt2(d-1)},\quad
\beta_d=\frac{d^2(d-2)}{6(d-1)^2},\quad e=\frac{\mathbf1_m}{\sqrt m}.
\]

## The sharp collective criterion

Within the dilute range m=o(n), the following equivalence holds for H=0:

\[
\frac{\mu_1-d}{\sqrt{m/n}}\xrightarrow{\mathbb P}\kappa_d
\quad\Longleftrightarrow\quad
\frac{m^3}{n}\longrightarrow0.                            \tag{1}
\]

In the sufficient range, the stronger full cluster statement holds. Uniformly over every fixed symmetric norm ball ||H||<=H_0, the ordered eigenvalues of

\[
\frac{\mathcal A_H-dI}{s}
\]

in its top m+1 cluster match those of

\[
M_{d,m}(H)=\begin{pmatrix}0&\kappa_d e^\top\\
\kappa_d e&H/D_d\end{pmatrix}
\]

with maximal error tending to zero in probability. The remaining eigenvalues stay below the original second eigenvalue by interlacing. For H=0 the effective eigenvalues are +kappa_d, -kappa_d and m-1 zeros. The previously proved eigenvector mass fractions also hold in this enlarged range.

Sufficiency is the new log-free marked-resolvent estimate combined with the frozen SG-20 transfer and SG-21 eigenvector arguments. All other hypotheses of those arguments are checked at the end of the new upper proof.

For necessity, suppose m^3/n does not tend to zero. There is a subsequence on which theta>=theta_0>0. On that subsequence m tends to infinity. The pair lower bound gives, for every fixed K>0,

\[
\liminf\mathbb P\{(\mu_1-d)/s>K\}
\ge\frac{\beta_d\theta_0}{K+\beta_d\theta_0}>0.             \tag{2}
\]

Choose K>kappa_d. This contradicts the convergence on the left side of (1). The same argument rules out the uniform bounded-H cluster approximation outside the sufficient range, since its norm ball contains H=0.

## What happens at and above the threshold

If m/n^(1/3)->c in (0,infinity), the normalized whole cluster is tight. For the top eigenvalue with H=0, however,

\[
\liminf\mathbb P\{(\mu_1-d)/s>K\}
\ge\frac{\beta_d c^{3/2}}{K+\beta_d c^{3/2}}               \tag{3}
\]

for every fixed K>0. Thus the critical top does not converge in probability to any finite constant. The large values have reciprocal tail lower bounds. The variable-cutoff upper estimate also gives a reciprocal tail upper bound, with unspecified constants, for the limiting upper probabilities as K grows. This describes a genuine transition, without asserting the existence of a limiting distribution.

If n^(1/3)<<m<<sqrt(n), then

\[
\mu_1-d=\Theta_{\mathbb P}(m^2/n),                        \tag{4}
\]

uniformly over ||H||<=H_0. Here this notation means both that (mu_1-d)/(m^2/n) is tight uniformly in H and that its infimum over H is bounded away from zero in probability. It does not mean convergence to a deterministic constant. More precisely,

\[
\liminf\mathbb P\left\{
\inf_{\|H\|\le H_0}\frac{\mu_1(H)-d}{m^2/n}>K\right\}
\ge\frac{\beta_d}{K+\beta_d}.                            \tag{5}
\]

Throughout the larger supercritical dilute range n^(1/3)<<m<<n, the infimum over bounded H of (mu_1-d)/s tends to positive infinity in probability. A matching upper scale is asserted only below sqrt(n).

The entire top m+1 cluster has width

\[
O_{\mathbb P}\bigl(\max\{\sqrt{m/n},m^2/n\}\bigr)
\]

when m=o(sqrt(n)). This follows from the centered resolvent bound and a finite monotonicity comparison, with no simplicity or separation assumption on the eigenvalues inside the cluster.

## A consequence for expectations

At criticality, although X_n=(mu_1-d)/s is tight for H=0, its expectation tends to positive infinity. In the range of (4), the same is true for (mu_1-d)/(m^2/n). This is a consequence of the probability lower bounds, not an additional estimate of the precise growth rate.

Indeed, these nonnegative random variables satisfy, with a fixed b>0,

\[
\liminf_n\mathbb P(X_n>K)\ge\frac b{K+b}\quad(K>0).
\]

For every finite L, the tail-integral identity and Fatou's lemma give

\[
\liminf_n\mathbb E X_n
\ge\int_0^L\frac b{K+b}\,dK
=b\log(1+L/b).
\]

Letting L tend to infinity proves the claim. Nonnegativity follows from interlacing with the host. Thus an average can be dominated by rare pairs even when the typical scale is controlled. No exact logarithmic expectation asymptotic is claimed.

## Why the exponent is one third

A radius-r ball contains order (d-1)^r vertices. Among m predetermined marks, the expected number of close pairs has order

\[
\frac{m^2(d-1)^r}{n}.
\]

The tree Green interaction of a pair at distance r has order (d-1)^(-r). Matching this to the collective scale s gives an expected close-pair count of order

\[
\frac{m^2}{ns}=\sqrt{m^3/n}.
\]

The proof makes each step quantitative. Below the threshold, short paths between marks can be excluded with probability tending to one. The remaining interactions are controlled through squared mass, which removes the logarithm introduced by summing all their absolute values. Above the threshold, a close pair supplies a negative Schur quadratic form and therefore an actual eigenvalue beyond the collective edge. This is a competition between collective coupling to the host's constant mode and interactions determined by local graph distance.

## Frozen proof dependencies

- Log-free estimate: [nonbacktracking-upper-v1.md](nonbacktracking-upper-v1.md), SHA256 d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896.
- Distinct polynomial proof: [chebyshev-proof-v1.md](../probability/chebyshev-proof-v1.md), SHA256 d9265e631ea99465eb243aaeecda7ad5a6d27c92b977ebe3b4cf185ac411a011. This route uses a stronger published host-spectrum rate.
- Cubic lower bound: [proof-v1.md](../obstruction/proof-v1.md), SHA256 cadd1408ff45526a328b78f7b2f063fa599278603e90282c216e364c68280a35.
- Fixed-degree extension: [weighted-extension-v1.md](../obstruction/weighted-extension-v1.md), SHA256 3ffd9f003e3e4c3d94be96a9ff831f666da815e631eed531cdcbf1ba5d0f33d1.
- Pair-scale lower bound: [pair-scale-v1.md](../obstruction/pair-scale-v1.md), SHA256 272cdb331e73e23aecc36685cb62211c9733d50022e438c6e7fa7f5fb18c505a.
- Cluster upper bound: [cluster-width-v1.md](cluster-width-v1.md), SHA256 e40164dcf711cca13d945b666645c26aa8095b835e1e727d2d6d7159a78e7b8f.
- Earlier structural transfer and eigenvector proofs remain frozen in the preceding round and attached to SG-20 and SG-21.

## Scope and the next question

These are paper theorems with separate internal proof reviews. The finite formal components verify only their recorded identities and inequalities. They do not encode the full random-graph theorem. Priority comparison credits existing deformation, scattering, nonbacktracking and splitting-graph methods. No historical-firstness or resolution of an exact published open problem is claimed.

The natural next target is the critical distribution: can one retain a sparse matrix of close-pair interactions together with the collective mode, and prove its limiting spectral law? Graph distance is integer valued, so a full-sequence limit might require a correction or fail in favour of subsequential limits. That question remains open here. Spatial localization of pair modes is also unproved. Neither gap is needed for the sharp criterion (1).
