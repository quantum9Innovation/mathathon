# A precise obstruction to transferring kernel relative error to normalized cut

Date: 2026-11-15. This is an independently derived algebraic scope audit, not a claim that a published data structure is incorrect in every formulation.

## Source and inspected claim

[Jourdan, Macgregor, and Schwartzman, *Fully Dynamic Coreset Spectral Clustering*, ICML 2026](https://proceedings.mlr.press/v306/jourdan26a.html), Appendix A, Definition 6, equation (16), and Appendix F, Theorem 6, were inspected in the actual proceedings PDF (`dynamiccoreset2026.pdf`). Definition 6 uses average conductance. Equation (16) writes an equivalent optimization problem after an additive change of objective. A multiplicative approximation requires accounting for that additive change. The graph kernel in Definition 3 also includes a positive diagonal shift.

The following calculation identifies exactly what must be accounted for. It does not audit the entire algorithm or its proof.

## Identity

Let a weighted undirected graph have positive degrees, adjacency matrix A, degree matrix D, and n vertices. A partition into k nonempty sets has indicator matrix X. Put

\[
 Z=D^{1/2}X(X^TDX)^{-1/2},\qquad B=D^{-1/2}AD^{-1/2}.
\]

Then Z^TZ=I_k, and the classical average normalized-cut objective is

\[
 \operatorname{NC}(\Pi)=\frac1k\sum_i\frac{w(S_i,V\setminus S_i)}{\operatorname{vol}(S_i)},
 \qquad k\operatorname{NC}(\Pi)=k-\operatorname{tr}(Z^TBZ).
\]

For the positive definite graph kernel

\[
 K_\sigma=D^{-1}AD^{-1}+\sigma D^{-1},\quad W=D,
\]

the weighted kernel k-means cost for this same partition is

\[
 J_\sigma(\Pi)=\operatorname{tr}(DK_\sigma)
 -\operatorname{tr}(Z^TD^{1/2}K_\sigma D^{1/2}Z).
\]

Direct substitution gives the exact formula

\[
 \boxed{J_\sigma(\Pi)=k\operatorname{NC}(\Pi)
 +\operatorname{tr}(D^{-1}A)-k+\sigma(n-k).}
\]

All terms outside NC are independent of the partition. Thus exact minimizers agree. Relative approximation factors need not agree. If the additive constant is c, a guarantee J_sigma(Pi)<=a J_sigma(OPT) gives only

\[
 k\operatorname{NC}(\Pi)\le a k\operatorname{NC}(\mathrm{OPT})+(a-1)c.
\]

This distinction is essential when OPT is small.

## Explicit connected, regular, balanced counterexample to the transfer implication

Take the unweighted even cycle C_n, n>=6, k=2, and sigma=2. Its degrees are two. Since all eigenvalues of B lie in [-1,1], K_2 is strictly positive definite. For this loopless graph c=2n-6.

Let Pi_good partition the cycle into two contiguous arcs of n/2 vertices. Each part has boundary two and volume n. Hence

\[
 \operatorname{NC}(\Pi_{\rm good})=2/n,
 \qquad J_2(\Pi_{\rm good})=2n-6+4/n.
\]

This partition is an exact NC minimizer: every nontrivial cycle cut has at least two boundary edges, and for a part of size s,

\[
 \operatorname{NC}(\{S,S^c\})\ge\frac12(1/s+1/(n-s))\ge 2/n.
\]

Let Pi_bad partition by parity. Both parts still have n/2 vertices; every edge crosses. Therefore

\[
 \operatorname{NC}(\Pi_{\rm bad})=1,
 \qquad J_2(\Pi_{\rm bad})=2n-4.
\]

Consequently

\[
 \frac{J_2(\Pi_{\rm bad})}{J_2(\Pi_{\rm good})}
 =\frac{n}{n-1}=1+\frac1{n-1},
 \quad
 \frac{\operatorname{NC}(\Pi_{\rm bad})}{\operatorname{NC}(\Pi_{\rm good})}=n/2.
\]

For every fixed epsilon>0, sufficiently large even n makes Pi_bad a (1+epsilon)-approximation for J_2 while its genuine NC approximation ratio diverges. This remains true under exact balance, bounded degree, connectivity, and a valid positive definite graph kernel.

This proves that a multiplicative approximation to J_sigma, by itself, is insufficient to infer the same multiplicative approximation to classical NC. A coreset algorithm might have additional properties that avoid this example; those would need a separate argument. This audit does not construct an actual execution of the published algorithm returning Pi_bad.

## Consequence for our frontier

A relative fractional-response approximation controls a positive quadratic form. It cannot silently be converted to relative error for a partition objective formed by subtracting a large constant from that form. Any proposed dynamic normalized-cut application must state and prove its objective conversion, including the diagonal kernel shift, before claiming a gap-free partitioning guarantee. The cycle calculation supplies an immediate exact regression test for such a conversion.

`check_shift_identity.py` verifies these identities using exact rational arithmetic; it is corroboration of the elementary calculation, not an algorithmic benchmark.
