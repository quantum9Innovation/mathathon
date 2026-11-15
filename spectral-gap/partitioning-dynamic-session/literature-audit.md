# Spectral partitioning: primary-literature audit

Research date: 15 November 2026. Scope: adversarial edge edits, balanced graph partitions, hard spectral projectors, and their soft substitutes. This is a bounded literature audit, not a certification of historical priority.

## Findings that change the research target

1. **A generic dynamic clustering approximation is already available.** Jourdan, Macgregor, and Schwartzman (ICML 2026) state a fully dynamic weighted-graph result with logarithmic edge update time and a normalized-cut approximation inherited from an algorithm on a small coreset. A nearly linear reconstruction of a fractional response is not, by itself, an improvement to this dynamic result.
2. **Relative eigenspace perturbation bounds are classical.** Replacing an absolute gap by a relative gap or replacing a norm by an edge-sensitive residual does not by itself remove the need for separation.
3. **“Gap-free clustering” already has an established meaning in planted clustering.** Removing a size/eigengap between recovered and unrecoverable SBM clusters has prior results. This is different from obtaining adversarial stability for an arbitrary graph at an arbitrary spectral cutoff.
4. **The proposed all-scale hard-projector target meets an established obstruction.** Anderson orthogonality work gives logarithmically growing Hilbert–Schmidt leakage of sharp spectral projections under local perturbations. The published continuum theorems are a mechanism and prior-art warning; a graph single-edge counterexample still requires a graph proof.
5. **Soft-resolvent trace budgets are classical.** The exact integrated identity below is an immediate rank-one resolvent/trace-determinant calculation. It is useful, but cannot be sold as a breakthrough.

## Primary sources and exact boundaries

### Jourdan–Macgregor–Schwartzman, ICML 2026

[Fully Dynamic Coreset Spectral Clustering, PMLR 306, 54725–54740](https://proceedings.mlr.press/v306/jourdan26a.html). Full published PDF is saved in `literature/jourdan2026.pdf`; its text is in `literature/jourdan2026.txt`.

Theorem 6, Appendix F, treats a dynamic **weighted** undirected graph, with edge insertion/deletion and implicit vertex insertion/removal. It states edge update time `O(log n_i)` and, at query time, an `alpha(1+epsilon)/(1-epsilon)`-consistent normalized-cut labeling with high constant probability, conditional on an `alpha`-approximation algorithm for normalized cut on the coreset. Query cost includes `k d_max^2 log n`, coreset construction, the small-graph optimization, and labeling queried vertices. The coreset has `O(epsilon^-4 k^2)` vertices. There is no explicit eigengap assumption in Theorem 6. This is an objective guarantee, not a bound on movement of a maintained partition or spectral subspace. The theorem does not state a simultaneous, adaptive-adversary, all-times high-probability guarantee; avoid adding one. The paper uses degree-volume normalized cut, not a fixed unit-mass balance constraint.

**Audit caution:** its conversion between normalized cut and kernel k-means is presented as trace objectives “up to a constant”; any attempt to build on its exact multiplicative approximation transfer should independently verify that normalization and additive constants are handled correctly. This note records the published theorem and does not independently certify that proof.

### Laenen–Sun, NeurIPS 2024

[Dynamic Spectral Clustering with Provable Approximation Guarantee, arXiv:2406.03152](https://arxiv.org/abs/2406.03152); [full primary text](https://arxiv.org/html/2406.03152v1).

The model permits edge insertions and new vertices, and assumes changing but well-defined cluster structure at designated times. The stated amortized update cost is `O(1)` and query cost `o(n_T)` (specifically `O(n/log n)` in the comparison in the 2026 paper). It maintains a cluster-preserving sparsifier and contracted graph. This is neither a fully adversarial deletion theorem nor a stability guarantee for the labels before and after an edit. It already addresses adaptation to a changing number of clusters.

### Peng–Yoshida, KDD 2020

[Average Sensitivity of Spectral Clustering, arXiv:2006.04094](https://arxiv.org/abs/2006.04094); [full primary text](https://arxiv.org/html/2006.04094v1).

The sensitivity is an expected symmetric difference after **random** edge removals. The bounds use spectral cluster structure, including dependence of the form `lambda_2/lambda_3^2`, with separate normalized/unnormalized analyses and a k-way extension. This is direct prior art for partition-label sensitivity, but does not imply adversarial edit stability without a separation condition. Its discussion already warns of adversarial fragility and dangling sets. A balanced, connected, single-positive-edge counterexample would be a stronger and cleaner obstruction than the disconnected-singleton example discussed there.

### Li, SIAM J. Matrix Anal. Appl. 1998

[Relative Perturbation Theory: II. Eigenspace and Singular Subspace Variations](https://doi.org/10.1137/S0895479896298506).

Li extends Davis–Kahan/Wedin to multiplicative perturbations, bounding subspace changes through reciprocal **relative** spectral gaps. This blocks novelty claims based solely on a multiplicative Laplacian form comparison followed by a relative sin-theta estimate. A leverage-sensitive graph specialization may still improve an application, but the perturbation mechanism is established.

### Peng–Sun–Zanetti, COLT 2015

[Partitioning Well-Clustered Graphs: Spectral Clustering Works!, PMLR 40](https://proceedings.mlr.press/v40/Peng15.html).

The paper analyzes bottom-eigenvector embeddings followed by k-means for well-clustered graphs and gives a nearly linear algorithm via heat-kernel embeddings. Approximation and rounding guarantees under strong spectral cluster structure are established; combining Cheeger/relative-form comparison with these guarantees needs a new ingredient before becoming a new partitioning theorem.

### Zurek–Chen, COLT 2024

[Gap-Free Clustering: Sensitivity and Robustness of SDP, PMLR 247](https://proceedings.mlr.press/v247/zurek24a.html).

Their SDP recovers sufficiently large SBM clusters despite small unrecoverable clusters, without a size gap between the two classes. They develop leave-one-out arguments near the recovery threshold and semirandom robustness. The paper also identifies gap-free **spectral** predecessors by Mukherjee et al. (2022) and Mukherjee–Zhang (2022). Thus “first gap-free clustering” is not a viable generic claim. These random-model guarantees do not settle an arbitrary-graph, leverage-budget recourse theorem.

### Bhaskara et al., arXiv:2412.14315

[On the Robustness of Spectral Algorithms for Semirandom Stochastic Block Models](https://arxiv.org/abs/2412.14315); [full primary text](https://arxiv.org/html/2412.14315v1).

The semirandom modifications add internal edges or increase internal edge probabilities. The authors prove unnormalized spectral bisection recovery under stated density and gap hypotheses, and construct a family where normalized spectral bisection makes a constant fraction of errors. This is a normalization warning: a positive edit of the combinatorial Laplacian is not a PSD rank-one update of its symmetric normalized counterpart, because the degree matrix also changes. Helpful edits relative to a planted objective need not help a particular spectral algorithm.

### Gebert, arXiv:1705.02796v2 (2018)

[On an integral formula for Fredholm determinants related to pairs of spectral projections](https://arxiv.org/abs/1705.02796); [full primary text](https://arxiv.org/html/1705.02796v2). PDF and extracted text are saved in `literature/`.

For `B=A+phi phi*`, Theorem 2.1 expresses the logarithm of a section determinant through a double integral of the spectral shift function. Corollary 2.4 gives

`-log det(I-(P_I(A)-P_I(B))^2) = 2 integral_I integral_Ic xi(x)xi(y)/(y-x)^2 dx dy`.

Its assumptions include a common resolvent-set boundary and vanishing spectral shift there. It is **not** a gap-free Hilbert–Schmidt identity and should not be cited as one. Rank mismatches can force the displayed determinant to vanish, as Proposition 2.6 explains. This is the closest exact rank-one prior art found for projector determinants.

### Küttler–Otte–Spitzer, Ann. Henri Poincaré 2014

[Anderson's Orthogonality Catastrophe for One-dimensional Systems, arXiv:1301.4923](https://arxiv.org/abs/1301.4923), [DOI](https://doi.org/10.1007/s00023-013-0287-z).

They derive the leading asymptotics of the Anderson integral `tr[P_N(I-Pi_N)]`, with a logarithmic system-size term and scattering-matrix coefficient, for one-dimensional continuum Schrödinger systems. For equal-rank projections, the squared Hilbert–Schmidt distance is twice that integral. This proves that local perturbations can generate extensive numbers of small principal angles near a sharp Fermi cutoff. It does not directly furnish a graph-edge theorem.

Related primary source: [Gebert–Küttler–Müller–Otte, The exponent in the orthogonality catastrophe for Fermi gases, J. Spectral Theory 6 (2016), 643–683](https://doi.org/10.4171/JST/135), especially Remarks 2.4(ii) and the projection expansion in Section 3. That paper distinguishes the first Anderson-integral term from the full determinant series, which is important when deriving lower bounds.

### Pushnitski, Bulletin London Math. Soc. 2008

[The scattering matrix and the differences of spectral projections, 40, 227–238](https://doi.org/10.1112/blms/bdn002), [arXiv:math/0702253](https://arxiv.org/abs/math/0702253), [author-hosted primary PDF](https://nms.kcl.ac.uk/alexander.pushnitski/papers/paper22.pdf).

Under the paper's Kato-smoothness hypotheses, Theorem 1.1 gives essential spectrum `[-a,a]` for the difference of the sharp spectral projections at energy `lambda`, with `a=||S(lambda)-I||/2`. Thus nontrivial scattering makes the difference noncompact and in particular not Hilbert–Schmidt, despite a compact perturbation of the original operators. A possible graph-specific falsification route is an infinite path with one changed bond, a direct verification of nontrivial scattering and smoothness, and strong convergence of finite-path spectral projections away from atoms. Fatou over a nontrivial energy interval would then imply unbounded finite-graph all-scale Hilbert–Schmidt drift. This is a proposed proof route, not a theorem proved by this audit.

## Exact classical identities relevant to the candidate

These are elementary calculations, supplied to keep the novelty boundary precise. Work on the positive support `H=1^perp` of a finite connected combinatorial graph Laplacian, with **unit vertex masses**. Write `A=L|H>0`, `B=A+u u*`, `u=sqrt(d)(e_p-e_q)`, `tau=u*A^-1u`, and

`s(t)=u*(A+tI)^-1u`, `S_A(t)=t(A+tI)^-1`, `D(t)=S_A(t)-S_B(t)`.

Sherman–Morrison gives

`D(t)= t (A+tI)^-1 u u* (A+tI)^-1 / (1+s(t)) >=0`,

`tr D(t) = -t s'(t)/(1+s(t))`.

Integrating the logarithmic derivative gives the exact identity

`integral_0^infty tr D(t) dt/t = log(1+tau)`.

Moreover, `t(A+tI)^-2 <= (A+tI)^-1`, so

`0 <= tr D(t) <= s(t)/(1+s(t)) <= tau/(1+tau)`.

Because `D(t)` has rank one,

`integral_0^infty ||D(t)||_F^2 dt/t <= [tau/(1+tau)] log(1+tau)`.

The same reasoning gives operator-norm bounds. The trace identity is an instance of the classical resolvent perturbation determinant/Krein spectral-shift calculus, and the bound uses only rank one and positivity. It should be called an exact baseline, not a new all-scale stability theorem. For a batch PSD edit, the integrated trace is `log det(A^-1/2 B A^-1/2)`; the rank-one Frobenius equality no longer holds in that form.

For hard projectors `P_t=1_(0,t](A)` and `Q_t=1_(0,t](B)`, the exact algebra is instead

`||P_t-Q_t||_F^2 = tr(P_t-Q_t) + 2 tr[Q_t(I-P_t)]`.

Eigenvalue interlacing makes the first term nonnegative and its logarithmic-scale integral equals `log(1+tau)`. The second term is noncommuting eigenspace leakage, which is not charged by the eigenvalue-shift budget. Equivalently, with eigenpairs `(lambda_i,v_i)` and `(mu_j,w_j)`,

`integral ||P_t-Q_t||_F^2 dt/t = sum_ij |<v_i,w_j>|^2 |log lambda_i-log mu_j|`.

These identities isolate the missing ingredient in the proposed big-if theorem. An attempted bound of this full quantity by `C log(1+tau)` must control the leakage term, and AOC suggests this cannot hold uniformly in dimension.

## What could still be a substantive positive target

- A theorem connecting a **certifiable cut margin** or a fixed-mass partition stability parameter to adversarial edit leverage, with an efficiently testable certificate and actual label recourse. Merely assuming that every near-optimal cut is close restates approximation stability and does not provide the missing certificate.
- A gap-free **abstaining or set-valued** clustering output that identifies which spectral bands or vertex labels remain certified, rather than demanding continuity of a sharp fixed-rank projector. The output and ambiguity budget must be precisely defined.
- An update method that beats existing dynamic data structures in a clearly specified model, or provides a guarantee absent from them: stable labels, adversarial recourse, certificate maintenance, unit-cardinality balance, or a useful dependence on the *observed* leverage rather than graph condition numbers.

None of those positive targets is proved by this audit. The safe conclusion is to test the hard-projector target directly, preserve a rigorous counterexample if it fails, and treat the soft-resolvent identities as classical alternatives.
