# Priority audit for growing collections of duplicated neighbourhoods

November 15, 2026, America/Los_Angeles.

Status: bounded primary-source comparison. This is not a historical-priority certificate or a proof review. The new probability and transfer attempts were not read during this audit, preserving a later separately reconstructed review.

## Exact target inspected

The input is [NEXT_PROBLEM.md](../../research-direction-2026-11-14/NEXT_PROBLEM.md). The host is a uniform simple labelled cubic graph with adjacency A. A deterministic set of m distinct labels is chosen before sampling. Its coordinate inclusion is E. Add m new vertices, each connected to the original neighbours of its corresponding label, without adding edges between new vertices. The augmented adjacency is

\[
\begin{pmatrix}A&AE\\E^\top A&0\end{pmatrix}.
\]

The target range is m<=n^(1/3-epsilon), for fixed epsilon>0. The claimed scale would be s=sqrt(m/n), with two displacements plus and minus 3s/sqrt(8), and m-1 further eigenvalues at 3+o_P(s). The key prerequisite is operator-norm control of the Perron-centered marked resolvent to o_P(s), with derivative convergence. The [SG-17 replacement proof](../../../../spectral-reconciliation-2026-11-14/remote-intake/CRITICAL_SCALE_AUDIT.md) supplies the m=1 precedent.

The altered graph is irregular. The resonance is near the isolated host eigenvalue 3, separated from the bulk edge 2sqrt(2). It is not a transition at the bulk edge or a normalized-Laplacian gap theorem.

## Main assessment

The inspected sources do not directly supply this exact graph theorem. This supports doing the proof comparison, not claiming that the target is open or first. The likely distinguishing content, if proved, is a quantitative subspace resolvent estimate for predetermined localized marks in a fixed-degree dependent graph ensemble, strong enough to resolve a shrinking collective resonance scale.

Growing-rank perturbation theory, compressed-resolvent master equations, inertia comparisons and local-state scattering are already established methods. They must be cited as such. In particular, a deterministic transfer theorem based on a subspace resolvent bound is not by itself a new general research framework.

## Closest direct comparisons

### 1. Benaych-Georges and Nadakuditi, fixed-rank deformation theory

Source: [The eigenvalues and eigenvectors of finite, low rank perturbations of large random matrices, arXiv:0910.2120v3](https://arxiv.org/html/0910.2120v3).

Inspected directly: Section 2.1, Theorem 2.1, and Proposition 5.1, including its kernel correspondence. The hypotheses fix rank r independently of n, require independent host and perturbation, and impose orthogonal or unitary invariance on one of them. Proposition 5.1 gives the exact compressed-resolvent singularity criterion.

Applicability boundary: the present host has only label-permutation symmetry. Its localized attachment AE depends on A, and its rank grows. Also, the host has an isolated Perron eigenvalue above the bulk. Merely substituting the Kesten-McKay transform into Theorem 2.1 does not establish the proposed result. The determinant identity is relevant classical machinery, not the missing probabilistic estimate.

### 2. Huang, growing-rank Hermitian perturbations

Source: [Mesoscopic Perturbations of Large Random Matrices, arXiv:1412.4193v2](https://arxiv.org/html/1412.4193v2), published in Random Matrices: Theory and Applications 7(2), 1850004, 2018.

Inspected directly: Section 2.1, Theorem 2.1 and its monotone master-matrix argument, Theorem 2.8, and Proposition 2.9. Rank M=o(N) is allowed. The hosts are Haar-conjugated matrices or Wigner matrices whose independent entries satisfy a logarithmic Sobolev inequality. For bounded perturbations and locations separated from the host spectrum, the displayed failure bound is C exp(-c_1 N eta^2+c_2 M). The Wigner location theorem assumes sqrt(M/N)<<eta.

Applicability boundary: this is the closest established growing-rank method, including monotonicity and operator compression. It does not verify such compression for constant-degree regular graphs or the correlated attachment AE. Its displayed accuracy does not resolve an o(sqrt(m/n)) resonance. The present project should credit the method and identify its graph-specific precision as the proposed additional input.

### 3. Shmalo, subspace local-law transfer

Source: [Mesoscopic Rectangular Spikes under Subspace Local Laws: Outlier Values and Singular Subspaces, arXiv:2608.19594v1](https://arxiv.org/html/2608.19594v1), August 20, 2026. This is a recent preprint, not an independently certified result in this audit.

Inspected directly: Sections 1.3 and 1.4, Assumptions 2.3 through 2.5, the example table, Theorem 3.2 and its proof setup. The paper assumes operator-norm compression of the linearized noise resolvent on growing signal subspaces, then derives outlier matching without mutual spike separation. Its contours stay a fixed distance from the limiting noise spectrum. Several model verifications allow rank o(n), while an overwhelming-probability anisotropic law alone yields a logarithmic-rank route. The paper explicitly credits Huang for the real-axis inertia and monotonicity argument.

Applicability boundary: this prevents presenting abstract subspace-law transfer as untouched territory. It does not provide the required cubic-graph compressed resolvent, nor the critical o(sqrt(m/n)) precision or the attachment-dependent Perron coupling in this target. A direct theorem specialization was not established.

### 4. Huang and Yau, regular-graph Green functions

Source: [Spectrum of Random d-regular Graphs Up to the Edge, arXiv:2102.00963v3](https://arxiv.org/html/2102.00963v3), corrected version dated February 2, 2025. Journal DOI: [10.1002/cpa.22176](https://doi.org/10.1002/cpa.22176).

Inspected directly: Theorems 1.2, 1.3 and 4.2, the error definition (4.2), and the surrounding tree-extension discussion. This treats fixed d>=3. Theorem 4.2 approximates individual Green-function entries by a local tree-extension Green function, not uniformly by a scalar identity. The source explicitly distinguishes these entries from the Wigner setting. Theorem 1.3 supplies a high-probability nontrivial spectral edge bound.

Applicability boundary: this is an important stronger toolkit and a host-gap source. This audit did not derive the marked operator estimate R1 from its entrywise estimates. Such a derivation must remove the Perron pole, aggregate m by m errors at the required scale, and handle short marked-to-marked paths. Cite it as relevant prior local-law machinery, not as an automatic proof or a verified obstruction to novelty.

### 5. Colin de Verdiere and Truc, local defects on trees

Source: [Scattering theory for graphs isomorphic to a homogeneous tree at infinity, arXiv:1209.1001v2](https://arxiv.org/html/1209.1001v2), May 17, 2013.

Inspected directly: introduction, Section 4 setup, Theorem 4.2, and the finite-support reduction in Section 5. The setting permits a finite core attached to homogeneous tree ends, with a finite-dimensional pure point component. Its Green-function and scattering reduction already connects local geometry to bound states.

Applicability boundary: an infinite tree has no normalized constant Perron vector. This source does not transfer a growing defect collection into a finite random regular host with accuracy at sqrt(m/n). The local-state mechanism is prior work. The quantitative finite-host collective law would require separate proof.

### 6. Alt, Ducatez and Knowles, sparse-graph localization

Sources: [Extremal eigenvalues of critical Erdos-Renyi graphs, arXiv:1905.03243](https://arxiv.org/abs/1905.03243), [Localized phase for the Erdos-Renyi graph, arXiv:2305.16294v2](https://arxiv.org/html/2305.16294v2), and the [authors' full paper](https://www.unige.ch/~knowles/er_localization.pdf).

Inspection depth: primary abstracts, introduction-level descriptions and model ranges, not reconstruction of the proofs. The first paper relates high-degree vertices to outliers when d is of order log N. The later paper establishes localization for sqrt(log N)<<d at most of logarithmic order, using comparisons of tunnelling amplitudes and eigenvalue spacing.

Applicability boundary: these are substantive precedents for interacting local spectral structures. They concern independent-edge graphs, random high-degree centres and a growing degree regime. They do not directly cover prescribed cubic neighbourhood duplicates. The project must not describe localization, resonant centres, or their interaction as concepts introduced here.

## Duplication and sparse-deformation screening

Targeted searches included vertex duplication, neighbourhood cloning, partial duplication, fixed-degree regular perturbations, growing rank, mesoscopic deformation and localized defect outliers. Two nearby graph-operation hits were inspected at abstract or theorem-excerpt level:

- [On the inverse eigenvalue problem for block graphs](https://doi.org/10.1016/j.laa.2021.09.008), Section 2, replaces a vertex by a clique with controlled matrix weights. That operation is not the present unweighted independent duplication model.
- [Compression of Dynamic Graphs Generated by a Duplication Model](https://doi.org/10.1007/s00453-020-00699-2) uses iterative full neighbourhood duplication, but the inspected abstract concerns encoding dynamic graphs. No quantitative random-cubic spectral comparison was established from it.

Screening also found [Han's bounded-rank non-Hermitian band-matrix work](https://arxiv.org/abs/2408.00567). Its abstract assumes independent entries and growing sparsity, with a bounded-rank deterministic deformation. It is not a direct theorem for this Hermitian fixed-degree ensemble. These limited inspections do not exclude relevant theorems elsewhere in the papers or citation chains.

## What a structural extension should state

A useful general theorem should expose its inputs rather than conceal them in an abstract determinant. The appropriate data are a separated host Perron eigenpair, a growing marked inclusion or attachment matrix, an operator-norm approximation for its projected resolvent, a derivative approximation, and a uniform second-derivative bound. The conclusion should identify the number and order of roots using Hermitian inertia and monotonicity, and then give the concrete graph application.

For this project, the test of substance is whether the random regular graph supplies the required approximation with error smaller than the collective coupling sqrt(m/n). A theorem valid for each deterministic marked set is different from one event valid simultaneously for all marked sets. No union over all sets is justified by label symmetry alone. Likewise, graph-dependent selection can force adjacent marks and alter the approximation.

The m<=n^(1/3-epsilon) range in the input is a sufficient proof target. Neither the checked literature nor this audit establishes that it is optimal. Increasing m can bring direct marked edges and stronger off-diagonal interactions into play. A threshold claim requires an actual obstruction or transition theorem.

## Audit conclusion and next action

The integrator subsequently specified a broader planned application without supplying its proof: for each fixed d>=3, use the weighted attachment B=sqrt(d-2) A E and an internal defect block C=s H_n, where s=sqrt(m/n), ||H_n|| is bounded and m^3 log^2(n)/n tends to zero. The proposed scaled near-d cluster is compared with

\[
\begin{pmatrix}0&\kappa_d e^\top\\\kappa_d e&H_n/D_d\end{pmatrix},
\qquad
D_d=\frac{2(d-1)^2}{(d-2)^2},\quad
\kappa_d=\frac{d(d-2)^{3/2}}{\sqrt2(d-1)},
\]

where e is the unit constant vector on the marks. This is a target description received during the audit, not a reviewed theorem. The calibration gives a critical weighted family. For d other than three, it is not an unweighted graph-duplication theorem.

The same source boundaries apply. The fixed-degree regular ensemble and localized attachment remain outside the inspected invariant, Wigner and rectangular model verifications. Arbitrary bounded H_n would add a useful interaction description, but general effective matrices and growing-rank root matching remain established ideas. Uniformity over bounded H_n must be justified by a common operator-error event. It must not be confused with simultaneous uniformity over graph-dependent marked sets. No direct subsumption or historical-firstness conclusion for this calibrated family was established here.

Preserve a bounded novelty statement: the candidate graph-specific critical law and its localized growing-mark resolvent estimate were not directly supplied by the inspected theorems. Historical firstness remains unverified. Credit existing finite-rank, growing-rank, local-law and scattering methods. Do not call the target a published open problem unless an exact prior question is located.

The next action is separate review of the frozen probability estimate and the exact root-transfer theorem, followed by comparison of their final hypotheses and rates with this note. This audit does not accept a mathematical claim or modify any canonical ledger.
