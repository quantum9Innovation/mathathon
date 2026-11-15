# Priority and theorem-scope audit

Frozen revision 1. November 15, 2026. Primary sources were inspected during the authorized structural-defects round. This is a bounded comparison, not an exhaustive priority determination.

## Scope and verdict

The target is [the proposed attachment theorem](../root/port-interaction-v1.md), SHA256 `5e41e11cccc76df15cb61f4fffa59a2f8e0a5b3d6ad92554298b294df2d10d17`, together with [the retuned crossing problem](../input/NEXT_PROBLEM-v1.md). Neither proposal is accepted by this audit as a proved theorem. Mathematical review and source-only formal validation are separate tasks.

General finite boundary elimination, rational decoration maps, reconstruction of eigenvectors, and matrix-valued nonbacktracking correspondences already have direct precedents. Growing-rank outlier analysis and sparse resonant localization also have substantial precedents. A contribution must therefore be stated at the combined graph-model and error scope actually proved.

| Proposed framing | Verdict from the inspected sources | Required correction or additional theorem |
| --- | --- | --- |
| A new general boundary-operator principle | Unsupported as a priority claim | Present the exact elimination as established machinery |
| A new matrix-valued adjacency to nonbacktracking correspondence | Unsupported as a priority claim | Compare directly with Bordenave and Collins, Propositions 9 and 10 |
| The first analysis of growing-rank outliers or many localized states | Unsupported as a priority claim | Restrict the comparison to fixed-degree geometric attachments and their precise dependence |
| A structural critical law for locally filtered finite motifs on fixed-degree random regular hosts | A substantive candidate scope | Verify uniform growing-mark errors, the actual top cluster, attachment-dependent metric, and a distinct unweighted example |
| A universal avoided crossing at the retuned negative level | Not established | Compute the signed coupling and all terms at the proposed scale, including normalization and stationary centering |

## Direct precedents

### Finite decoration and a cyclicity caveat

Schenker and Aizenman, *The Creation of Spectral Gaps by Graph Decoration*, Letters in Mathematical Physics 53 (2000), Proposition 3.1, treat a fixed finite rooted decoration at every host vertex. For the bounded self-adjoint decorated operator, cyclicity of the root vector gives exact spectral mapping through a scalar rational function with positive pole weights. Without cyclicity, the boundary resolvent and spectral-measure relation still hold, but invisible decoration modes prevent the same unconditional equality of full spectra. The decisive hypothesis is “a cyclic vector for A.” Sections 2 and 3, the proposition and its resolvent proof were inspected. This is a direct predecessor for local motif elimination, not a theorem about a sparse growing set of randomly interacting marks. [Published author-hosted paper](https://users.math.msu.edu/users/schenke6/Reprints/LMPV53P253.pdf)

### A finite graph coupled to an arbitrary graph

Golinskii, *Spectra of infinite graphs via Schur complement*, arXiv:1504.04452, Theorem 1.1, couples a finite graph to another graph by one bridge. At a spectral parameter in the second graph's resolvent set, the combined spectrum is characterized by a scalar equation involving the finite characteristic polynomial, its root-deleted polynomial, and the second graph's rooted Green function. The paper explicitly uses the “Schur complement.” Definition 0.1, the block factorization, Theorem 1.1 and its proof were inspected. Its bridge geometry is narrower than a general multiport attachment, but it is already an exact spectral theorem for actual attached graphs. [Primary preprint](https://arxiv.org/pdf/1504.04452)

### General isospectral reduction and reconstruction

Dusson, Sigal and Stamm, *The Feshbach-Schur map and perturbation theory*, arXiv:2105.02058v1 (2021), Theorem 1.2, gives isospectral reduction when the eliminated block is invertible and the map is defined. It identifies kernels, preserves their dimensions, and reconstructs the full eigenvector from the retained component. Corollary 1.3 converts eigenvalues into a parameter-dependent finite effective eigenvalue equation. The operative term is “isospectral.” Theorem 1.2, Corollary 1.3 and equations (1.10) through (1.16) were inspected. The general algebra and reconstruction are therefore established. Their application still requires graph-specific invertibility, uniform estimates, and control of the retained metric. [Primary article](https://arxiv.org/html/2105.02058)

### Ihara-Bass and the Bethe Hessian

Saade, Krzakala and Zdeborova, *Spectral Clustering of Graphs with the Bethe Hessian*, arXiv:1406.1880 (2014), Section I equation (2), defines the actual symmetric matrix

\[
H(t)=(t^2-1)I-tA+D,
\]

where D contains the actual vertex degrees. Section II.1 equation (5) relates nonbacktracking eigenvalues other than plus or minus one to zeros of its determinant through the “Ihara-Bass formula.” The weighted version appears in equation (3). Those sections were inspected. For an augmented graph, D must be the augmented degree matrix. A regular-host substitution that discards the finite attachment's degree changes is not this identity. The paper supplies established correspondence, not the present growing-motif resonance estimates. [Primary article](https://arxiv.org/html/1406.1880)

### Matrix-valued nonbacktracking correspondences

Bordenave and Collins, *Eigenvalues of random lifts and polynomials of random permutation matrices*, Annals of Mathematics 190 (2019), Theorem 2, proves Hausdorff spectral convergence on the complement of the constant fiber sector for fixed coefficient dimension and fixed generator count. Proposition 9 gives a matrix-valued spectral correspondence with an explicit parameter-dependent vertex operator, excluding specified matrix poles. Proposition 10 gives a resolvent-weighted nonbacktracking operator for which host invertibility is equivalent to exclusion of eigenvalue one. The phrase “if and only if” appears in both correspondences. Definitions, Theorem 2, and Propositions 9 and 10 were inspected. This directly rules out claiming the correspondence itself as new. The fixed-dimensional random-lift theorem does not directly supply a growing marked compression at a shrinking resonance scale. [Published paper](https://annals.math.princeton.edu/2019/190-3/p03), [inspected full text](https://arxiv.org/html/1801.00876)

### Finite dense motifs and nonbacktracking localization

Timar, Dorogovtsev and Mendes, *Localization of nonbacktracking centrality on dense subgraphs of sparse networks*, Physical Review E 107, 014301 (2023), arXiv:2209.02594v2, studies an arbitrary finite child graph in an infinite locally tree-like mother network. Branches leaving the child “do not intersect within any finite distance.” Under that idealized geometry, Section II equation (6) gives the composite leading nonbacktracking eigenvalue as the maximum of the child's value and the mother's branching value. Sections III and IV study normalized centrality and decay. Sections II, III.1, III.3 and III.4 were inspected. Section III.4 explicitly gives a rough finite-size validity criterion. This is an essential predecessor for motif-induced localization. Its nonnegative Perron centrality, infinite nonintersection geometry, and fixed child do not establish signed adjacency subspaces for a growing set of interacting motifs in a finite regular host. [Primary article](https://arxiv.org/html/2209.02594v2)

### Growing-rank outlier reductions

Huang, *Mesoscopic Perturbations of Large Random Matrices*, arXiv:1412.4193v2 (2015), allows perturbation rank M=o(N). Theorem 2.1 treats a Haar-rotated bounded host plus deterministic bounded perturbation with separated outliers. Theorem 2.8 treats the stated Wigner ensemble with a logarithmic Sobolev assumption and separated spikes, locating outliers near theta plus its reciprocal with explicit probability estimates at errors larger than sqrt(M/N). Proposition 2.9 controls a growing compressed resolvent. The author's abstract specifies “rank M is o(N).” Definitions and these theorem statements were inspected. Thus growing dimension and monotone effective outlier equations are established techniques. A fixed-degree regular host with coupling p(A)E is neither of these isotropic models, and its distance-dependent rare interactions cannot simply be replaced by their scalar compression estimates. [Primary article](https://arxiv.org/html/1412.4193v2)

### Sparse resonant tunnelling

Alt, Ducatez and Knowles, *Localized phase for the Erdos-Renyi graph*, arXiv:2305.16294v2, Theorem 1.1, proves single-center exponential localization in its specified high-energy region for the independent-edge model. The displayed hypothesis (1.5) is sqrt(log N) log log N much smaller than d, with d at most 3 log N. Section 1.1 compares tunnelling with eigenvalue separation through “Mott's criterion,” using globally accurate approximate vectors and an anticoncentration estimate. Section 1.2 and the overview were inspected. This supplies an important conceptual and technical precedent for deciding when interactions select individual states. It does not cover a fixed cubic regular host, predetermined attachments, or exact repeated lattice pair levels. The proposed theorem must retain degenerate subspaces until its own error and separation analysis permits a basis statement. [Primary article](https://arxiv.org/html/2305.16294v2)

### Poisson edge statistics and phase dependence

Alt, Ducatez and Knowles, *Poisson statistics and localization at the spectral edge of sparse Erdos-Renyi graphs*, arXiv:2106.12519v4 (2022), Theorem 1.3, approximates rescaled edge eigenvalues by a Poisson point process after removing the stray eigenvalue. Its range has d at least a power greater than four of log log N and below the critical logarithmic degree threshold. Theorem 1.7 provides localization for a specified growing set of extreme eigenvectors. The introduction explicitly notes that the intensity “does in general not have a limit.” The overview and theorem statements were inspected. Hence Poisson localized edge statistics and phase-sensitive subsequences already occur in sparse spectral theory. Our candidate instead concerns pair-distance counts among predetermined marks in a fixed-degree host. A compensated next-order law would require convergence and centering at its own scale, beyond a finite-window Poisson statement. [Primary article](https://arxiv.org/html/2106.12519)

## What the candidate would have to add

The following assessment concerns the proposed local files, not an asserted absence of other literature.

1. **A genuine class with a checkable interface.** State the fixed motif C, port b, polynomial p, local resonance calibration, positivity and nonzero stationary coupling. The root proposal does this. The signed cancellation model shows why p(d) nonzero is a substantive boundary, rather than a cosmetic hypothesis.
2. **Uniform control as the number of attachments grows.** Derive the marked operator remainder and its derivative from actual host estimates, with constants independent of m through the critical range. A collection of fixed-motif limits is insufficient.
3. **A common critical interaction law.** Establish the finite-window star-plus-matching approximation, distance-phase Poisson counts, and both tails needed for order statistics. Identify the attachment dependence through kappa and h, rather than repeating the whole random argument for each motif.
4. **Actual graph subspaces and masses.** Prove the top-cluster count when each motif contributes several coordinates, the reconstruction Gram matrix, and the normalized projection transfer. State mass in the constant host direction separately from mass on all host vertices.
5. **A distinct unweighted example.** The proposed cubic K1,7 attachment adds eight vertices per marked site and has a different internal resolvent and metric from duplication. Its claimed constants and full applicability require independent verification. This would demonstrate structural scope beyond a renamed duplication model.
6. **Sharper precision only when earned.** The retuned negative crossing lies below the accepted logarithmic splitting scale. A limit there requires the next graph normalization term, compensated collective drift, signed pair coupling, and any surviving integer phase. A formal two-level calculation alone cannot provide these graph estimates.

## Route decision and claim boundaries

Use the self-adjoint boundary reduction as the main route unless a direct oriented-edge argument proves a sharper remainder, a broader attachment class, or an additional invariant. An exact correspondence without such a gain does not answer the current precision problem. A nonnormal nonbacktracking spectral-radius bound is not by itself a self-adjoint operator-norm bound.

If the structural theorem survives review, a defensible description is a common critical interaction law for a class of sparse finite attachments to fixed-degree random regular hosts, with explicit motif-dependent spectral and mass coefficients. The present audit does not establish historical firstness, resolve any named published open question, or show that this framework unifies previously unrelated fields. Its plausible value is a reusable theorem joining local attachment data to collective and rare-pair behavior.

The highest-value remaining obligations are the uniform attachment reduction and physical lift, the signed retuned crossing at its actual graph precision, and an exact-scope comparison against any closer literature found before dissemination.

## Exposure and limitations

The reviewer authored finite formal supporting packets in the growing-defects, close-pair, critical-law and critical-subspaces rounds. The reviewer also read and reviewed the preceding negative logarithmic probability proof and integration documents. Those are prior exposures, not independent validation of this new attachment theorem. The current root proposal was read after the initial literature pass.

This audit checks stated theorem scope and selected proof mechanisms. It does not independently reprove each cited article. Source text was read directly from author-hosted publications or primary preprints. PDF screenshot requests were unavailable for some sources, so the relevant text and displayed formulas were inspected through the primary text extraction. Search results alone were not used for the load-bearing comparisons. The search is bounded and may miss closer results, especially in decoration, graph surgery, and growing-rank sparse perturbations.
