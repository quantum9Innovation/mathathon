# Priority comparison for a critical geometric spectral law

November 15, 2026, America/Los_Angeles.

Status: bounded primary-source comparison. This is not a historical-priority certificate. The current geometric probability and effective-operator attempts were not read before this report was frozen. Its target is the [frozen problem packet](../input/NEXT_PROBLEM-v1.md), not an accepted theorem from this round.

The model has a uniform simple fixed-degree regular host, predetermined marks with m/n^(1/3) tending to c>0, and critically weighted neighbourhood duplication. The desired result is an actual spectral law near the isolated host eigenvalue d, retaining rare close-pair interactions and the collective constant mode. A joint marked-distance law and an operator approximation are separate obligations.

## 1. Integer-distance oscillation is established

Van der Hofstad, Hooghiemstra and Van Mieghem's Theorem 1.1 tracks the fractional part of log_nu N in the typical distance between two vertices. Corollary 1.2 gives convergence along exponential subsequences. Theorem 1.4 identifies the family of limits, and equation (1.10) explicitly specializes it to constant degree d, with tail exp[-d/(d-2) times (d-1)^(a+k)]. Inspection depth: arXiv:math/0407092v1, model, these statements, regular specialization and the displayed error estimate (1.9). The full proof was not re-audited. [Distances in random graphs with finite variance degrees](https://arxiv.org/html/math/0407092).

Applicability boundary: this is a typical two-vertex distance near log_(d-1)n. The current minimum over a growing marked set lies near log_(d-1)(n/m^2), much smaller at criticality. A marginal typical-distance theorem does not establish the required joint rare-event counts. Even its logarithmic error estimate cannot simply be multiplied by order m^2 to obtain the needed precision. The lattice mechanism must be credited, while the new parameter regime requires a separate proof.

## 2. Poisson approximation is a classical method

Arratia, Goldstein and Gordon's 1989 Theorem 2 approximates a dependent indicator process by independent Poisson coordinates, with total-variation control through dependency-neighbourhood terms. Theorem 1 includes a direct bound for a zero-count event, hence for an extreme. Inspection depth: the authors' retained Annals of Probability PDF, pages 9 through 12, definitions of b_1, b_2, b_3 and Theorems 1 through 3. [Two Moments Suffice for Poisson Approximations](https://dornsife.usc.edu/larry-goldstein/wp-content/uploads/sites/221/2023/06/AGG-1.pdf).

This gives a plausible established route after conditioning on a host graph and independently thinning its vertices. It does not remove the need to verify close-pair intensity, overlap contributions, geometric exceptional events and the passage back to a fixed-size marked set. Any newly proved factorial-moment or thinning lemma here should be presented as an application or elementary specialization, not a new Poisson approximation framework.

## 3. Joint distances with continuous edge weights are different

Salez's 2013 paper studies the full array of distances in fixed-degree random regular networks with independent exponential edge lengths. Its limit is an explicit recentered infinite random array. Inspection depth: primary journal PDF, abstract and initial model and marginal-limit statements, not the complete proof. [Joint distribution of distances in large random regular networks](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B9607D4D2BE8A38A924B90C23D60C335/S0021900200119928a.pdf/joint_distribution_of_distances_in_large_random_regular_networks.pdf).

The continuous lengths eliminate the integer-distance setting in the current question. The result should not be cited as a direct theorem for unweighted nearest pairs among n^(1/3) marks.

## 4. Poisson spectral extremes and nonconvergent intensities also precede this work

Alt, Ducatez and Knowles prove a Poisson approximation for the spectral edge in sparse Erdos-Renyi graphs. Theorem 1.3 and Remark 1.5 explicitly allow an intensity without a full-sequence limit, and discuss resonant parameter regimes with nonconvergent normalized extremes. Their hypotheses have growing expected degree between a power of log log N and a constant multiple of log N. Inspection depth: authors' PDF dated August 24, 2021, introduction, Theorem 1.3, the intensity discussion and Remark 1.5. The complete rigidity and localization proofs were not re-audited. [Poisson statistics and localization at the spectral edge of sparse Erdos-Renyi graphs](https://www.unige.ch/~knowles/er_edge.pdf).

The extreme states there arise from high-degree vertices in an independent-edge ensemble. This is not the bounded-degree partial splitting model or its collision with an isolated constant mode. Nevertheless, neither spectral Poisson statistics nor lattice-related absence of a full-sequence law can be presented as a newly discovered general phenomenon.

Hiesmayr and McKenzie extend precise edge laws and localization to constant expected-degree Erdos-Renyi graphs, using local neighbourhood geometry around nearly maximal-degree vertices. Inspection depth: primary abstract and published abstract, retained from the preceding audit, not a reconstruction of the theorem. [The Spectral Edge of Constant Degree Erdos-Renyi Graphs](https://arxiv.org/abs/2309.11007), [published version](https://doi.org/10.1002/rsa.70011). Constant expected degree is not the same as bounded degrees: their extreme local degrees grow. That difference and the dependent construction prevent an immediate specialization to the present model.

## 5. Splitting graphs and the full-mark spectrum

The operation itself is established. For full splitting, the adjacency is [[A,A],[A,0]], and Yang and Rosenfeld's Corollary 3.2 expresses its spectrum through phi A and -phi^(-1)A. Inspection depth: publisher-hosted definition, corollary and block determinant calculation, already checked in the preceding round and revisited through the primary page. [Some spectral invariants of the neighborhood corona of graphs](https://doi.org/10.1016/j.dam.2018.03.052).

The current model retains only a sublinear deterministic mark set, whose relative distances are random through the host. No direct rare-pair limit theorem for that partial operation was established from the inspected source. The prior [close-pair audit](../../close-pair-transition-round-01/priority/PRIORITY-v1.md) remains applicable to scattering, deformation and local resonance methods.

## Search boundary and useful conclusion

Queries covered lattice fluctuations and subsequences in random regular distances, nearest pairs among marked vertices, Poisson distance counts, partial splitting spectra and Poisson spectral extremes. Comparisons above use primary sources. Secondary search descriptions were not treated as theorem evidence. A failed fetch of an arXiv HTML version of the spectral-edge paper was replaced by the authors' dated PDF.

The potentially distinguishing result is an explicit critical spectral law for this finite-host partial splitting ensemble, derived from a separately verified marked-distance point process and an operator estimate at scale sqrt(m/n). If the law is subsequential, it should identify the precise phase parameter and show that differing phases actually give differing spectral distributions. Integer distances alone do not prove nonconvergence of a spectral observable, because the spectral map could erase that dependence.

The proof must also distinguish a limiting sparse interaction matrix from entrywise convergence, control contributions of smaller interactions in operator norm, and justify how the collective mode couples to or separates from rare pair modes. A Poisson pair count by itself does not establish a Poisson eigenvalue process.

No inspected theorem directly supplies all of those model-specific steps. This is a bounded applicability finding, not proof that the target is a published open problem or historically first. Publication-level novelty would require a deeper citation-chain audit after the exact final statement is frozen.
