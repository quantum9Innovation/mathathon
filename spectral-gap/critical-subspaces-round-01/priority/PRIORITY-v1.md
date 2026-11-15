# Bounded priority comparison for critical subspaces and resonance

Date inspected: November 15, 2026, America/Los_Angeles. Revision 1.

This is a bounded primary-source applicability audit. It does not establish historical firstness or that an exact published open problem has been resolved. The finite target is frozen in `../resonance/finite-normal-form-v1.md`, SHA256 `59bebac4b6a96d148d48830bf27130223d6820e53e16627720fb7f2f7216eed7`. The new graph probability and subspace proofs were not read before this note was frozen.

## 1. Separated spectral subspaces are classical

Chandler Davis and W. M. Kahan, The Rotation of Eigenvectors by a Perturbation. III, SIAM Journal on Numerical Analysis 7(1), 1970, DOI [10.1137/0707001](https://epubs.siam.org/doi/10.1137/0707001).

Inspection depth: the primary publisher record and abstract were read. The full paper was access restricted and its individual theorem hypotheses were not inspected here. The abstract explicitly treats invariant subspaces and approximate eigenvector clusters, with angle bounds obtained from a spectral gap and either perturbation or residual bounds.

Applicability: converting an already established graph-specific operator approximation into stability of a separated level subspace is standard perturbation theory. Multiplicity inside that level does not justify selecting individual basis vectors. This source receives historical attribution, not an unchecked citation for a particular constant or norm variant.

## 2. Degenerate effective matrices and direct rotation are classical

Sergey Bravyi, David DiVincenzo and Daniel Loss, Schrieffer-Wolff transformation for quantum many-body systems, Annals of Physics 326, 2011. Primary [preprint PDF](https://arxiv.org/pdf/1105.0675) and [publisher record](https://doi.org/10.1016/j.aop.2011.06.004).

Inspection depth: introduction, Section 3.1, Lemma 3.1 and Definition 3.1 were read. The PDF identifies arXiv:1105.0675v1, 3 May 2011. Its rendered title page carries a later date, which is not treated as a new theorem revision.

For a finite Hermitian matrix and a spectrally separated interval, Section 3.1 defines an exact direct rotation and effective Hamiltonian. Lemma 3.1 bounds the projector difference by twice the perturbation norm divided by the gap, under its gap-preserving assumption. The chosen interval need not be the lowest spectral interval.

Applicability: the positive two-by-two matrix and the elimination of a separated complementary sector belong to ordinary degenerate perturbation theory. The coefficient kappa sqrt(p), the graph lift and the achievable error relative to m^(-1/2) must come from this graph model. Neither a new perturbation principle nor a new general avoided-crossing mechanism is claimed.

## 3. Sparse-graph resonant subspaces and localization already exist

Johannes Alt, Raphael Ducatez and Antti Knowles, Delocalization transition for critical Erdos-Renyi graphs. Primary [author PDF dated August 31, 2021](https://www.unige.ch/~knowles/er_eigenvectors.pdf), published [Communications in Mathematical Physics](https://doi.org/10.1007/s00220-021-04167-y).

Inspection depth: abstract, model discussion, resonant-set definition, the discussion of Theorem 1.2 and the displayed Theorem 3.4 were read. The result concerns independent-edge graphs with expected degree above the square root of log N and at most a constant times log N. Its semilocalized eigenvectors are approximated by profiles supported near resonant vertices. Theorem 3.4 controls the total projection onto these profiles, rather than selecting a single profile merely because approximate eigenvalues are close.

Applicability obstruction: this is a growing expected-degree ensemble with high-degree resonances, not predetermined duplications in a fixed-degree regular host. It is nevertheless a close conceptual precedent for level-subspace statements and mass near a union of resonant centres. Such statements and the use of radial profiles are not new in general.

## 4. Tunnelling must be compared with level spacing

Alt, Ducatez and Knowles, Localized phase for the Erdos-Renyi graph, [arXiv:2305.16294v2, December 19, 2023](https://arxiv.org/html/2305.16294v2).

Inspection depth: abstract, the Mott-criterion discussion and formulas in Section 1.1, main theorem statements and the proof summary were read. The expected-degree range is again above the square root of log N and at most order log N. The paper proves localization by comparing tunnelling amplitudes with spacings of approximate eigenvalues, using global approximate eigenvectors and an anticoncentration input. It explains why insufficiently accurate local approximate vectors do not establish the desired localization conclusion.

Applicability obstruction: its independent-edge distribution, high-degree centres and spacing mechanism differ from the fixed cubic model with repeated lattice levels. The methodological lesson applies directly. A perturbation estimate that is small on the first spectral scale can still dominate the splitting within a degenerate level. The negative-side precision obstruction in the finite proof is consistent with this established distinction. No new localization principle is claimed.

## 5. Collective resonance has older physical precedents

Michael Tavis and Frederick W. Cummings, Exact Solution for an N-Molecule Radiation-Field Hamiltonian, Physical Review 170, 1968, [DOI 10.1103/PhysRev.170.379](https://journals.aps.org/pr/abstract/10.1103/PhysRev.170.379).

Inspection depth: primary publisher metadata and abstract only. The full article was access restricted. The abstract treats identical two-level molecules coupled to a single radiation mode at resonance and reports exact solutions with eigenvalue and eigenvector approximations.

This is historical context for collective resonance, not evidence that the present finite matrix or its graph-specific coefficient appears in that paper. No exact theorem comparison or claim of a new connection to quantum optics is based on the abstract alone. A second single-excitation article was returned by search, but its full page was blocked and is not used as evidence.

## 6. What could distinguish the present result

The useful candidate is a quantitative transfer for a particular graph model: predetermined critical duplications in a uniform simple cubic host, an explicit isometric lift of the marked effective coordinates, complete level-subspace control under repeated Poisson multiplicities, and a resonance expansion at the original adjacency scale n^(-1/2). The finite calculation additionally distinguishes symmetric positive pair modes from antisymmetric negative modes and proves that integer m,n sequences can realize every finite detuning.

These algebraic observations are proved in the finite note. Their application to the random graph requires a separate error estimate at the smaller scale. The old first-order eigenvalue law alone does not provide it. At zero detuning, an error o(m^(-1/2)) still need not select individual negative modes or reveal an order m^(-1) finite correction. A claim about localization near a union must be kept separate from a claim about each eigenvector choosing one pair.

The bounded searches included combinations of random regular graphs, neighbourhood duplication, partial splitting, resonant eigenvectors and collective modes. They did not return a directly applicable theorem. That observation is not evidence that none exists. The earlier critical-law priority audit remains relevant for splitting graphs and lattice Poisson limits. No full citation-chain audit of graph defects, molecular bright states or graph-specific resonant tunnelling has been completed.

The defensible attribution is therefore classical perturbation and resonance methods applied to an explicit graph-specific critical geometry, with historical priority unresolved. The finite two-by-two formula, a declaration count or a search miss should not be presented as a major new principle.
