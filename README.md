# mathathon

- **[Short report](report-short.pdf)** ([LaTeX](report-short.tex)): spectral-graph background and a brief explanation of the recovery algorithm.
- **[Long report](report-long.pdf)** ([LaTeX](report-long.tex)): the complete 76-page proof record, organized around exact constraints, cancellation, and certified recovery.
- **[Slides](slides.pdf)** ([LaTeX](slides.tex)): the supplied presentation with four final recovery slides.
- **[Lean project](formal/)**: [verification guide](formal/VERIFICATION.txt), [theorem map](formal/THEOREM_MAP.txt), and [proof status](formal/PROOF_STATUS.txt).

This index lists results established in the repository's manuscripts. Written proofs, finite computational checks, and Lean proofs have different scopes. Historical firstness and external peer review are not certified. The general quadratic-time matrix-multiplication target remains open.

## Results across the project

### Random permutations and spectral graph theory

- **Proposition 28 and exact mixed-product extrema.** Compatible conditioning and a positive row-sum recurrence prove the matching-product estimate for independent permutation colors and arbitrary powers. The fixed-support envelopes are attained for zero, one, and two conflicting centered singletons; scalar consequences sharpen the singleton factor and identify its optimal universal prefactor. [Long report, Part I](report-long.pdf); [original manuscript and evidence](spectral-gap/manuscript-round-01/README.md).
- **Diagonal-moment thresholds and sharp errors.** Necessary and sufficient cubic growth, even/odd critical laws, sublinear correction hierarchy, a formula through every order, and optimal square-root/global error profiles. [Long report, Part II](report-long.pdf); [extension index](spectral-gap/extension-round-02/README.md).
- **Growing graph attachments.** The collective top displacement holds exactly when m³/n tends to zero. Close pairs force necessity; for n^(1/3)≪m≪√n the top shift has random scale m²/n. [Sharp transition proofs](spectral-gap/close-pair-transition-round-01/README.md).
- **Critical lattice spectrum.** At m comparable to n^(1/3), independent Poisson pair counts generate linked positive/negative levels alongside deterministic collective levels. Integer-distance phases produce distinct subsequential laws. [Critical-law manuscript](spectral-gap/critical-law-round-01/README.md).
- **Graph subspaces and resonance.** Physical projections, eigenvector masses, localization at pair endpoints, positive bright/dark mixing, and the finer negative logarithmic scale. [Subspace and resonance proofs](spectral-gap/critical-subspaces-round-01/README.md).
- **Structural attachments and retuned collision.** A common sharp threshold for fixed motifs with one simple resonant channel, including distinct unweighted motifs; the cubic retuned negative law at scale m/n has a smooth collective fluctuation and vanishing leading signed mixing. [Structural manuscript](spectral-gap/structural-defects-round-01/README.md).

### Exact hidden-group recovery

- **Unknown frame and hidden classes.** Under the symmetric omission certificate, recover the unknown bounded degree frame, sizes, and finest bounded-class equitable partition in the specified independent simple-factor model. No planted eigengap or real-corank-one promise is required. [Long report, Part III](report-long.pdf); [complete recovery manuscript](spectral-gap/regular-community-recovery/regular-community-recovery.pdf).
- **Certified complete listing.** Full finite-field kernels and right-kernel projection give always-correct listing in unconditional expected nearly quadratic bit work, nearly linear working space, and linear expected output. Raw exponential-nullity moments charge rare inputs. [Algorithm proofs](report-long.pdf); [plain-language companion](spectral-gap/regular-community-recovery/plain-language/results-explained.pdf).
- **Lifts, identifiability, and information limits.** Every fixed connected simple regular template of degree at least three is covered; the separate recovery manuscript proves old/new spectral disjointness, all-parameter two-class ambiguity/Bayes constants, complete-base ambiguity, a cycle-lift obstruction, and exponential ambiguity for a nonregular K_(3,12) template. The cubic two-class ambiguity and optimal error are asymptotic to 4/N² and 2/N². [Full manuscript](spectral-gap/regular-community-recovery/regular-community-recovery.pdf); [result and proof index](spectral-gap/regular-community-recovery/INDEX.txt).

### Fractional Laplacians and graph updates

- **Sharp relative response to one edge.** Exact spectral budgets, unweighted bipartite realization, logarithmic-squared path/cycle ranks, and inverse-tolerance rank at degree at least three. The fixed-degree leading coefficient is α log(2d/(d+2)); extremal rooted limits are regular trees. A gap-free expected nearly linear factor algorithm attains it with two-sided relative error. [Research manuscript](spectral-gap/single-edge-response/single-edge-response.pdf); [guide](spectral-gap/single-edge-response/reading-guide.pdf).
- **Sparse fractional graph corrections.** Construct corrections after k edge changes in expected soft-O((m+n)k) arithmetic at intrinsic operator error, with no gap assumption; matching positive-path compression bounds. [Graph-update paper](matmul/graph-fractional-updates.pdf).
- **Optimal leading width and expander refinement.** Positive updates attain width k log²(1/ε)/(4π²α(1−α)); expander hypotheses reduce width to O(k log(1/ε)). [Sharp algorithm](matmul/sharp-graph-fractional-updates.txt); [expander theorem](matmul/expander-polynomial-updates.txt).
- **Bounded spectra and boundary transitions.** Exact leading coefficients r/(4π²α) for endpoint ratio R>1 and (r−1)/(4π²α) at R=1, with constructive algorithms; a joint crossover has two transitions and a terminal rank-one region, including rank-r extensions. [Bounded-spectrum proof](matmul/bounded-spectrum-fractional-counts.txt); [algorithm](matmul/bounded-spectrum-graph-algorithm.txt); [crossover manuscript](matmul/fractional-boundary-crossover.pdf); [constructive crossover](matmul/constructive-boundary-crossover-graph-algorithm.txt); [rank-r law](matmul/fractional-boundary-rank-r.txt).

### Matrix approximation and multiplication algorithms

- **Balanced permutation product sketches.** Unbiased covariance and spectral concentration; ordinary O(N²) explicit-output arithmetic at fixed stable ranks/accuracy/confidence, with unsigned balanced buckets and deterministic mean correction. [Paper](matmul/balanced-graph-multiplication.pdf); [covariance and moment reduction](matmul/balanced-permutation-amm.txt). Classical methods already give comparable or stronger bounds.
- **Hierarchical spectral approximation.** Rank-r output with error at most (1+θ)σ_(r+1)(AB), growing-depth total N^(2+o(1)) work in the stated rectangular regime, optimized comparison, two-level specialization, and adaptive absolute error. [Main paper](matmul/hierarchical-absolute-spectral.pdf); [explanation](matmul/understanding-hierarchical-spectral.pdf); [Lean theorem map](formal/THEOREM_MAP.txt).
- **Block absolute-pencil method.** Coarse Gram sketches, weighted quadratic-defect transfer, physical output lift, exact threshold decisions, and adaptive absolute error. A stated rectangular family has subquadratic factor construction and N^(2+o(1)) explicit output. [Paper](matmul/absolute-pencil-spectral.pdf).
- **Stochastic product method.** An unbiased signed-pencil sampler with correlation-PCA deflation gives the stated rank-sensitive cost; fixed-rank rectangular examples have O(N²) total arithmetic. [Paper](matmul/stochastic-product-spectral.pdf).
- **Sketch and shared-core constructions.** Independently proved sketch hierarchy and shared-core threshold routes in the exact-real model. [Paper](matmul/sketch-preconditioned-spectral.pdf); [ridge-filter proofs](matmul/ridge-filters.pdf).
- **Cluster-robust Krylov bounds.** Condition-number-free guarantees from sliding relative block gaps; the generic accuracy dependence remains θ^(−1/2). [Paper](matmul/cluster-robust-krylov.pdf).
- **A filtering obstruction.** Fresh Gaussian starts alone cannot justify the proposed robust far-cone filtering argument in its specified model. [Proof](matmul/gaussian-cone-span-obstruction.txt).

### Matrix functions and sharp approximation constants

- **Exact fractional constants.** Small-exponent Schatten-power constants and matching compression ranks for positive powers, absolute powers, polar maps, and analytic branches. [Basic paper](matmul/sharp-fractional-holder.pdf).
- **Uniform channel classification.** Every complex homogeneous fractional function, exceptional analytic families, the 1:2:4 law, vanishing-branch transition, and joint dimension law. [Classification paper](matmul/fractional-channel-classification.pdf).
- **Several singularities and infinite families.** One positive rank-one update attains combined leading constants; polynomial amplitude-counting yields log^(2+ν)(1/ε) compression growth. [Localization paper](matmul/local-singularity-universality.pdf).
- **Uniform endpoint limits.** Joint α→1 and Schatten exponent→0, including superexponential endpoint approach, with quantitative rates. [Endpoint paper](matmul/uniform-alpha-fractional-holder.pdf).
- **Constructive sharp-rank updates.** Signed Hermitian and rectangular fractional-map corrections attain optimal leading ranks at conventional arithmetic cost, including singular endpoints. [Algorithm paper](matmul/sharp-matrix-function-updates.pdf); [square-root construction](matmul/nongalactic-wildcard-search.txt); [signed extension](matmul/sqrt-update-extensions.txt).
- **Bounded and relative square-root corrections.** Sharper bounded-spectrum width, relative error at singular PSD endpoints, fully charged shifted solves, and the diagonal-Gram refinement. [Paper](matmul/bounded-relative-root-updates.pdf). [Priority correction](matmul/relative-root-regularization-priority.txt) identifies the classical regularization implication.

### Rational approximation and quantum entropy

- **Faust–Fawzi conjectured upper bounds.** Positive rational constructions achieve the exponents and fixed prefactors in Conjectures 1 and 2, including the stated endpoint cases. [Paper](matmul/positive-rational-approximation.pdf); [proof checks](matmul/positive-rational-proof-checks.txt).
- **Small-block entropy certificates.** Positive rational coefficients give 50 lower or 51 upper PSD blocks of order 2N, with bracket width below 5×10^(−7) times Petz chi-squared divergence. [Paper](matmul/positive-rational-approximation.pdf); [exact data](matmul/quantum-entropy-rational-rule.json); [certificate program](matmul/quantum-rational-coefficients.py).
- **Polynomial-bit coefficient preparation.** At dyadic accuracy η=2^(−b), deterministic polynomial-bit preparation retains m≤log²(1/η)/(2π²)+O(log(1/η)) positive rational terms and charges scalar/root computations. [Theorem](matmul/entropy-polynomial-bit-preparation.txt); [verification](matmul/entropy-polynomial-bit-proof-checks.txt).

## Formalization coverage

The main [Lean project](formal/) proves the hierarchical matrix-product approximation results, rather than the graph recovery theorem. The recorded integrated run completed **702 local/supporting modules and 22 endpoint axiom audits**; its source/dependency rehash passed. The proof-status files and theorem map describe that recorded run. Documentation changes here do not constitute a new full compiler run.

The verified endpoints include fixed and growing depth, optimized and two-level corollaries, adaptive absolute error, the exact-Gram appendix, and a polynomial degree lower bound. They construct the factors and explicit product, establish spectral-error probability, and charge input reads, scalar preparation, Gaussian draws, arithmetic, factor outputs, and dense output. The actual implementation choices and finite all-outcome fallback caps are documented in [VERIFICATION.txt](formal/VERIFICATION.txt).

The model is exact-real arithmetic. These proofs do not establish floating-point stability, bit complexity, practical speedups, or a lower bound against every competing method. Main results take verified feasible multiplication circuits, not an unproved runtime oracle. The allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`; admissions and additional axioms are rejected.

Separate graph packets formalize finite supporting components: [growing defects](spectral-gap/growing-defects-round-01/formalization/), [close-pair witnesses](spectral-gap/close-pair-transition-round-01/formalization/), [critical finite operators](spectral-gap/critical-law-round-01/formalization/README.md), [critical subspaces](spectral-gap/critical-subspaces-round-01/formalization/), and [structural attachments](spectral-gap/structural-defects-round-01/formalization/README.md). The critical-law packet records 30 declarations; the latest structural packet records 57 new and 16 reused declarations. Revision totals overlap and must not be added. These packets do not formalize the complete random-graph probability laws, limiting processes, or analytic bridges. Recovery and the Proposition 28 report have written proofs and finite checks, with no end-to-end Lean claim.

## Hierarchical spectral theorem statements and Lean verification

The formalization in [formal/](formal/) corresponds to
[hierarchical-absolute-spectral.pdf](matmul/hierarchical-absolute-spectral.pdf).
Start with the following declarations; each linked file contains the theorem
statement and its Lean proof. All names are in the `HierarchicalAbsoluteSpectral`
namespace.

| Manuscript result | Lean declaration | Source |
| --- | --- | --- |
| Fixed-depth tradeoff | `fixed_depth_from_feasible_kernel_polylog` | [MainFeasibleKernel.lean](formal/HierarchicalAbsoluteSpectral/MainFeasibleKernel.lean) |
| Growing-depth family, including total runtime | `growingDepthProgram_family_theorem` | [MainFamilyProgramFinal.lean](formal/HierarchicalAbsoluteSpectral/MainFamilyProgramFinal.lean) |
| Optimized comparison corollary | `optimized_paper_corollary` | [CorollaryOptimizedFinal.lean](formal/HierarchicalAbsoluteSpectral/CorollaryOptimizedFinal.lean) |
| Absolute error without a supplied rank | `absoluteFamilyProgram_paper_corollary` | [CorollaryAbsoluteFamilyFinal.lean](formal/HierarchicalAbsoluteSpectral/CorollaryAbsoluteFamilyFinal.lean) |
| Two-level specialization | `two_level_specialization` | [CorollaryTwoLevel.lean](formal/HierarchicalAbsoluteSpectral/CorollaryTwoLevel.lean) |
| Exact-Gram appendix algorithm | `exists_fast_exactGramAppendixComparator` | [ExactGramCharpolyAppendixCost.lean](formal/HierarchicalAbsoluteSpectral/ExactGramCharpolyAppendixCost.lean) |
| Polynomial degree lower bound | `polynomial_inverse_congruence_natDegree_lower` | [PolynomialDegreeLower.lean](formal/HierarchicalAbsoluteSpectral/PolynomialDegreeLower.lean) |

Read [FixedProblem](formal/HierarchicalAbsoluteSpectral/MainProblem.lean) and
[FamilyProblem](formal/HierarchicalAbsoluteSpectral/MainFamilyProgramParameters.lean)
to inspect the original matrix, dimension, rank, accuracy and confidence assumptions.
The fixed-depth theorem also takes verified matrix-multiplication circuits and their
feasible cost bound. Its conclusion includes the actual factors, `C = U * V`, rank,
success probability and total work. Lean's `tailSingularValue (A * B) r` uses zero-based
indexing and is the manuscript's `sigma_(r+1)(AB)`; the matrix norm is the spectral norm.
The [complete theorem map](formal/THEOREM_MAP.txt) also identifies the supporting
lemmas, the absolute-error uniform cap and the appendix's simplified cost bound.

With Elan, Python 3 and a working C toolchain installed, run from the repository root:

```bash
cd formal
elan toolchain install leanprover/lean4:v4.31.0
lake exe cache get
python3 verify.py --jobs 2 --all-local
```

[lean-toolchain](formal/lean-toolchain) pins Lean **4.31.0**; the
[Lake configuration](formal/lakefile.toml) and [manifest](formal/lake-manifest.json)
pin mathlib and its dependencies. The verifier checks local and supporting proof
modules in dependency order, checks the final source/dependency hashes, and audits
the transitive axioms of the public results. At the current revision, a successful
run reports **22 endpoint axiom audits** and finishes with
`Verified all 702 proof modules`.

To display the exact theorem types, original-input structures and axiom lists for
inspection after building, run:

```bash
lake env lean MainClosedAudit.lean
```

This [audit file](formal/MainClosedAudit.lean) uses `#check`, `#print` and
`#print axioms`; the full verifier already runs it. The allowed foundational axioms
are `propext`, `Classical.choice` and `Quot.sound`. Proof admissions and additional
axioms are rejected. See the [verification guide](formal/VERIFICATION.txt) for the
exact scope and verified implementation choices.

## Building the presentation documents

Run `bash present/build-reports.sh` from the repository root. The imported source copies are in [present/imported](present/imported/); supplied vector figure sources are in [figures](figures/). The long report preserves every original mathematical block; its reordering check is in [present/restructure-checks.json](present/restructure-checks.json).
