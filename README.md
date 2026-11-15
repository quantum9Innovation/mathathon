# mathathon

Do a breakthrough. Make no mistakes.

The revised [slides](spectral-gap-slides.pdf) ([TeX](spectral-gap-slides.tex))
use the standard Madrid mathematical Beamer theme, define matchings with
diagrams, and explain recovery through a six-vertex worked example. The
[report](spectral-gap-report.pdf) ([TeX](spectral-gap-report.tex)) first covers
prior work and the Proposition 28 proof, then presents recovery as its main
new contribution in the abstract, introduction, and Section 4. Its complete
proofs are in main Sections 5–8; quantitative refinements follow later. The
[build instructions](present/README.txt) explain how to compile both documents.

The completed [60-page manuscript](spectral-gap/regular-community-recovery/regular-community-recovery.pdf)
studies exact hidden-group recovery in sparse block-regular graphs without
a spectral-gap assumption. The separate
[six-page plain-language explanation](spectral-gap/regular-community-recovery/plain-language/results-explained.pdf)
introduces the results, algorithm, significance, and limits without assuming
background in the field. The [packet index](spectral-gap/regular-community-recovery/INDEX.txt)
links the sources and verification record. Breakthrough research is stopped;
historical firstness and external peer review are not certified.

The current spectral-graph investigation studies **how one edge edit changes
a fractional Laplacian in relative energy**. Start with the
[two-page reading guide](spectral-gap/single-edge-response/reading-guide.pdf)
and the [research manuscript](spectral-gap/single-edge-response/single-edge-response.pdf):
exact worst-case spectral budgets, realization by simple unweighted
bipartite graphs, and sharp fixed-degree rank laws. For doubling one unit
edge in a simple unweighted host of maximum degree d>=3, the worst rank
has leading coefficient alpha*log(2d/(d+2))/epsilon; extremal hosts look
locally like the d-regular tree. A gap-free expected-nearly-linear factor
construction attains that leading rank constant. The latter is
an exact-arithmetic algorithm theorem with fully charged solves and
two-sided relative error; it is not an implemented performance result.
The [session evidence](spectral-gap/RESEARCH_SESSION_2026-11-15.txt) links
the proof reviews, diagnostics, source reads and priority limits.
Historical novelty and the requested breakthrough scale remain unverified.
The spectral-partitioning investigation is now documented in the recovery
manuscript above. Earlier exploratory research records are retained.

The problem and target bounds are in [the research direction](matmul/research-direction.pdf).

The earlier matrix-multiplication research pursues a general quadratic-time advance
and practical theoretical algorithms with manageable constants and standard
operations. The results below establish narrower theorems and algorithms;
the requested general breakthrough remains open.

The [balanced graph multiplication paper](matmul/balanced-graph-multiplication.pdf)
([source](matmul/balanced-graph-multiplication.tex)) now proves spectral
concentration for the permutation sketch. It gives ordinary **O(N^2)**
total arithmetic for fixed stable ranks, accuracy, and confidence, including
every output entry, with error epsilon*||A||*||B||. Its high-confidence
variant has width ~O(r/epsilon^2) using unsigned balanced bucket sums and
deterministic mean correction. The [verification record](matmul/balanced-graph-multiplication-proof-checks.txt)
covers the actual-source independent audit and reproducible checks.
Classical methods already achieve comparable or stronger row/error bounds.

The [bounded-spectrum refinement](matmul/bounded-spectrum-fractional-counts.txt)
proves exact leading fractional compression coefficients r/(4*pi^2*alpha)
for endpoint/update norm ratio R>1, and (r-1)/(4*pi^2*alpha) at R=1.
Its [independent review](matmul/bounded-spectrum-fractional-independent-audit.txt)
also checks the finite rank discontinuity and connected-path transfer.
The [constructive bounded-spectrum graph algorithm](matmul/bounded-spectrum-graph-algorithm.txt)
now attains that sharper leading width at expected nearly linear cost.
It explicitly charges growing polynomial subtraction, moving-strip
quadrature, scalar construction and all shifted graph solves. Its
[verification record](matmul/bounded-spectrum-graph-algorithm-proof-checks.txt)
contains the complete proof review and reproducible algebra checks.
The [bounded-graph priority audit](matmul/bounded-graph-priority-audit.txt)
credits the existing optimal scalar pole-plus-polynomial rates and
rational matrix-update mechanisms.

The [joint boundary law](matmul/fractional-boundary-crossover.txt) now
determines the exact compression coefficient when the endpoint ratio
approaches one as the tolerance decreases. It proves two transitions and
an exact one-rank region, with matching single-edge path examples.
The [coefficient plot](matmul/fractional-boundary-crossover.png) shows
the proved law; the [verification record](matmul/fractional-boundary-crossover-proof-checks.txt)
records the independent proof reviews and finite algebra checks.
The [boundary-law priority audit](matmul/fractional-boundary-crossover-priority-audit.txt)
identifies the tail estimate and terminal cutoff as classical corollaries;
priority of the full joint law remains unverified.

The [constructive boundary algorithm](matmul/constructive-boundary-crossover-graph-algorithm.txt)
attains that leading width at expected nearly linear thin-factor cost,
and returns a rank-one correction strictly beyond the terminal transition.
Its [verification record](matmul/constructive-boundary-crossover-proof-checks.txt)
includes independent source and factor-algebra reviews.
The [rank-r corollaries](matmul/fractional-boundary-rank-r.txt) show how
the transition depends on the update spectrum, with matching connected
weighted-path examples and a separate [proof review](matmul/fractional-boundary-rank-r-proof-checks.txt).

The [graph connection manuscript](matmul/graph-fractional-updates.pdf)
([source](matmul/graph-fractional-updates.tex)) constructs corrections to
fractional graph Laplacians after k edge changes in expected
~O((m+n)k) arithmetic, at intrinsic operator error epsilon*||Delta L||^alpha,
without a spectral-gap assumption. It also transfers the exact worst-case
matrix compression constant to single-edge updates on paths with positive
vertex masses. The [verification record](matmul/graph-fractional-proof-checks.txt)
separates proof review, numerical diagnostics, and priority limits.
The [sharp graph algorithm](matmul/sharp-graph-fractional-updates.txt) attains
the optimal leading width k/[4*pi^2*alpha*(1-alpha)] times log^2(1/epsilon)
for positive edge updates with arbitrary fixed vertex masses, at the same
expected nearly linear construction cost. Its [independent audit](matmul/sharp-graph-fractional-independent-audit.txt)
checks the algorithm and matching path lower bound.
The [spectral-gap corollary](matmul/expander-polynomial-updates.txt) gives
width O(k log(1/epsilon)) and ordinary sparse construction on expanders,
including a uniform random-regular-host guarantee for bounded additions.
The imported [spectral-gap project](spectral-gap/README.md) is now available.
The [cross-project assessment](matmul/matrix-graph-bridge-state.txt) records
the concentration proof and the remaining stronger multiplication target.
The [Gaussian cone-span obstruction](matmul/gaussian-cone-span-obstruction.txt)
shows that fresh random starts alone do not justify a proposed robust
far-cone filtering route; its [verification record](matmul/gaussian-cone-span-proof-checks.txt)
states the restricted model and independent proof checks.
An [unbiased balanced permutation sketch](matmul/balanced-permutation-amm.txt)
now has exact covariance formulas and a complete reduction of its trace
moments to that project's mixed-cell bounds. The new concentration proof
uses the exact covariance and classical permutation Bernstein inequalities;
sharper use of the higher mixed moments remains open.

A [working paper on exact fractional matrix constants](matmul/sharp-fractional-holder.pdf)
([source](matmul/sharp-fractional-holder.tex)) derives the exact leading
small-exponent constants for positive powers, absolute powers, and polar
matrix maps. The full-line power coefficient is exactly four times the
positive-matrix coefficient. It also derives sharp worst-case compression
rank constants. The actual manuscript passed an independent mathematical
audit; see the [verification record](matmul/sharp-holder-proof-checks.txt).
Classical scalar rates and compression methods are credited. Novelty of
the precise matrix limits remains under review.

The [companion classification paper](matmul/fractional-channel-classification.pdf)
([source](matmul/fractional-channel-classification.tex)) proves the complete
uniform law for every complex homogeneous fractional function, including
approach to two exceptional analytic families, the 1:2:4 comparison, and
the joint transition with matrix dimension. The actual source passed an independent review;
see its [verification record](matmul/channel-classification-proof-checks.txt)
and [priority audit](matmul/channel-classification-priority-audit.txt).
Classical Cauchy spectral laws and two-channel representations are credited.

The [localization paper](matmul/local-singularity-universality.pdf)
([source](matmul/local-singularity-universality.tex)) extends the sharp law
to several singularities: one positive rank-one perturbation attains
their combined leading constant. An infinite family with a polynomial
amplitude-counting law has exact compression growth log^(2+nu)(1/epsilon).
The [verification record](matmul/local-singularity-proof-checks.txt) includes
the independent actual-source review. The update norm may shrink;
no charged runtime theorem follows from this compression result.

The [joint endpoint paper](matmul/uniform-alpha-fractional-holder.pdf)
([source](matmul/uniform-alpha-fractional-holder.tex)) proves
H(1-beta,s)~beta^(2s-1)/(2*pi^2*s^2) for every joint beta,s->0,
including superexponential beta. It refines Ricard's established endpoint
kernel and threshold1/2 with quantitative rates and uniform nonlinear
bounds. The full source passed
independent review; see its [verification record](matmul/uniform-alpha-proof-checks.txt).
Both papers credit classical methods and leave external priority open.

A [second working paper](matmul/positive-rational-approximation.pdf)
([source](matmul/positive-rational-approximation.tex)) gives complete proofs
of the bounds in Faust--Fawzi (2023) Conjectures 1 and 2, using positive
rational sums with the conjectured exponents and fixed prefactors.
The [verification record](matmul/positive-rational-proof-checks.txt) covers
the actual source, all endpoint cases, arithmetic scope, and explicit SDP
representations. No later resolution was found in a bounded search;
priority and external verification remain open.

The quantum section derives small PSD-block representations and two-sided
optimization certificates. An [interval certificate](matmul/quantum-product-certificate.py)
first proves an ideal 25-pole construction. The new
[rational-coefficient program](matmul/quantum-rational-coefficients.py)
now supplies [exact positive rational data](matmul/quantum-entropy-rational-rule.json)
for 50 lower or 51 upper blocks of order 2N, with bracket width below
5e-7 times the Petz chi-squared divergence. Lower weights use the stated
rescaling u_i/(1+e). The [verification record](matmul/quantum-rational-coefficient-proof-checks.txt)
includes independent proof/code/data review and agreement of two arithmetic
implementations. It certifies the scalar coefficients and lifted brackets;
SDP solver runtime and solver rounding remain separate questions.
The small-block principle has classical antecedents.

The [entropy preparation theorem](matmul/entropy-polynomial-bit-preparation.txt)
extends coefficient preparation to arbitrary dyadic accuracy eta=2^-b
in deterministic polynomial bit complexity, retaining
m<=log^2(1/eta)/(2*pi^2)+O(log(1/eta)) positive rational terms.
All scalar and root computations are charged. Its
[verification record](matmul/entropy-polynomial-bit-proof-checks.txt)
includes the independent exact-copy PASS. This is a family algorithm
proof; the separate25-pole program is the implemented finite instance.

The [square-root-update construction](matmul/nongalactic-wildcard-search.txt)
gives conventional arithmetic cost ~O(Nmr+m^3) for a factor of a correction
to sqrt(XX^T), at additive error epsilon*||U|| and rank
O(r log^2(r/epsilon)). Its [state-of-the-art comparison](matmul/sqrt-update-sota-audit.txt)
finds a possible gain over explicit Gram construction, with substantial
risk that existing methods already imply the complete bound. No global
state-of-the-art or novelty claim is made.
The [signed/downdate extension](matmul/sqrt-update-extensions.txt) achieves
intrinsic error epsilon*sqrt(||B-A||), including singular endpoints and
cancelling signed factors; its full arithmetic theorem passed an
[independent audit](matmul/sqrt-update-independent-audit.txt).

The complete [sharp-rank algorithm paper](matmul/sharp-matrix-function-updates.pdf)
([source](matmul/sharp-matrix-function-updates.tex)) now realizes the optimal
leading compression ranks at the same conventional cost, including signed
Hermitian and rectangular fractional-map corrections. The square-root case
uses arithmetic and scalar square roots. The actual manuscript passed an
independent audit; see the [verification record](matmul/sharp-update-proof-checks.txt)
for precise input, error, scalar-model and full-output guarantees.

The [bounded-spectrum and relative-root refinement](matmul/bounded-relative-root-updates.pdf)
([source](matmul/bounded-relative-root-updates.tex)) constructively attains
the sharper bounded-spectrum leading width r/(4*pi^2*alpha), and gives
relative correction error even with singular PSD endpoints. Its relative
width is O(r L[L+log(rho)]), with explicit scale dependence and fully
charged raw shifted solves. A diagonal-Gram promise removes cubic setup
deterministically; general raw factors retain it. The
[verification record](matmul/bounded-relative-root-proof-checks.txt)
covers the independent actual-source review and exact arithmetic scope.
The relative rank order also follows by regularization from the published
SPD bound; the [priority correction](matmul/relative-root-regularization-priority.txt)
derives this directly. The [new constants audit](matmul/new-constants-priority-audit.txt)
separates the sharper quantitative claims from classical mechanisms.

A new [working paper on cluster-robust Krylov bounds](matmul/cluster-robust-krylov.pdf)
([source](matmul/cluster-robust-krylov.tex)) proves condition-number-free
convergence bounds for standard block Krylov using a positive sliding
relative b-th spectral gap, up to extra logarithmic factors. It uses ordinary
matrix operations. Three independent informal mathematical reviews and a
bounded primary-source comparison are recorded in the
[verification record](matmul/cluster-robust-krylov-proof-checks.txt).
The generic accuracy dependence remains theta^(-1/2); the general N^2
matrix-product target is still open.

The earlier [hierarchical spectral-approximation paper](matmul/hierarchical-absolute-spectral.pdf)
([LaTeX source](matmul/hierarchical-absolute-spectral.tex)) proves total time
**N^(2+o(1))**, including every output entry, for arbitrary fixed factorizations
with n=p=N, m=N^(α+o(1)), target rank r≤√m, and θ=(m/N)^(5/2), where
α=(3√5−5)/2≈0.854102. It returns width at most r and spectral error at most
(1+θ)σ_(r+1)(AB), with probability at least 1−δ.
The checked exact-Gram and ordinary fast batched Krylov bounds at these
parameters are **N^(2.0364745084…+o(1))**. Rank may grow through
N^(0.427051…+o(1)); accuracy is θ=N^(−0.364745…+o(1)).

The hierarchy uses a growing number of matrix-free refinements with every
depth-dependent cost counted. A carried-preimage identity implements the
physical output without inverting an implicit preconditioner. An absolute-error
variant chooses its rank, with a joint high-probability error, width, and runtime
bound. The [hierarchy verification record](matmul/hierarchy-proof-checks.txt) links
the independent proof and prior-art reviews. These comparisons are upper bounds;
the result does not establish a lower bound for all possible algorithms.

The new [block spectral-approximation paper](matmul/absolute-pencil-spectral.pdf)
([LaTeX source](matmul/absolute-pencil-spectral.tex)) proves a block method using
coarse Gram sketches and regularized absolute-value preconditioning. When its
raw Krylov width is at most m, total cost is
~O(I+G_h+m^ω+√(h/θ)[T_MM(n,m,r+1)+T_MM(p,m,r+1)]+np+T_MM(n,r,p)).
Here G_h is the cost of two Grams after sketching to ~m/h² rows.
The guarantee is spectral error at most (1+θ)σ_(r+1)(AB), with probability
at least 1−δ, for arbitrary fixed factors and output width at most r.

For N=m^(59/50), θ=m^(−21/50), and every r≤⌈√N⌉, construction costs
**N^(2−2/3363+o(1))**, and total explicit output costs **N^(2+o(1))**.
For r≤m^(59/109), the checked ordinary Krylov bound with fast factor actions is
N^(239/118+o(1)) ≈ N^(2.025424+o(1)); exact Gram is N^(2.027004+o(1)).
The weighted quadratic-defect transfer and physical lift are proved in full.
Exact coefficient sign counts handle threshold decisions without eigenvalue
extraction or coefficient powering. An absolute-error variant chooses its
rank by doubling and returns width at most twice the slack rank, with its
rank-dependent runtime on the same high-probability event. Three workers
reviewed the integrated manuscript; see the
[block verification record](matmul/block-proof-checks.txt).

The [stochastic spectral-approximation paper](matmul/stochastic-product-spectral.pdf)
([LaTeX source](matmul/stochastic-product-spectral.tex)) proves total time
~O(Ir+m^ω+r I^(3/4)m^(1/2)/√θ+T_MM(n,r,p)), with a sharper dependence on
the product's rank. It constructs an unbiased signed-pencil sampler from raw
input rows and applies established SVRG, acceleration, and PCA theorems.
Correlation-PCA deflation removes the earlier √r loss.

For fixed r, m=⌈N^(50/59)⌉, and θ=m^(-56/125), it gives **O(N²) total
arithmetic operations**, including every output entry. Construction improves
to N^(2−1/1180+o(1)); the checked general-product Gram bound is N^(2.027004…).
A growing-rank example gives output N^(2+o(1)), versus fast batched Krylov
N^(701/350+o(1)). An adaptive rule certifies absolute error without a supplied rank.

The [earlier threshold paper](matmul/sketch-preconditioned-spectral.pdf)
([source](matmul/sketch-preconditioned-spectral.tex)) retains the independently
proved sketch hierarchy and shared-core route. These are exact-real arithmetic results; global novelty
and finite-precision stability remain unconfirmed. The original θ=1/m target is open.

[Continuation state](matmul/research-state.txt) and the
[approach ledger](matmul/approach-ledger.txt) record the current evidence and remaining work.
Supporting material includes [ridge-filter proofs](matmul/ridge-filters.pdf),
[stochastic reduction and frontier audit](matmul/frontier-reduction-audit.txt),
[correlation-PCA and block audit](matmul/block-threshold-audit.txt),
[independent block proof review](matmul/block-absolute-independent-audit.txt),
[absolute-pencil prior-art audit](matmul/absolute-pencil-literature-audit.txt),
[positive-feature and rank-support audit](matmul/positive-feature-audit.txt),
[verification record](matmul/stochastic-proof-checks.txt),
[multilevel derivation](matmul/multilevel-proxy-audit.txt),
[shared-core and precision audit](matmul/shared-threshold-audit.txt),
[independent proof and novelty audit](matmul/novelty-completion-audit.txt),
[product-method comparisons](matmul/product-literature-audit.txt),
[oversampled Krylov comparisons](matmul/oversampled-krylov-audit.txt), and
[the reported AI research runs](matmul/research-run-evidence.txt).

A further [mathematical review and practical assessment](matmul/hierarchical-mathematical-review.txt)
checks the hierarchy paper. Its [Lean 4 verification](formal/VERIFICATION.txt) now
proves the original-input main results, all corollaries and the exact-Gram appendix,
including randomized success probabilities, full arithmetic costs and output entries.
The [theorem map](formal/THEOREM_MAP.txt) identifies the exact statements; all 702
local/supporting modules and 22 endpoint axiom audits pass. Reproduce the full check
with `cd formal && python3 verify.py --jobs 2 --all-local`.
The [practical examples](matmul/hierarchical-formal-significance.txt) explain the
literal constants and the scope of the exact-real arithmetic model.

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
