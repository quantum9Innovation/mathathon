# mathathon

Do a breakthrough. Make no mistakes.

The problem and target bounds are in [the research direction](matmul/research-direction.pdf).

The active research goal is broader: pursue a general quadratic-time advance
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

The [joint boundary law](matmul/fractional-boundary-crossover.txt) now
determines the exact compression coefficient when the endpoint ratio
approaches one as the tolerance decreases. It proves two transitions and
an exact one-rank region, with matching single-edge path examples.
The [coefficient plot](matmul/fractional-boundary-crossover.png) shows
the proved law; the [verification record](matmul/fractional-boundary-crossover-proof-checks.txt)
records the independent proof reviews and finite algebra checks.

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

A [second working paper](matmul/positive-rational-approximation.pdf)
([source](matmul/positive-rational-approximation.tex)) gives complete proofs
of the bounds in Faust--Fawzi (2023) Conjectures 1 and 2, using positive
rational sums with the conjectured exponents and fixed prefactors.
The [verification record](matmul/positive-rational-proof-checks.txt) covers
the actual source, all endpoint cases, arithmetic scope, and explicit SDP
representations. No later resolution was found in a bounded search;
priority and external verification remain open.

The quantum section derives small PSD-block representations and two-sided
optimization certificates. A reproducible
[interval certificate](matmul/quantum-product-certificate.py) proves that an
ideal 25-pole construction uses 50 lower or 51 upper blocks of order 2N,
with bracket width below 5e-7 times the Petz chi-squared divergence.
The [independent quantum audit](matmul/quantum-small-block-independent-audit.txt)
separates this guarantee from numerical coefficient preparation and SDP
solver runtime. The small-block principle has classical antecedents.

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
checks the hierarchy paper. The [Lean 4 development and coverage map](formal/VERIFICATION.txt)
prove its deterministic matrix reductions, carried lift, conditional spectral-error
theorem, and cost cancellations. The randomized certificate construction and full
runtime theorem remain unformalized. Build the checked library with `cd formal && lake build`.
