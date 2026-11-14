# mathathon

Do a breakthrough. Make no mistakes.

The problem and target bounds are in [the research direction](docs/research-direction.pdf).

The active research goal is broader: pursue a general quadratic-time advance
and practical theoretical algorithms with manageable constants and standard
operations. These remain open. The results below establish narrower arithmetic
bounds; they do not yet establish the requested general breakthrough.

The latest [hierarchical spectral-approximation paper](docs/hierarchical-absolute-spectral.pdf)
([LaTeX source](docs/hierarchical-absolute-spectral.tex)) proves total time
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
bound. The [hierarchy verification record](docs/hierarchy-proof-checks.txt) links
the independent proof and prior-art reviews. These comparisons are upper bounds;
the result does not establish a lower bound for all possible algorithms.

The new [block spectral-approximation paper](docs/absolute-pencil-spectral.pdf)
([LaTeX source](docs/absolute-pencil-spectral.tex)) proves a block method using
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
[block verification record](docs/block-proof-checks.txt).

The [stochastic spectral-approximation paper](docs/stochastic-product-spectral.pdf)
([LaTeX source](docs/stochastic-product-spectral.tex)) proves total time
~O(Ir+m^ω+r I^(3/4)m^(1/2)/√θ+T_MM(n,r,p)), with a sharper dependence on
the product's rank. It constructs an unbiased signed-pencil sampler from raw
input rows and applies established SVRG, acceleration, and PCA theorems.
Correlation-PCA deflation removes the earlier √r loss.

For fixed r, m=⌈N^(50/59)⌉, and θ=m^(-56/125), it gives **O(N²) total
arithmetic operations**, including every output entry. Construction improves
to N^(2−1/1180+o(1)); the checked general-product Gram bound is N^(2.027004…).
A growing-rank example gives output N^(2+o(1)), versus fast batched Krylov
N^(701/350+o(1)). An adaptive rule certifies absolute error without a supplied rank.

The [earlier threshold paper](docs/sketch-preconditioned-spectral.pdf)
([source](docs/sketch-preconditioned-spectral.tex)) retains the independently
proved sketch hierarchy and shared-core route. These are exact-real arithmetic results; global novelty
and finite-precision stability remain unconfirmed. The original θ=1/m target is open.

[Continuation state](docs/research-state.txt) and the
[approach ledger](docs/approach-ledger.txt) record the current evidence and remaining work.
Supporting material includes [ridge-filter proofs](docs/ridge-filters.pdf),
[stochastic reduction and frontier audit](docs/frontier-reduction-audit.txt),
[correlation-PCA and block audit](docs/block-threshold-audit.txt),
[independent block proof review](docs/block-absolute-independent-audit.txt),
[absolute-pencil prior-art audit](docs/absolute-pencil-literature-audit.txt),
[positive-feature and rank-support audit](docs/positive-feature-audit.txt),
[verification record](docs/stochastic-proof-checks.txt),
[multilevel derivation](docs/multilevel-proxy-audit.txt),
[shared-core and precision audit](docs/shared-threshold-audit.txt),
[independent proof and novelty audit](docs/novelty-completion-audit.txt),
[product-method comparisons](docs/product-literature-audit.txt),
[oversampled Krylov comparisons](docs/oversampled-krylov-audit.txt), and
[the reported AI research runs](docs/research-run-evidence.txt).

A further [mathematical review and practical assessment](docs/hierarchical-mathematical-review.txt)
checks the hierarchy paper. The [Lean 4 development and coverage map](formal/VERIFICATION.txt)
prove its deterministic matrix reductions, carried lift, conditional spectral-error
theorem, and cost cancellations. The randomized certificate construction and full
runtime theorem remain unformalized. Build the checked library with `cd formal && lake build`.
