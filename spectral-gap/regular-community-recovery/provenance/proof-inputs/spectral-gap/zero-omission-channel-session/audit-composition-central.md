# Full main-theorem and recovery-composition audit: central/lattice reviewer

Reviewer: `/root/central_lattice`, November 15, 2026. I read the entire actual new recovery composition and the frozen dependency sources listed below. The entire accompanying main theorem was previously read at the same unchanged hash for `audit-tex-central.md`; its model and raw-moment interface were checked again here. This review addresses the full main-plus-recovery conclusion, rather than only the central moment calculation.

**Verdict: PASS.** The main theorem and the stated certified symmetric-kernel primitive imply the composition's unconditional expected nearly quadratic bit work, expected nearly linear working storage, complete integer one-hot listing on every bounded-degree input, and high-probability recovery of the finest planted bounded-class frame, including forced zero omission weights. No substantive correction is required at these hashes. The primitive remains an identified existing algorithmic theorem; this audit checks its actual interface and the reduction, not a new proof of its cited external preconditioning theorems.

## Exact audited sources

```
ec3e96da5add3fb07699ce491927dc166361df6f7fba08448a441a005023b5d5  spectral-gap/zero-omission-channel-session/fast-recovery-composition.tex
cd522c3421cd7ebe63ddaa2c103627b5b13a9d51fda03be1555415df8864630c  spectral-gap/zero-omission-channel-session/channel-moments.tex
1fa625ce8206ace0c6d3bed4fd683ee488b37d614c8bf379d10603a14afbecda  spectral-gap/zero-omission-channel-session/audit-tex-central.md
bb6ec1086a2d46f4a1d0b66c69aadc2d120b07157ba8e95f3c08ffb187843473  spectral-gap/partitioning-dynamic-session/rsbm-full-kernel/certified-full-kernel.tex
cb893b0def524ba101a4419adf922f0dec60ad3156348c8e91d600887e743df9  spectral-gap/partitioning-dynamic-session/rsbm-full-kernel/intertwiner-extension.txt
127b233ee065d4ab158f251f57a33ea771ac101a3fc2e1637fc7e09273bd8c09  spectral-gap/regular-frame-fast-algorithm-root-audit.txt
2db029a9d3058122f939ccec2d190172c439d70ab0d4f72579f19bfbc49adc8d  spectral-gap/partitioning-frontier-session/nonregular-fibers/strict-q-recovery/zero-omission-addendum.tex
0042ca4067451330f955c9621bc741694369f4743ee4823c70f16f6a87d4c634  spectral-gap/partitioning-frontier-session/nonregular-fibers/strict-q-recovery/strict-q-blind-frame-recovery.tex
b0c449292c23e63e09cdb958ba24430cd594acf1533f9882c12999f6197bd017  spectral-gap/partitioning-frontier-session/nonregular-fibers/strict-q-recovery/support-audit/mixed-degree-small-support.tex
```

All of the algorithm and structural sources above were read in full for this composition audit. The earlier polynomial-moment conclusion is not promoted to a bounded moment; that stronger input comes from the new channel theorem at the separately fully audited unchanged hash.

## Main theorem and the exact statistical interface

The main theorem proves raw bounded moments for the actual independent configuration factors and transfers them directly to the independent uniform-simple factors by a bounded simplicity-conditioning cost. It permits mixed total degrees, zero certificate weights, arbitrary fixed prime, arbitrary target dimension, and arbitrary on-site target matrix, including singular or nonsemisimple targets. Its channel induction, exact normalization, maximal lattices, finite phase family, selected proper-phase certificate, global induction, and simple-model transfer were checked in the full main-source audit named above.

For a candidate `R`, the number of solutions of `AY=YR` over `F_3` is exactly `3^(h_R)`, with `h_R` the right nullity of the column-vectorized operator. Thus the main theorem supplies the required *single raw moment* for every candidate `R` on the actual simple-graph distribution. The certificate hypothesis concerns the true generating frame, not `R`. A candidate need not admit any certificate, be feasible over the integers, be reversible, be symmetric, or have connected support. The moment theorem allows all such target maps. The fixed field `p=3` is odd and therefore matches the actual primitive's hypothesis.

## One-hot gap with zero weights

I rederived the quantitative gap from the displayed equations and compared it against the frozen zero-omission addendum.

Repeated-target symmetrization preserves the legal integer equation and all pooled pair laws while increasing the exponent. Root marginals, and hence the distance `delta`, stay fixed. Lossless omission for one-hot integer stars holds because the missing unit vector is determined by the root row and the retained unit vectors. The weighted entropy identity therefore applies even when some omission weights vanish.

The divergence `kappa_it` is that of the actual root/retained law from the product of its marginals. Its chain-rule decomposition is conditional total correlation plus the sum of retained root-neighbor mutual informations. The weighted sum counts each directed slot with coefficient `1-q`, and factor reversibility gives the displayed internal-half-compatible expression for `A_q`. Every coefficient satisfies the bound giving `A_q <= (2/c)L`; no inverse of a zero or small omission weight is used.

Under the independent retained reference, the occupied root row of `R` still has total mass exactly `d_i`: this follows from integer legality and the unchanged root marginal. Both nonnegative vectors whose difference defines `f_it` have mass `d_i`, proving the range bound `2D^2`, including at boundary laws. The actual expectation is `V_it`, while the independent expectation is `S_i-V_it+B_i`. Pinsker with this range gives the displayed `sqrt(2)D^2 sqrt(kappa_it)` bound.

Weighted averaging uses precisely `sum_t q_it=1` and `q_it <= (1-c)/2`, so its lower bound is `c S_i`, regardless of signs of individual expectation differences. Weighted Cauchy--Schwarz has total weight one. Reversibility gives `sum_i alpha_i S_i=sum_j alpha_j d_j(1-||rho_j||^2)`, bounded below by `3 delta`. Squaring yields exactly `gamma=9c^3/(4D^4)`. The gap is valid with unused labels, vanishing candidate-class masses, internal factors, and forced zero weights.

The original exact factorial count applies to one-hot stars with no duplicate root factor, and has a fixed polynomial number of profiles and fixed polynomial remainder. The macroscopic expectation estimate therefore follows, and a finite candidate union preserves its exponential decay. A bound on binary or scalar counts is not substituted here.

## Small supports, clean neighborhoods, and structural recovery

Connected off-diagonal support and balance imply the stated uniform lower bound on old-class proportions. Following at most `K-1` present edges changes a class-size ratio by at most `D^(K-1)`; normalizing then gives `alpha_min >= 1/(K D^(K-1))`. This also covers the one-type case.

The ordinary support certificate contains all physical edges incident to a support. At an outside vertex with no unique support incidence, its selected degree is at least two. The excess is therefore at least `(d_min-2)s/2`; prescribing edges costs `O(1/n)` per pair, and the support/outside/factorial/pairing count leaves `C^s(s/n)^((d_min-2)s/2)`. No omission weight is involved. The simple model excludes bad singletons, so summation from `s=2` yields `O(n^(-(d_min-2)))`. This is distinct from the selected certificate needed for heterogeneous quotient phases in the main theorem; the composition does not import quotient injectivity into the ordinary support argument.

On the resulting graph event, every nonzero small row-support solution `AV=VR` is impossible simultaneously over all fields, widths and targets. The unique outside support incidence has coefficient one and gives a nonzero row of `AV` while the row of `VR` is zero.

Macroscopic exclusion puts every accepted integer indicator within `eta n` changed rows of some old-type point map `JT`, with no onto requirement on `T`. Changed vertices and their neighbors use at most `(D+1)eta n` vertices. The chosen threshold leaves a clean vertex in every old class. Its integer equation proves `QT=TR` exactly. Subtraction then gives the ordinary small-support equation for `Y-JT` over `Q`, forcing `Y=JT`. This also covers tiny candidate classes and non-surjective preliminary point maps. No real spectral gap is used.

The true `(J,Q)` is always in the complete list. Every accepted nonempty-class coarsening has an onto map from the old types, hence at most `k` classes. A maximum has `k` classes and its onto map is a permutation. Thus the stated algorithm recovers `J,k,Q` up to names on the structural event. It completes all enumerations before certifying a maximum.

## Complete right kernels and certificates

The actual primitive applies to every sparse symmetric input over the fixed odd field and has a per-input Las Vegas work bound; it is not a high-probability corank-one routine. The extension-field construction, verified trials, canonical base-field descent, deterministic rank certificate, and all-input retry charges are present in the actual source. Its theorem has precisely the work and workspace used by the composition.

Column vectorization gives `K_R=I_r tensor A-R^T tensor I_n`. The transpose on `R` is correct. Both `K_R` and its transpose have linear sparse product cost at fixed `K,D`, without a dense Kronecker construction. The block matrix `S_R=[0 K_R; K_R^T 0]` is symmetric, has rank twice the rank of `K_R`, and has nullity `2h_R` over the base field and its extensions.

The primitive computes a *basis* of the doubled kernel. Its bottom projections span exactly the complete right kernel: every `(0,v)` with `K_R v=0` lies in the doubled kernel. Selecting independent projected columns is essential and is stated. Pivot normalization gives the complete base-field right basis at cost `O(mh^2+h^3)`, within the per-input work bound. An arbitrary extension-field basis is not enumerated with base-field coefficients.

The compact right-kernel certificate is sound. The checker regenerates the shifted sequence and its true finite recurrence length; it does not trust a claimed polynomial degree. The unconditional shifted-image argument gives `ell <= rank S_R=2 rank K_R`. The verified independent right columns give `rank K_R <= m-h`. Requiring `ell=2(m-h)` forces equality and completeness. This uses integer dimension arithmetic, covers full and zero rank, and needs no dense elimination fallback. Verification costs nearly quadratic work. No division by a class size occurs, so `p` dividing a class size is irrelevant.

## Enumeration, expectations, storage, and exceptional inputs

Only the right kernel is enumerated. Incremental base-`p` generation makes the total digit changes `O_p(p^h)` and costs `O_p(n p^h)`, avoiding both a doubled exponent and an additional `h p^h` expectation. Each enumerated row is checked to be exactly one residue `1` with all other entries `0`, then lifted uniquely to an integer one-hot row. Nonempty class tests and the original integer identity reject modular artifacts. Every true integer candidate reduces to a vector of the computed right kernel, so listing is complete on every input graph in the stated bounded-degree class.

Nonempty classes ensure that any actual integer quotient has nonnegative rows with sum at most `D`, so the finite candidate family contains every possible accepted intertwiner. Nonsymmetric and otherwise infeasible candidates are retained rather than incorrectly filtered by conditions on the true frame. Per-vector integer checks and class counters cost nearly linear bit work at fixed parameters.

For each fixed input and target, all primitive retries, projection, descent, rank verification, vector generation and integer checks fit the displayed conditional expected bound

`soft-O(n^2(h_R+1)+n p^(h_R))`.

Since `h_R+1 <= p^(h_R)` and the actual simple-model raw moment is bounded, averaging this all-input bound gives unconditional expected nearly quadratic work. No structural success event is conditioned on for the runtime calculation; rare high-corank or ambiguous graphs are charged by the same moment. The expected workspace is nearly linear from `soft-O(n(h_R+1))`, with the primitive retry counter having finite expected size. Candidates can be streamed or only the current best retained. The expected number of accepted assignments is bounded by the finite sum of the raw moments, so their expected output size is `O(n)` bits.

Finally, there are finitely many candidate targets and finitely many connected integer generating frames at fixed `K,D`. The latter fix their positive proportions. Choosing one valid certificate per qualifying true frame makes the finite minimum of their positive `c` values positive. Moment bounds, support bounds, simplicity thresholds and failure estimates then admit uniform finite extrema. The algorithm needs none of these certificates. Sequential candidate processing and linearity of expectation require no independence among candidate kernels.

This is a mathematical source audit. It supplies no historical firstness claim, growing-field estimate, or practical benchmark, and it does not replace the identified certified-kernel theorem by an unproved new primitive.
