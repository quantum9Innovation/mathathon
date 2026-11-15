# Independent audit of the bounded-moment assembly

Prepared 2026-11-15. Scope: the logical assembly in `bounded-moment-theorem.md`, with particular attention to zero-phase coverage, compactness, neighborhood definitions and the dimension induction. I also checked the matching-count normalizers, covariance comparison and conditional-rank mechanism in the two companion estimates. This is a mathematical audit of the written argument, not a historical novelty assessment.

**Verdict: PASS for the assembly as written.** No missing zero phase or unclosed induction class was found. The resulting constant is for fixed base, field and target dimension; it is independent of lift size, not uniform in the field.

## 1. The exact region decomposition

Use the full legal-star law tuple `P=(P_i)` as the global type parameter. Its feasible set `K` is a compact polytope: finite probability simplices cut out by the real linear edge-table reversal constraints. The entropy exponent `Phi` is continuous on it, including at zero entries.

For a fixed problem, all entropy-zero points are a finite family. In a connected nonbipartite base each is determined by an invariant `H` and quotient cosets `a_i+H`; in the enlarged bipartite class it is determined by `H_L,H_R` and the corresponding quotient cosets. Each phase's complete star law is unique. Thus the zero set is finite, rather than a positive-dimensional family parametrized by hidden neighbor correlations.

Choose the sufficiently small fixed edge-table radius `delta` allowed by `central-lift-uniform.md`. Define the **open** full-uniform neighborhood

`U={P: max_(edges ij)||nu_ij-uniform edge law||<delta}`.

It contains the full uniform star phase. The central proposition controls **every star allocation whose pair tables lie in this neighborhood**, not merely star types that are themselves close to uniform. This distinction is essential and is satisfied by its exact iid-star/table formulation.

For each proper coset phase `F`, choose the `epsilon_F>0` from the sparse proposition and set

`V_F={P: sum_i mu_i(outside the phase coset at i)<epsilon_F}`.

This is an open set containing that phase. For an actual empirical type,

`sum_i mu_i(outside coset)=D_a(Y)/N`,

because every old fiber has size `N`. Hence its assignments belong to the sparse proposition's range `D_a(Y)<=epsilon_F N`. If one instead uses a per-fiber closeness condition, its radius should be divided by the number of old vertices; the displayed total-mass definition avoids this normalization issue.

The closed complement

`K \ (U union union_F V_F)`

is compact and contains no zero of `Phi`. Therefore its maximum is `-eta` for some `eta>0`, unless the complement is empty. The exact factorial count has a uniform `O(log(N+1))` remainder over boundary tables, and there are polynomially many types. Consequently this entire complement contributes `O(N^C exp(-eta N))=o(1)`.

Neighborhood overlaps cause no problem: the decomposition is an upper bound. No separation of the many proper phases is needed for boundedness. Crucially, no inference is made from “entropy nonpositive” to a bounded contribution at a zero.

## 2. Nonbipartite dimension induction

For fixed `B,p,r,R`, the estimate is

`E Z_R <= C_uniform + sum_(proper phases F) M_(H_F)(N)(1+o(1)) +o(1)`.

Every `H_F` is proper and invariant under `R`; after choosing a basis of it, `M_(H_F)` is exactly a smaller-dimensional instance of the same homogeneous random-lift moment. The random lift law is unchanged. The coset representatives need not be exact base solutions: their zero-defect fibers are empty or translates of this homogeneous smaller kernel.

At dimension zero there is one labeling. Assuming all lower dimensions have bounded moments therefore bounds each summand, and the phase family is finite for fixed field and dimension. This yields a finite limsup for every target `R`. There are finitely many matrices in `Mat_r(Fp)`, so a common eventual bound and threshold exist. The finitely many remaining lift sizes have finite moments, proving the full supremum in `N` and uniformity over `R` at fixed `B,p,r`.

## 3. Bipartite induction really is closed

A single-alphabet/common-endomorphism statement is not closed under mixed phases. The enlargement to `V_L,V_R` and two maps of opposite directions repairs this. A proper phase gives restricted maps

`T_L|_(H_L):H_L -> H_R`, `T_R|_(H_R):H_R -> H_L`.

They remain in the same class, and `dim H_L+dim H_R` strictly decreases unless both subspaces are full. The base case of total dimension zero has one solution. A zero-dimensional side is allowed in both the central estimate and sparse argument, so no final induction stratum is omitted.

The same reasoning remains correct for vertex-dependent maps, as covered by the appendices, but that stronger class is not necessary to close the original two-map restriction. Affine offsets after subtracting coset representatives do not require an affine induction hypothesis: each solution fiber has size at most the associated homogeneous kernel.

The all-slot entropy identity uses real coefficients `1/d`, and the local retained-product argument uses coefficient one on each omitted neighbor. No division by `d` or by a target map occurs in `Fp`. Thus singular maps, characteristics dividing `d`, and different side dimensions introduce no missing phase.

## 4. Central estimate: checks relevant to the assembly

The two exact probability identities are consistent:

`E Z=q^(dkN) E_P W`, `q^(dkN) E_Q W=1`.

The second counts all root assignments against the independent-neighbor star law; it retains the factorial and lattice normalizer instead of suppressing a polynomial factor. In the two-space case the corresponding common multiplier is `(uv)^(eN)`, since regular bipartite bases have equally many old vertices on their two sides.

Under the legal uniform law, any two neighbors are independent uniform given the root because `d>=3`. Thus the legal and independent-neighbor pair-table covariances agree. I checked the displayed eigenvalues and compatible root-margin/interaction decomposition. The combined weighted precision is strictly positive, including when one side has alphabet size one. The dimension identity cancels the remaining powers in the central Gaussian calculation.

The maximal legal-table lattice index is finite, and the comparison only needs the upper bound by this index. It does not need a claim that the compatible legal sublattice occupies every residue class. The relative tilted LLT applies on the maximal affine lattice; unattainable translates contribute zero. The local weighted rate-function estimate then removes all edge-table deviations between the logarithmic window and the fixed neighborhood. This is why the central proposition can control all star allocations with near-uniform edges.

A minor terminology improvement in the central note would be to call `Nv0+L` the **affine lattice hull of the support**, rather than the support set itself. For finite `N`, the actual support is finite and cannot equal an entire affine lattice. The relative LLT statement on the central attainable lattice is the property the proof uses, so this wording does not affect the assembly.

## 5. Sparse-boundary mechanism and correlation

The sparse quotient certificate gives `E-v>=(d-2)k/2` for support size `k`. At outside-zero vertices, one nonzero neighbor cannot sum to zero; no invertibility of the target is needed. The simple-base lift has no loops and distinct neighbor fibers, so support size one is impossible. Summing from `k=2` gives the claimed `N^(-(d-2))` correction.

The potentially dangerous factor is the number of subspace-valued assignments in the bulk. It is not treated as independent of the rare certificate. Instead the explicit image-swap coupling sends independent uniform edge permutations to their exact conditional law given prescribed edges. At most `E` swaps occur. Each changes at most four vertex rows of the homogeneous smaller operator, so kernel size inflates by at most `p^(4 dim(H)E)`, or the corresponding two-space bound. This factor is exponential in `k` and is absorbed by the support enumeration after choosing a smaller fixed neighborhood. It has no remaining power of `N`.

Thus the sparse proposition's right side is the **unconditioned smaller moment**, exactly as required for induction. There is no circular estimate of a conditioned smaller ensemble.

## 6. Scalar sharpening

For odd-characteristic scalar targets on a nonbipartite base, the only phases are full uniformity and the `p^t` point maps, `t=dim ker(B-lambda I)`. The central coefficient is `p^t`; the exact point assignments contribute `p^t` and the sparse correction is `o(1)`. For the equality `E|ker|=2p^t+o(1)`, choose the fixed central edge neighborhood disjoint from sufficiently small point neighborhoods. This is always possible for fixed `p`, because their phase centers are distinct and finite. Then the upper and lower counts give the stated equality without overlap.

For `K4,lambda=-1`, odd primes have `t=3`. The deterministic real old space has dimension three, and an extra real direction forces modular nullity at least four for every prime. The bound from the moment is `1/(p-1)+o(1)`; first taking the lift-size limit and then fixed odd primes to infinity proves the claimed real nullity conclusion.

## Audit limit

This audit validates the logical bounded-moment assembly and its stated fixed-parameter scope. It does not supply an explicit useful bound uniform in `p`, a growing-base result, a degree-two extension, or an algorithmic running-time estimate. None of those follows merely by taking the fixed constants in this induction.
