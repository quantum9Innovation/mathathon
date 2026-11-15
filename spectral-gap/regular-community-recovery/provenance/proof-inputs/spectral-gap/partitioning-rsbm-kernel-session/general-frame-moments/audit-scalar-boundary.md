# Fresh assembly audit: scalar regular-frame moment and RSBM simplicity

Audit completed 2026-11-15 by the boundary/phase worker. I freshly read the **entire actual assembly** `scalar-regular-frame-theorem.md`, not only an outline or delegated summary, and independently checked its composition against the central and boundary source files. No simulations or numerical eigenvalue evidence are used in this audit.

## Audited source hashes

SHA-256 of the exact theorem assembly read twice during this audit:

```
236e56d2d028835bf86b8f6c2a3f29864cdb84cb3140b248ab35143d8b19fa0c  scalar-regular-frame-theorem.md
```

Dependency versions inspected or independently reconstructed:

```
e64d46ae873a6ce568b76784788b1605a38e249c2f8983451372486eff0315a7  central-frame.md
cbfd5c6c8372bbbb1a4e2ef01426bfd93225e54cc7842e9efadc7802fe07f5e4  boundary-frame.md
7738f0c8d2aa86f7e4aaf50ff02f2b6741885076a60625f368c593d5755cc2e2  scalar-lattice-rank.md
2ca675978aa450a3db04d33d33b571bb0f455e33e006c04f2fde7227c49023e0  scalar-central-equidistribution.md
```

The boundary and scalar-lattice notes are my own primary derivations in this team. The actual assembly's doubled-root-margin construction differs from the unscaled construction in my lattice note; I checked that variant independently below. The central note and its weighted-reference law were freshly read as mathematical inputs, including its fixed-neighborhood likelihood estimate, maximal-lattice proof, and permutation/label concentration argument.

## Verdict

**PASS: no mathematical gap found in this assembled scalar argument at the hashes above.** It proves the exact fixed-prime configuration-model moment `2p^t+o(1)` for connected nonbipartite regular frames over fixed odd prime fields, then proves the planted eigenvalue simple with high probability in the original uniform-simple RSBM for every fixed `d1>d2>0` and every admissible block-size sequence. The proof supplies no uniform growing-prime estimate or effective real failure rate.

This is a mathematical audit, not proof-assistant verification or a historical novelty determination. Changing the theorem source after the recorded hash requires checking the changed version.

## 1. Exact compatible-lattice coefficient

The assembly retains full physical-slot tables. Its unrestricted integer difference lattice correctly records zero total per slot and one common root-row vector at each old type. The legal congruences subtract `lambda x` times that common root-row vector **once**, rather than once per slot. The maximal-index count `p^(kp)` is valid: the three-slot character argument gives all periods, and a within-row transfer in one slot varies a single root-label congruence arbitrarily. It uses `d>=3`, not division by `d`, any degree, or any size multiplier.

The compatibility lattice correctly keeps internal pooled symmetry and the integer even-diagonal condition. The all-zero star array is legal and compatible at every admissible size; thus no additional affine residue condition was omitted. Only the intersection with the maximal legal lattice defines the legal compatible coset.

The fixed-translation argument is sound. For each fixed compatible integer shift, the unrestricted relative local CLT makes its probability ratio `1+o(1)` in the logarithmic window. All full-slot and present pooled entries are positive of order `N` there. Cross factorial powers cancel by zero pool-total shift. For internal factors, diagonal shifts are even; the double-factorial exponents combine with off-diagonal factorial exponents to half the symmetric pooled total shift, also zero. Thus the normalized weighted-reference masses have ratio `1+o(1)` after each fixed compatible shift.

The weighted-reference subgaussian tail makes the discarded logarithmic-window mass and its fixed-width boundary shells `o(1)`. Fixed shifts therefore permute finite compatible-lattice cosets with asymptotically equal probability. Their actual integer quotient index, not a presumed finite-field saturation index, gives mass `1/J+o(1)` to the legal coset. Combining this with the full local ratio `I(1+o(1))` and the already controlled fixed-neighborhood annulus gives `I/J+o(1)` exactly.

## 2. Congruence-image rank, including multiplicities divisible by p

The cross `2x2` interaction transfer can indeed be placed in one physical slot per orientation while preserving zero root margins. Therefore its character equation has no degree factor. It forces affine root-label coefficient functions with opposite slopes across a cross support edge.

The doubled symmetric internal interaction is an actual integer direction: symmetric pooled table, zero row sums, even diagonal. Its character value forces a constant coefficient function at that old type for odd `p`. An odd cross cycle forces the same vanishing of all slopes. Connectivity then makes every annihilator function constant on root labels. Repeated target types and degrees divisible by the characteristic do not invalidate any of these directions.

The assembly's root-margin extension is also valid. Starting from arbitrary zero-total integer margins `r_i`, it constructs actual margins `2r_i`. Cross pooled rows and columns can be extended using anchor label zero. Internal diagonal entries `2q_ii r_i(x)` have exactly the desired row vector and have even diagonal. A pool with rows `2q_ij r_i` decomposes into `q_ij` physical tables with common row vector `2r_i` by anchor tables plus a residual. Directions may have negative entries, as they should. Since `p` is odd, these doubled margins range freely modulo `p`.

For constant annihilator coefficients `c_i`, pooled reversal and internal symmetry yield exactly the coefficient `(Q-lambda I)c` on each freely variable weighted root-margin sum. Consequently the annihilator has dimension `dim ker(Q-lambda I)=t`, so `J=p^(kp-t)` and the full-uniform coefficient is `p^t`. No invertibility of a `q_ij` or type-size multiplier was used.

## 3. Point phases, disjoint neighborhoods, and strict complement

For a scalar prime-field alphabet, the nonbipartite phase classification has only subspaces zero and the full field. Thus the assembly lists every zero-entropy phase: the full-uniform phase and exactly `p^t` point maps satisfying the old-type equation.

Each point map is an exact type-constant eigenvector for every configuration, including internal loops counted through their two incidences. Its zero-defect contribution is exactly one. The correlation-safe certificate estimate applies to the zero-dimensional restricted system, with homogeneous count one, and correctly retains support-one multigraph defects. Its `O(N^{-(d-2)/2})` leakage tends to zero for all `d>=3`.

Distinct point maps differ on an entire fixed-positive-proportion old class, so their fixed small defect neighborhoods can be chosen disjoint. A full-uniform physical-table neighborhood can be chosen disjoint from them as well. The feasible star-type region is compact after the fixed margins/reversals are imposed. Every zero is in one of these neighborhoods, including the strict-concavity symmetrization equality condition for repeated physical slots. Hence the remaining region has a strictly negative entropy maximum. Uniform finite-alphabet Stirling bounds and a polynomial number of types make its contribution `o(1)`. These observations justify adding the two `p^t+o(1)` pieces without unexamined overlap or missing boundary mass.

## 4. Real simplicity and the exact original model

For the RSBM quotient `[[d1,d2],[d2,d1]]`, positive internal degree supplies old-type self-incidences and positive cross degree supplies connectivity. At the planted scalar `d1-d2`, any fixed odd prime avoiding `d2` separates the two old eigenvalues by `2d2`, so `t=1`, including when that prime divides the planted eigenvalue or the total degree.

Real excess nullity forces vanishing of every integer minor of order `2N-1` and hence finite-field nullity at least two. The exact configuration moment bounds its probability by `2/p+o(1)` for each fixed admissible prime. The planted integer sign vector supplies nullity at least one deterministically. First taking the size limit and then fixed primes arbitrarily large proves configuration-model nullity exactly one with high probability. No exchange of these limits is needed.

The event that both internal configuration factors and the cross factor are simple has probability bounded below by a fixed positive degree-dependent constant along every admissible block-size sequence. That bound is independent of the auxiliary prime. Conditioning therefore preserves the just-proved vanishing failure probability. Labeled-stub representations of each simple factor have constant multiplicity, giving exactly the original independent uniform simple internal and cross factors. The assembly does not assert that the sharp finite-field constant remains unchanged after this conditioning, which would require a separate analysis.

## Minor wording clarification

The sentence “Both are fixed finite-index lattices independent of size” immediately after defining `J` should be read as saying that `K0` and `K0 intersect L` are fixed lattices with finite index **between them**. In general `K0` has smaller real dimension than `L0` and is not finite-index in `L0`. The subsequent proof uses only the correct index `J=[K0:K0 intersect L]`; this is a wording clarification, not a gap in the argument.
