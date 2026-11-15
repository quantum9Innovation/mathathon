# Independent full-chain audit from the central/lattice reviewer

Reviewer: `/root/central_lattice`, 2026-11-15. The master and all three expanded proof modules were read in full at the hashes below. This review checks cross-module assumptions as well as the central argument. It does not infer the conclusion merely from the separate module verdicts.

**Verdict: PASS for the raw bounded-moment theorem and its fixed-power extension.** The optional simple-model transfer additionally uses the standard positive fixed-degree simplicity probability stated in the master. No expected near-quadratic algorithm is proved by these sources alone; the master correctly leaves its structural and algorithmic dependencies separate.

## Audited exact sources

```
5b4deb69c14bd125b99467e6e4c13dddb2d8ab6ad05eb7bacd641f44d6a34f58  spectral-gap/zero-omission-channel-session/bounded-channel-moment-theorem.md
da20fe1cc2196732527922469d12e6a5086979186ee9d7b738866a4acc039a43  spectral-gap/zero-omission-channel-session/central-channel.md
1eb6b7fde716997292b5c32e1f1243a80bc3f39fa6e0dae9d6e5c885e9d59004  spectral-gap/zero-omission-channel-session/zero-phases.md
2e6add1ce91ac01ca68c0fe6261ce934594c3d1b72283c6a03a5530fe4bc52fc  spectral-gap/zero-omission-channel-session/boundary-channel.md
```

## Full-chain findings

**Exact exponent.** The profile multinomials already assign roots. Cross factors contribute the complete pooled-table factorial weight and internal factors contribute symmetric-table double factorials with even diagonal. The exponential terms are precisely the displayed `Phi`; fixed alphabet sizes give only polynomially many profiles and a polynomial Stirling error, even when counts vanish. There is no duplicate root-label factor.

**Weighted entropy.** Repeated-target symmetrization preserves the local equation because a directed type pair has the same channel at each physical slot. The entropy gain is retained with negative sign in the original exponent. The identity cancels root entropy using both symmetric `q` and reversibility. Internal factors carry a half in their factor weight and two copies of the root entropy. Every present pair mutual-information coefficient is positive, including inactive factors; only active retained-product conditions are required. Thus the stated equality conditions are exact.

**Complete zero phases.** Conditioning all but three active coordinates is legitimate under each of the three retained-product identities. The conditional pair laws remain their original product laws. Reflection at fixed sum gives equal support-difference subspaces and actual translation invariance, hence uniform cosets rather than only coset supports. Every root type is an active neighbor somewhere. After uniformity, an active retained sum forces every inactive image subspace into the local `K_i`. The on-site and offset conditions follow for every root in its coset. Conversely those conditions produce the unique uniform legal-star law. Hence the finite list is exhaustive, even with disconnected active support or nonbipartite full support.

**Closure and descent.** The restricted channels are all injective and their active members remain onto `K_i`. The restricted on-site maps target `K_i`. Every proper phase decreases the sum of root dimensions, while full root subspaces force full output subspaces. The zero-dimensional base forces every output zero and has exactly one global assignment. No different induction parameter or common-subspace assertion is used implicitly.

**Central coverage.** The central theorem uses exactly the same spaces, channels, frame, and active slots as the master. Its full uniform legal-star law is the unique full phase. At that phase every physical-slot table is exactly the independent pair table. Therefore the inverse image of its strict full-table neighborhood is an open neighborhood of that phase in the finite profile simplex. The master does not replace physical-slot closeness with only pooled-table closeness.

**Central estimate.** The heterogeneous common-row difference space, exact normalizer, complete lattice characters, relative tilted local limit estimate, loop-aware weighted-reference concentration, and cubic tail integration all have the needed hypotheses. The local finite index is `|U_i|^(|V_i|)`; it is retained throughout. The upper bound needs no claim of finite-coset equidistribution. The detailed adversarial checks are in `audit-central.md`.

**Quotient support.** After subtraction of the type-constant quotient coset point the defect equation is homogeneous even when the representatives fail to solve the ambient equations. Only active quotient channels are asserted injective. If an outside zero vertex has exactly one active support incidence, that nonzero contribution forces an inactive support incidence with nonzero contribution. Selecting it adds no new outside vertex. Vertices with no active support incidence are not added. This yields the exact excess `E-(s+t)>=s/2` using physical incidences, including support loops and multiple edges.

**Correlation and counting.** Prescribed pairs have no absence conditions on unselected inactive stubs. The equal-preimage switching maps really produce the conditional-uniform configuration law. Rectangular rank-nullity bounds the restricted fiber under this coupling. The enumeration explicitly chooses the selected support-stub subset, so unsaturated inactive stubs cost a fixed exponential factor rather than a missing combinatorial term. The identity in boundary equation (8), together with the factorials, leaves the factor `(s/n)^(s/2)` and only a fixed exponential multiplier. The term-ratio bound sums from support size one to `epsilon n`; no singleton exceptional case is silently discarded.

**Proper-phase coverage.** For a fixed phase the strict condition that total root mass outside its cosets be less than its boundary `epsilon` defines an open neighborhood of that phase. Every actual solution in this neighborhood has at most `epsilon n` quotient defects. Its entire count, without any local profile convergence rate, is bounded by the empty-or-affine-fiber statement and the sparse estimate. Since there are finitely many phases, the thresholds can be chosen separately and a finite union still covers the complete zero set.

**Compact complement and supremum.** The feasible star-profile set with paired marginal compatibility is compact. Entropy is continuous, including its boundary. Removing the finite open neighborhoods leaves a compact set with no zero, hence a strictly negative entropy maximum. Exact counting bounds that complement by `poly(n) exp(-cn)`. The induction therefore proves finite limsup, and adding the finitely many smaller admissible sizes proves the claimed supremum. Uniformity over fixed finite maps uses only finitely many choices and is consistent with all restriction dimensions.

**Fixed powers.** Direct sums of the spaces and maps preserve injections and active isomorphisms, and the solution count for `s` identical direct summands is exactly `Z_T^s`. Thus every fixed raw power is bounded. For the original intertwiner this is the block-diagonal target construction. No growing-field or growing-target conclusion is introduced.

The result includes the forced-zero example `[[0,3],[3,1]]`; its unique certificate has active cross weight `1/3` and inactive internal weight zero. The proof treats it in the same class, rather than trying to approximate its certificate by a nonexistent strictly positive one.

This is a source-bound mathematical audit, not a formal verification or a historical firstness claim.

## Final master refresh

The final master was reread at SHA256

`9248cfd3b1791d8276d80e4b16de5bfdb49ca9eea662a016086747eac85320bf`.

Its sole change from the audited `5b4deb69...` source is the explicit instruction to choose strict smaller neighborhoods within the proved central and boundary bounds. The neighborhood argument above already checked these strict neighborhoods. The clarification preserves the complete theorem, all fixed-power consequences, and the **PASS** verdict. The three expanded proof-module hashes are unchanged.
