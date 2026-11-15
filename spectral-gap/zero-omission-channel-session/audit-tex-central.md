# Fresh whole-TeX audit from the central/lattice reviewer

Reviewer: `/root/central_lattice`, 2026-11-15. I read the entire actual 360-line integrated TeX source, including every noncentral section and its simplicity/fixed-power conclusion. This is a source-bound mathematical audit, not proof-assistant verification or a historical-priority determination.

**Verdict: PASS for the complete configuration and independent uniform-simple bounded-moment theorem, including all fixed powers.** No substantive correction is required at the source hash below. The algorithmic discussion correctly remains conditional on separately certified structural and computational inputs.

## Exact source scope

```
cd522c3421cd7ebe63ddaa2c103627b5b13a9d51fda03be1555415df8864630c  spectral-gap/zero-omission-channel-session/channel-moments.tex
9248cfd3b1791d8276d80e4b16de5bfdb49ca9eea662a016086747eac85320bf  spectral-gap/zero-omission-channel-session/bounded-channel-moment-theorem.md
da20fe1cc2196732527922469d12e6a5086979186ee9d7b738866a4acc039a43  spectral-gap/zero-omission-channel-session/central-channel.md
1eb6b7fde716997292b5c32e1f1243a80bc3f39fa6e0dae9d6e5c885e9d59004  spectral-gap/zero-omission-channel-session/zero-phases.md
2e6add1ce91ac01ca68c0fe6261ce934594c3d1b72283c6a03a5530fe4bc52fc  spectral-gap/zero-omission-channel-session/boundary-channel.md
```

The verdict is based on the integrated proof itself. The expanded modules were used to check preservation of details, not to supply a missing theorem hypothesis.

## Global proof audit

1. **The theorem includes the intended forced-zero case.** It fixes a reversible integer frame with arbitrary total degrees, distinguishes present factors from positive-weight active factors, allows zero weights in the certificate, and counts every raw solution. Physical stubs, internal pairing parity, loops counted twice, and repeated edges remain explicit. The example with degrees three and four really has a forced-zero internal weight and exhibits the need for heterogeneous restrictions.

2. **The type count is exact.** Ordered-star multinomials assign the roots once. The cross factorial weight and internal double-factorial weight count matching probabilities on labeled stubs, including symmetric/even internal tables. Uniform factorial bounds leave only a fixed polynomial factor, so the displayed entropy is the correct exponent on all boundary profiles too.

3. **The entropy identity has the right hypotheses and coefficients.** Repeated-target symmetrization preserves legality because each directed type pair has a common channel. Its entropy loss is retained. The unit physical omission budgets, symmetric weights, and reversibility cancel all root entropies. The internal half is consistent with the two internal root-marginal copies. Every present mutual-information coefficient is positive; only active retained-product identities are inferred.

4. **Zero phases are exhaustive.** Conditioning all but three active coordinates is justified by the three retained-product identities. Fixed-sum reflection proves uniformity of their actual laws, and every root type pulls back through some active isomorphism. The independent retained-sum support argument forces inactive image containment. The on-site and coset-offset conditions follow and are sufficient. The solved active omission makes each legal-star phase unique. Thus the phase list is finite and no continuum of boundary laws is omitted.

5. **The induction class closes.** Every restricted channel remains injective; active restrictions stay onto their local output spaces. Restricted on-site maps target those same spaces. A proper phase strictly reduces the sum of root dimensions. If all root subspaces are full, the active channels force full outputs and the phase is uniquely full uniform. The zero-dimensional base has exactly one assignment.

6. **The heterogeneous central normalization is exact.** Legal-star counts use a single active absorber. The identity `K_N E_Q W=1` is proved by the weighted reversibility calculation, without equal-degree or equal-side-size assumptions. At the ordered-star level the weighted reference measure is exactly a random configuration with iid uniform roots in their own alphabets. This identifies the law needed for concentration, rather than an asymptotically related measure.

7. **Full-table covariance is handled on the correct space.** The real dimension is the heterogeneous common-row dimension, with each slot retaining its own alphabet width. A third active absorber proves equality of all table first and second moments. The null-variance argument proves positivity on the full common-row space. No common-width matrix formula is imported.

8. **The maximal lattices are proved, not assumed.** Three active slots give a common additive output character at each root. Compensation in an active slot determines the character on every inactive image. Independence of root-row congruences follows from active within-row transfers. The finite quotient argument excludes a stricter hidden lattice. The exact index is therefore the displayed product of output-size powers, including characteristic two, zero-dimensional spaces, and repeated slots.

9. **The local-limit estimate is relative and uniform where used.** Compact exponential tilts have uniformly positive support probabilities and covariance. Fourier inversion on the maximal-lattice torus has one modulus-one point, a common spectral gap away from it, and a Gaussian expansion near it. This proves the displayed relative error and positivity at relevant affine lattice points. Matching covariance cancels the quadratic rate terms, leaving the cubic comparison. The logarithmic-window ratio retains the precise finite lattice factor. Empty compatible residues cause no difficulty for the upper bound.

10. **Weighted concentration has the correct centering.** Uniform permutations exactly generate both configuration factor laws. Image transpositions affect at most four physical incidences; a root change affects at most `2D`. Exposure couplings preserve earlier permutation entries, so the bounded-range martingale estimate applies. Internal self-partner probabilities contribute only `O(1)` total mean bias. The resulting tail is valid at every larger deviation, allowing the cubic ratio to be integrated on a sufficiently small fixed neighborhood without a polynomial loss.

11. **The selected certificate uses only valid quotient injectivity.** Active quotient channels are isomorphisms because both ambient and restricted active maps are isomorphisms. A unique active support incidence at an outside zero vertex gives a nonzero term; its equation forces a nonzero inactive cancellation incidence. Selecting that edge adds no new outside vertex. The support vertices retain at least three physical incidences and selected outside vertices at least two. The displayed excess bound follows, with loops and support size one counted correctly. Inactive quotient kernels are never ruled out.

12. **The affine-fiber and correlation arguments are valid for rectangular systems.** A quotient point need only solve the quotient equations. Its lift fiber is empty or a translate of the homogeneous restricted kernel. Uniform conditional forcing has the exact cross and internal preimage counts, preserves earlier prescriptions, and changes at most four physical row blocks per pair. The resulting rank-nullity comparison works for the fixed rectangular domain and codomain. No independence of the rare certificate and kernel count is assumed.

13. **Sparse enumeration includes unsaturated inactive stubs.** The support-stub subset choice is counted explicitly. There are no absence conditions on remaining pairs. Factoring the vertex/factorial/pairing expression leaves the excess power `(s/n)^(s/2)`; all remaining factors are bounded by a constant to the power `s`. The term-ratio bound sums from `s=1`, so no support-one exception is lost.

14. **The global neighborhoods and compact complement close the proof.** Strict versions of the bounded central-table and proper root-coset neighborhoods are open and cover every zero phase. Their complement is compact with strictly negative continuous entropy maximum. The exact type formula makes its total contribution exponentially small up to a fixed polynomial. Induction gives finite limsup and the finite initial size set gives the claimed supremum. Map uniformity uses finitely many maps at each fixed collection of finite spaces.

15. **The integrated simplicity proof is sufficient.** I checked the internal loop mean `(b-1)/2`, internal double-edge mean `(b-1)^2/4`, and cross double-edge mean `(b-1)(c-1)/2` directly from the stated stub templates and denominators. For fixed factorial moments, vertex-disjoint templates give the products. A consistent overlap of distinct loop/double-edge templates has positive edge-versus-vertex excess and contributes `O(1/n)`; conflicting stub prescriptions have zero probability. There are finitely many fixed overlap types. Bonferroni bounds at each fixed order, then the size limit and truncation limit, give a positive zero-pattern probability. The absence of loop/double-edge templates is exactly simplicity. Independent factors retain a positive joint limit. Conditioning therefore costs a bounded factor for this unbounded observable, and equal stub representation counts give exactly uniform simple projections.

16. **The fixed-power conclusion uses the same theorem.** Direct sums preserve every injection and active isomorphism. Their solution count is precisely the fixed power on the same graph; no independence of graphs is assumed. In the intertwiner case this is the block-diagonal repeated target. The theorem and simple-model conditioning therefore give every stated fixed-power bound.

The source does not certify a growing-field estimate, construct a sparse-kernel primitive, or claim historical firstness. These scope limits are consistent with what its proof establishes.

Two optional notation clarifications were sent to the author: write the usual exponential-tilt rate explicitly as `I(t)=theta(t).t-Lambda(theta(t))`, and say that the final central `epsilon` is also at most the local-limit `epsilon_0`. Both are already the standard interpretations of the displayed argument and do not change this verdict.
