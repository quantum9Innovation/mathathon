# Whole standalone TeX audit from the boundary reviewer

Reviewer: fresh `certificate_assembly` adversarial agent, 2026-11-15. I read the entire 360-line integrated `channel-moments.tex`, including every central analytic step, the phase classification, the sparse argument, the final cover, simplicity, and fixed powers. I also previously read all three expanded modules and the full master.

**Verdict: PASS for Theorem 1 and Corollary 1 as stated.** No mathematical correction is required in the reviewed standalone source. The target bounded raw finite-field intertwiner moment includes mixed total degrees and factors whose zero omission weight is forced. The larger heterogeneous class is closed under every proper-phase restriction and is the class actually proved.

## Source binding

| Source | SHA256 |
|---|---|
| `channel-moments.tex` | `cd522c3421cd7ebe63ddaa2c103627b5b13a9d51fda03be1555415df8864630c` |
| final `bounded-channel-moment-theorem.md` | `9248cfd3b1791d8276d80e4b16de5bfdb49ca9eea662a016086747eac85320bf` |
| `central-channel.md` | `da20fe1cc2196732527922469d12e6a5086979186ee9d7b738866a4acc039a43` |
| `zero-phases.md` | `1eb6b7fde716997292b5c32e1f1243a80bc3f39fa6e0dae9d6e5c885e9d59004` |
| `boundary-channel.md` | `2e6add1ce91ac01ca68c0fe6261ce934594c3d1b72283c6a03a5530fe4bc52fc` |

The theorem and integrated proof were reviewed directly; this is not a verdict inferred merely from the three module audits.

## Global proof checks

The reversible stub model, symmetric strict omission certificate, active isomorphisms, injectivity of all ambient channels, and repeated-target equality of channels are stated before the theorem. Opposite-direction channels may differ; no step requires them to be inverses. The forced-zero example has exactly the asserted certificate and demonstrates why the restricted root subspaces need not be common. Internal loops count two physical incidences throughout.

The exact multinomial/matching count includes roots once, retains internal diagonal parity, and yields the entropy exponent with a polynomial total prefactor including boundary profiles. Repeated-slot symmetrization is legal. The weighted chain-rule calculation cancels every mixed-degree root-entropy coefficient using reversibility and the unit budgets, leaving strictly positive coefficients at every pair mutual information. Only active retained-product equalities are inferred.

The full phase proof is present, not deferred. Three active physical slots give the conditional fixed-sum product-pair law and the reflection lemma. Every root type is an active neighbor, so its image uniformity pulls back to a uniform coset. Independent sums after an active omission give inactive inclusions. The on-site inclusion and affine offset follow from varying the root coset. The converse constructs the unique uniform legal-star law and verifies every equality condition. Finiteness, restriction closure, strict total-root-dimension descent, the unique full phase, and the zero-dimensional base are all supplied.

The central proof retains heterogeneous full physical-slot tables. Its normalization is exact: active isomorphisms, weighted row budgets, reversibility, and symmetric weights make the total root/output alphabet products equal. Thus the weighted reference law is precisely configuration plus iid uniform roots. A third active slot proves equality of table means and covariance; the conditional-variance proof identifies the full positive real span with no common-width formula. The three-slot Cauchy and compensator character argument gives all periods, while active within-row transfers make the root-row congruence map surjective. Singleton cases have no missing determinant or index factors.

The source gives a relative tilted Fourier estimate on a fixed neighborhood, with its maximal lattice, exact covolume, positive covariance, uniform outer-torus gap, and relative error. Equal quadratic terms yield the cubic likelihood ratio. The reference-law concentration is obtained from exact uniform permutation representations plus iid roots, with bounded changes and `O(n)` exposure length. Internal loops have only `O(1)` mean bias. Integrating the cubic ratio against the subgaussian tail on a sufficiently small fixed neighborhood proves the stated bounded central contribution without a polynomial loss.

The proper-phase proof never assumes inactive quotient injectivity. It selects all active support edges and, at an outside zero vertex with a unique active support incidence, a further inactive edge with nonzero contribution. This yields `E-(s+t)>=s/2` with loops, multiplicities, and support one included. The exact equal-preimage forcing couplings condition only on selected pairs. They alter at most four row blocks per edge, so the rank charge applies to rectangular restricted operators. The inactive support-stub subset factor is explicitly counted; no absent-edge condition is introduced. Vertex factorials and the certificate excess produce the pointwise `B^s(s/n)^(s/2)` bound, and the explicit successive-term ratio sums it from one.

The final proof uses strict phase neighborhoods in the compact feasible-profile space, so the negative-entropy complement is compact. Proper phases reduce the exact induction parameter; all finite zero phases are covered. A finite limsup becomes a supremum because only finitely many smaller admissible sizes remain. At fixed finite spaces, the map sets are finite.

## Independent check of the added simplicity argument

The standalone source adds a direct fixed-degree pattern-count derivation. Its means are correct:

* internal loops: `n binom(b,2)/(nb-1) -> (b-1)/2`;
* internal unordered double-edge patterns: `binom(n,2) binom(b,2)^2*2/((nb-1)(nb-3)) -> (b-1)^2/4`;
* cross double-edge patterns: `n_L n_R binom(b,2)binom(c,2)*2/(M(M-1)) -> (b-1)(c-1)/2`, using `M=n_L b=n_R c`.

For each fixed joint factorial moment, vertex-disjoint patterns yield the products. Distinct overlapping cycle patterns have at least one more distinct prescribed edge than distinct vertices in their overlapping component, and hence cost `O(1/n)`; inconsistent stub prescriptions contribute zero. Identical unordered patterns are excluded by factorial counting. This includes overlapping triple parallel edges and multiple loops at one vertex. There are finitely many overlap types at a fixed moment order. Bonferroni bounds for no loop/double patterns then converge, after the size limit and then truncation-order limit, to a positive exponential zero-count probability. Degree-one or other zero-mean factors are included. A configuration is simple exactly when both pattern counts vanish. Factor independence and equal labeled-stub realization counts give the stated positive joint simplicity probability and exactly uniform independent simple projections. Conditioning therefore bounds the unbounded observable by its unconditional expectation divided by a positive probability; no contiguity step is needed.

Finally, direct sums of a fixed number of all spaces and maps preserve active isomorphisms and all other hypotheses, so the power identity proves every fixed moment power. Specializing to common spaces and identity channels gives the raw intertwiner corollary with the stated loop convention.

No growth in field size, degree, frame, or number of moments is claimed. The last algorithmic sentence correctly leaves structural identifiability, right-kernel computation, and charged bit-work accounting to separate inputs. This audit makes no historical-priority claim and is not a formal proof-assistant verification.
