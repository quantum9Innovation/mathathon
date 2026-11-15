# Primary-session audit of the final proof and recovery composition

November 15, 2026. **PASS** for the stated raw configuration/simple-factor moments, all fixed powers, and the source-identified expected nearly quadratic blind recovery composition. This is a mathematical source audit, with no historical priority determination.

## Exact new sources reviewed

| Source | SHA256 |
|---|---|
| `bounded-channel-moment-theorem.md` | `9248cfd3b1791d8276d80e4b16de5bfdb49ca9eea662a016086747eac85320bf` |
| `channel-moments.tex` | `cd522c3421cd7ebe63ddaa2c103627b5b13a9d51fda03be1555415df8864630c` |
| `central-channel.md` | `da20fe1cc2196732527922469d12e6a5086979186ee9d7b738866a4acc039a43` |
| `zero-phases.md` | `1eb6b7fde716997292b5c32e1f1243a80bc3f39fa6e0dae9d6e5c885e9d59004` |
| `boundary-channel.md` | `2e6add1ce91ac01ca68c0fe6261ce934594c3d1b72283c6a03a5530fe4bc52fc` |
| `fast-recovery-composition.tex` | `ec3e96da5add3fb07699ce491927dc166361df6f7fba08448a441a005023b5d5` |

I read and reconstructed all three expanded modules, assembled the master and standalone proof, and checked the composition against the actual dependencies below. Three fresh adversarial reviewers separately audited their modules, the entire expanded chain, the whole standalone moment TeX, and the entire composition. Their source-bound audit files are indexed in `README.md`.

## Moment proof checks

**Standalone boundary wording qualification.** In `boundary-channel.md`, Section 1 writes `T_i:V_i->U_i` without repeating the adjective “linear.” Its affine-fiber and rank arguments are audited within the main theorem's explicitly linear on-site class. The master, zero-phase module, and standalone TeX all impose that hypothesis. This is an interface clarification, not a claim of a boundary theorem for arbitrary nonlinear on-site functions; the frozen boundary source is unchanged.

1. The exact star multinomial already counts roots. Cross factors use reciprocal multinomial category counts; internal factors retain symmetric pooled tables and even diagonal, with the double-factorial probability. Loops and multiple edges are included throughout. The type remainder is polynomial uniformly through zero profile counts.
2. Repeated-slot symmetry is taken only within identical channels. Its entropy gain is nonnegative and explicitly charged. The weighted chain rule gives strictly positive mutual-information coefficients `1-2q` at every present factor, including inactive ones. Root entropy cancels by reversibility, symmetry, and unit-row budgets. No inactive retained-product identity is assumed.
3. Three active physical omissions suffice for the conditional three-coordinate reflection lemma. The image marginals are uniform cosets of the same local output subspace. Every old type is an active neighbor somewhere, so all root marginals are uniform cosets without assuming active-support connectivity. Retained independent-sum supports force every inactive image subspace into the local output subspace. The on-site and coset compatibility conditions are necessary and sufficient.
4. For fixed cosets the legal-star law is unique. The phase set is finite. Restrictions retain injective channels and active isomorphisms and strictly lower total root dimension unless the phase is full. If all roots are zero-dimensional then all outputs are zero-dimensional, so the induction base count is one. Mixed-dimensional phases on nonbipartite full supports remain in scope.
5. The heterogeneous legal-star count is `|V_i| product_s |V_j(s)|/|U_i|`. The exact independent-star normalizer reduces to `product_i(|V_i|/|U_i|)^n_i=1`, by the symmetric weighted balance identity. The normalized weighted reference law is exactly a configuration with iid uniform roots.
6. Root and any two physical neighbor labels are product uniform because a third active isomorphism absorbs the local constraint. The full table covariance therefore agrees with the independent law, and a direct zero-variance argument proves positivity on the complete common-root-row table space even when slot widths differ. No equal-width covariance matrix is reused.
7. The circle-character calculation uses three onto active slots and an active compensator for arbitrary inactive label variation. It identifies every legal lattice period. The independent congruence map is onto separately at each root value, giving exact index `product_i |U_i|^|V_i|`.
8. The relative tilted local limit proof is uniform on a fixed compact mean neighborhood, with the maximal lattice covolume retained. Positive covariance supplies an interior mean and inverse tilt map. The Fourier modulus is uniformly below one away from its sole maximal-lattice period; the local cubic error integrates with Gaussian domination. Thus the comparison is relative at every relevant affine lattice point, rather than an absolute central-window bound extended to an annulus.
9. Configuration permutations and root labels have bounded martingale differences, with only `O(1)` internal-loop bias. The actual weighted reference law has a subgaussian tail at all larger deviations. Choosing a small fixed neighborhood integrates the cubic likelihood ratio with no polynomial loss; the logarithmic window contributes at most the finite lattice index plus `o(1)`.
10. Inactive quotient channels may have kernels. The selected sparse certificate uses only active quotient isomorphisms to force cancellation edges. Every selected support vertex has at least three incidences, every selected outside vertex at least two, hence `E-(s+t)>=s/2`. Every selected edge touches the support. No saturation of inactive support stubs or absence of unselected edges is required.
11. Unsaturated support stubs are explicitly chosen at cost `2^(D s)`. The exact conditional forcing couplings have uniform preimage counts and change at most four physical rows per edge. Rectangular rank-nullity controls the restricted homogeneous kernel even when coset representatives have no ambient exact lift. This gives the weighted `B^s(s/n)^(s/2)` support bound, starting at one, with sum `O(n^-1/2) M_H`.
12. Strict smaller central and root-coset neighborhoods form an open cover of all finite entropy zeros. The complement is compact with strictly negative entropy. Induction therefore proves the raw supremum, with no missing flat boundary or prefactor. Direct simplicity conditioning is justified by the explicit bad-pattern/Bonferroni proof and constant labeled-stub multiplicities. Direct sums give every fixed power.

## Actual recovery and linear-algebra dependencies read

All paths below are rooted at `spectral-gap/` and were read without edits.

| Dependency | SHA256 |
|---|---|
| `partitioning-frontier-session/nonregular-fibers/strict-q-recovery/zero-omission-addendum.tex` | `2db029a9d3058122f939ccec2d190172c439d70ab0d4f72579f19bfbc49adc8d` |
| `partitioning-frontier-session/nonregular-fibers/strict-q-recovery/strict-q-blind-frame-recovery.tex` | `0042ca4067451330f955c9621bc741694369f4743ee4823c70f16f6a87d4c634` |
| `partitioning-frontier-session/nonregular-fibers/strict-q-recovery/support-audit/mixed-degree-small-support.tex` | `b0c449292c23e63e09cdb958ba24430cd594acf1533f9882c12999f6197bd017` |
| `strict-omission-frame-recovery-root-audit.txt` | `d0287aad168253f8de89be8c76f5b272cd096a776a1838e7ebea6860aaa332d1` |
| `partitioning-dynamic-session/rsbm-full-kernel/certified-full-kernel.tex` | `bb6ec1086a2d46f4a1d0b66c69aadc2d120b07157ba8e95f3c08ffb187843473` |
| `partitioning-dynamic-session/rsbm-full-kernel/intertwiner-extension.txt` | `cb893b0def524ba101a4419adf922f0dec60ad3156348c8e91d600887e743df9` |
| `regular-frame-fast-algorithm-root-audit.txt` | `127b233ee065d4ab158f251f57a33ea771ac101a3fc2e1637fc7e09273bd8c09` |

The existing symmetric kernel primitive is taken with its identified per-input theorem and prior root audit. Its primary-source preconditioner theorems are not new results of this session. Its exact nonsymmetric reduction and all application interfaces are rechecked in the composition.

## Complete composition checks

- The zero-weight one-hot gap is rederived from the actual weighted entropy identity. Omission-weighted divergence has total mass one and costs at most `2L/c`; the squared-discrepancy statistic has range `2D^2`; the weighted variance lower bound is `3 delta`. This gives exactly `9c^3 delta^2/(4D^4)` and uses no positive lower bound on an omission weight. It includes boundary laws, unused candidate labels, and non-surjective old point maps.
- The ordinary small-support certificate for `AV=VR` uses all support stubs and minimum total degree three. It is distinct from the generalized quotient certificate. In the simple model singleton bad supports are absent, so its sum starts at two. Together with the clean closed neighborhood in each planted class, it proves the integer compatibility `QT=TR` and then exact closure `Y=JT`. The structural conclusion covers the whole finite candidate family and does not require lower bounds on new class masses.
- The new moment applies to each arbitrary target reduced over the same fixed odd prime `p=3`. Certificate feasibility belongs to the true frame alone. The candidate family is finite at fixed class/degree bounds; nonsymmetric quotients, singular targets, residue collisions between integer targets, and primes dividing sizes or degrees are harmless.
- Column vectorization uses `I_r tensor A-R^T tensor I_n`. The symmetric block has twice the nullity, but its full basis is computed only as a polynomial-cost intermediate. Bottom-coordinate projections span the complete right kernel; independent selection and pivot normalization are charged. The left kernel is not enumerated.
- The compact right-kernel certificate regenerates the true shifted recurrence length and sandwiches rank using `ell<=2 rank K` and verified independent right nullvectors. It includes zero/full rank, canonical base-field descent, and no dense fallback.
- Odometer enumeration charges `O(n p^h)` up to logarithms and avoids both `p^(2h)` and `h p^h`. Exact row tests, nonemptiness, and original integer identities eliminate modular artifacts. The full finite search finishes before selecting a maximum. Empty-list reporting is specified for arbitrary bounded-degree inputs; model inputs always contain the planted candidate.
- The per-input Las Vegas expected work is `soft-O(n^2(h+1)+n p^h)`. The raw actual-simple-law moment bounds both terms unconditionally, including rare graphs. Expected workspace is `soft-O(n)` and output can be streamed. The statistical event enters only the identification of the returned maximum with the planted partition, never the runtime expectation.
- Connectedness fixes positive proportions, and there are finitely many true frames at fixed bounds, so moment, gap, support and simplicity constants have finite uniform extrema after selecting one valid certificate per frame. The algorithm receives neither the true frame nor the certificate.

## Validation and freeze

The standalone moment PDF has eleven pages and the composition PDF six. Both final two-pass builds have no warnings, unresolved references, or overfull boxes. The moment TeX and master were frozen before final whole-source reviews; the sole master wording change selected literal strict open subneighborhoods and was refreshed by all reviewers. The final PDFs and all review files are hashed in `artifact-manifest.sha256`.

No counterexample or unresolved proof defect was found within the stated strict-upper certificate class. The result does not include `q=1/2`, growing parameters, dependent factors, noise, or a new sparse kernel primitive. All session writes were confined to the new directory.
