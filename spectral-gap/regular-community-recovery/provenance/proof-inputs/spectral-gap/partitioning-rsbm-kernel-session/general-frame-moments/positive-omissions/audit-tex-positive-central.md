# Fresh complete-source audit of the positive-omission TeX

**Verdict: PASS for the final standalone TeX, including mixed-degree moment proofs, scalar refinement, and the charged blind-recovery composition using its explicitly identified external inputs.**

Audit date: 2026-11-15. The entire actual TeX was read from preamble to `end{document}`, and the final corrected source was then read in full again. The reviewer made no edits to the TeX, the mixed-degree proof files, or any frozen parent packet. This is a mathematical and source-fidelity audit, not a proof-assistant verification or historical-novelty certification.

## 1. Bound final artifacts and dependencies

All first six files are in `general-frame-moments/positive-omissions/`.

| Artifact | SHA-256 |
| --- | --- |
| `positive-omission-moments.tex` | `f6d65ea8a2cc997f8ba137641610a953dde2fbbaa24843bb0ccd251dccda659a` |
| `positive-omission-moments.pdf` | `2b6eea2c161e934b753843b9667c864dc504c251f05263f8433bd31b7ecaa593` |
| `central-positive.md` | `489062a3cb600d2c5d7b3c66dde9300357f53391152868f2bbdee4f8d2380985` |
| `boundary-positive.md` | `269803d130d344465235060cf5359875b6cbcb00d9763e15cf0f54dfd51075d2` |
| `scalar-positive.md` | `46d5c8e9e9f7df950d16d6bab51a0010ae19fe1fff3799295579d8901f23e5a2` |
| `positive-omission-theorem.md` | `424c281a4f93713b3dfe31f6145f5bde3e38cbb21d19b477d5dd100b5eb11861` |

The initial fully read TeX had hash `4e23ef3f370b0ffcd339670625402da873442a5f674f479eba0db94bb5ab1c73`. The final wording explicitly locates blind recovery in the independent uniform simple-factor law and explicitly requires at least two types in the internal-degree-at-least-two covered class. Both clarifications are correct. The final TeX was independently reread in full, rather than only accepting a reported patch.

The final build log reports nine pages and contains no LaTeX warnings, unresolved references, errors, or overfull boxes.

The actual external sources consulted for statement and charge fidelity were:

| External source | SHA-256 |
| --- | --- |
| `spectral-gap/partitioning-frontier-session/nonregular-fibers/strict-q-recovery/strict-q-blind-frame-recovery.tex` | `0042ca4067451330f955c9621bc741694369f4743ee4823c70f16f6a87d4c634` |
| `spectral-gap/partitioning-dynamic-session/rsbm-full-kernel/certified-full-kernel.tex` | `bb6ec1086a2d46f4a1d0b66c69aadc2d120b07157ba8e95f3c08ffb187843473` |
| `spectral-gap/partitioning-dynamic-session/rsbm-full-kernel/intertwiner-extension.txt` | `cb893b0def524ba101a4419adf922f0dec60ad3156348c8e91d600887e743df9` |

For the first external source the exact model, certificate, main structural theorem, structural closing argument, and unknown-frame algorithm were checked. For the second its actual per-matrix theorem and hypotheses were checked. The complete nonsymmetric intertwiner supplement was read. Those external packets are used as the previously established inputs explicitly declared by the standalone note; this audit does not claim to reprove their primary sparse-linear-algebra ingredients from scratch.

## 2. Mixed-degree model and statement scope

The positive certificate is required on **every active factor**, with strict positivity, strict upper bound one half, symmetry, and a unit weighted row. It implies every local degree is at least three. The actual graph law is the independent internal-pairing/cross-bijection configuration law, retaining loops and parallel edges until conditioning. The theorem does not substitute a permutation model for it.

The vector moment is uniform over the finite family of target matrices at fixed field and dimension. It includes every admissible scale; after simplicity conditioning it is asserted only at sizes where the simple factors exist. Small finite sizes can be absorbed into the constant.

The exact scalar moment is restricted to fixed odd primes and nonbipartite old support and is stated for the configuration law. Its real-multiplicity consequence is then transferred by positive-probability conditioning. No growing-prime estimate, exact conditional scalar moment, or polynomial real-failure rate is asserted.

The final blind-recovery corollary now explicitly uses the independent uniform **simple-factor** law, which is the model of the cited structural theorem. This correction resolves the only graph-law statement ambiguity noticed in the initial version.

## 3. Weighted entropy and phase classification

The exact star count retains the internal half-edge coefficient and even pooled diagonal. Root assignments appear once in the star multinomials. Repeated-slot symmetrization is restricted to the same target old type and preserves pooled feasibility and the local equation.

The local weighted omission identity is correct:

`H(P_i)=(2-d_i)H(mu_i)+sum_j q_ij(1-theta_ij)H(nu_ij)-sum_s theta_is J_is`.

The slot weights sum to one; the omitted coordinate is determined with coefficient one over every characteristic. Reversibility and symmetric omission weights give the printed global mutual-information identity. In particular each root entropy cancels using its **own** degree through `sum_j q_ij(1-2theta_ij)=d_i-2`; there is no remaining common-degree assumption.

Every present pair coefficient and every omission coefficient is positive. Therefore every entropy zero has all pair mutual informations and all omission defects zero. The generic finite-group fact is applied at each type with the number of variables equal to its local `d_i`; its use of a dummy symbol `d` does not impose common row totals. The uniform-coset classification, even-walk propagation, internal self-incidences, two-space bipartite phases, and strict dimension decrease agree with the mixed-degree boundary source.

Active zero weights are correctly excluded: the proof would otherwise lose some omission equalities and would not justify the same common-subspace phase classification.

## 4. Exact two-space normalizer

The TeX explicitly derives physical-side equality using the weighted certificate:

`sum_L n_i=sum_(L,R) n_i q_ij theta_ij=sum_(R,L) n_j q_ji theta_ji=sum_R n_j`.

This is the correct replacement for the common-degree balance argument. Individual class sizes and local degrees may vary.

With local star lengths `d_i`, the actual normalizer ratio is printed as

`K_N E_Q0 W=product_i(|V_i|/|U_i|)^{n_i}`.

It is one for a common alphabet, and in the two-space class it is `(u/v)^{n_L-n_R}=1` by the proved weighted balance. The identity remains true for every pair of restricted side alphabets because the physical frame and its certificate do not change under restriction. No exponential normalizer factor was silently discarded.

## 5. Central covariance, lattice estimate, and tails

The local covariance is the correct variable-degree operator

`Sigma_i=(|V_i||U_i|)^(-1)[Id+(d_i-1)Pi_row]`.

The legal and unrestricted laws have the same mean and covariance because every `d_i>=3`. Both eigenvalue statements and the real common-row table space are correct, including singleton alphabets. The maximal lattice index remains `product_i |U_i|^{|V_i|}`; the three-slot character proof is local and requires no equality of degrees.

The finite-support compact-tilt Fourier argument is relative, retains the exact lattice and covariance factors, and guarantees positive probabilities at the relevant affine lattice points. Applying it separately to type sizes `a_iN` yields the uniform cubic likelihood estimate and logarithmic-window ratio as printed.

The normalized weighted law is exactly configuration followed by iid root labels. Its bounded-difference proof uses the maximum degree `D`, not a fictitious common degree: permutation transpositions change at most four incidences, and a type-`i` label change affects at most `2d_i<=2D`. Internal self-pairing probabilities have the same bounded loop bias as in the source. Integration of the cubic ratio against the resulting subgaussian tail retains a bounded full-uniform contribution with no polynomial loss.

## 6. Boundary induction with mixed support degrees

The support-degree sum is used in the certificate excess:

`2i+j=sum_(v in S)d_v>=d_*|S|`, while `E<=D|S|`.

Together with exterior multiplicity at least two, this gives `E-V>=(d_*-2)|S|/2`. Loops and singleton support remain included. The exact forcing couplings and changed-row rank charge are degree-independent, and the enumeration uses `D` only in its finite combinatorial constants. The printed bound and its geometric sum therefore have the correct exponent involving `d_*`, not an unjustified common `d`.

Proper phases reduce the correct one-space or two-space induction dimension. The controlled central and coset neighborhoods cover all zeros; the compact complementary entropy region is strictly negative. Direct simplicity conditioning is applied to the actual unbounded moment with a uniform positive probability at fixed frame, rather than through qualitative contiguity. No new gap was introduced in compressing the boundary source into the TeX.

## 7. Scalar refinement and fixed integer multiplicity

The scalar lattice argument carries over without row regularity. It uses the actual integer compatible subgroup with internal even diagonal. Fixed compatible translations preserve the unrestricted central mass asymptotically; cross factorial powers and internal half-diagonal powers cancel by zero total pool shift. Concentration removes the translated outer shells and gives equal finite-coset masses.

The internal parity-preserving interactions, cross two-by-two transfers, and twice-root-margin construction are independent of common degree and permit arbitrary multiplicities modulo the odd prime. The residual annihilator is `(Q-lambda I)c`, with the correct matrix orientation. The exact central coefficient is `p^t`, and the scalar positive-omission phase classification leaves only the full-uniform phase and `p^t` exact old-type point maps. Point neighborhoods, the mixed-degree support estimate, and the compact complement yield the stated `2p^t+o(1)` moment.

For a fixed integer eigenvalue, avoiding one nonzero maximal-rank old minor makes the old modular dimension equal to the real one; in rank zero the standard zero-by-zero determinant is one, so there is no exceptional-prime issue. The type-indicator lift is injective even if a prime divides class sizes. Subtracting its deterministic modular baseline gives the displayed `1/(p-1)` excess-nullity bound. The prime is fixed before the size limit and simplicity probability is prime-independent, so the real conclusion is correct. Its specialization to the already-frozen RSBM result is accurately labeled as a specialization rather than the new mixed-degree headline.

## 8. External structural input and blind algorithm fidelity

The actual frozen strict-weight source states exactly the required model and certificate: independent uniform simple regular/biregular factors, connected bounded integer frame, positive fixed proportions determined by balance, and positive symmetric unit-row omission weights below one half on every active factor. Its main structural theorem asserts that every equitable partition into at most `K` nonempty cells is a compatible planted coarsening, and its algorithm is not given the quotient, sizes, or certificate. The standalone TeX invokes this structural result explicitly rather than purporting to prove it from finite-field bounded moments alone.

The actual certified full-kernel theorem is a per-input Las Vegas bit-work bound for every sparse symmetric input over a fixed odd field. The entire intertwiner supplement extends it by symmetric block linearization to `K_R=I_r tensor A-R^T tensor I_n`. Its projected complete right kernel has the exact per-input charge `tilde O(n^2(h_R+1))` at fixed `r,p,D`; base-field descent and failed computational trials are included. The left kernel is projected away before enumeration, so the application does not accidentally require an exponential moment at `2h_R`.

The supplement's known-size application checks prescribed sizes; the new application replaces that filter by nonempty columns and uses the independently proved unknown-size structural theorem. This does not change the kernel primitive, completeness, or charge. Both `K_R` and its transpose have linear sparse application cost at fixed bounds, even for nonsymmetric quotient candidates.

The finite candidate family, base-prime odometer update, and exact integer verification are correctly charged. A constant-size candidate family can have distinct integer matrices with the same reduction modulo three; exact integer verification correctly distinguishes them. There is no need for the chosen prime to exceed the degree. Complete right-kernel enumeration includes the true quotient indicator; selecting maximum class count recovers the planted classes on the structural event.

The new bounded moment holds for every candidate target matrix, not only the true quotient. Hence averaging the valid per-input kernel charge and `tilde O(n p^{h_R})` enumeration charge gives unconditional expected `tilde O(n^2)` work, including rare large kernels and retries. The algorithm has no uncharged high-probability truncation. Connected reversible integer frames at fixed `K,D` form a finite family with fixed proportions, so choosing one qualifying certificate for each and maximizing constants is legitimate. All fixed higher exponential moments follow from block-diagonal repeated targets as stated.

This audit checks compatibility and composition with the explicitly external established primitives; it does not claim that the moment theorem by itself proves sparse linear algebra or structural identifiability.

## 9. Covered examples and exclusions

The common-degree certificate `theta=1/d` is valid. For the mixed internal-degree class, `k>=2` connected implies every cross total `b_i>0`; with `epsilon=1/(4D)` the printed internal weight `(1-epsilon b_i)/h_i` is positive and strictly below one half, including when `h_i=2`. The final abstract now includes the needed at-least-two-types qualification, matching the displayed example.

The `K_5` minus one edge weights give unit rows exactly and are all positive below one half. Its simple-base lifts require no simplicity conditioning. The `K_{3,12}` obstruction has physical side sizes `3N,12N`, rank at most `6N`, and nullity at least `9N` over every field, hence an exponential zero-eigenvalue moment. It cannot satisfy the certificate because the proved weighted balance would force equal side sizes. These checks support, rather than enlarge, the stated scope.

No active-zero-weight, half-weight-boundary, growing-frame, growing-field, noisy, or arbitrary deterministic-factor theorem is claimed.

## Final verdict

**PASS at TeX hash `f6d65ea8a2cc997f8ba137641610a953dde2fbbaa24843bb0ccd251dccda659a` and PDF hash `2b6eea2c161e934b753843b9667c864dc504c251f05263f8433bd31b7ecaa593`.** No remaining common-degree residue, normalizer error, scalar carryover gap, or algorithmic charge mismatch was found. The scope clarifications in the final version are correct. Old parent packets were read only and remain unmodified.
