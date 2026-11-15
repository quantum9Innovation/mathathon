# Fresh whole-TeX audit: regular frame moments and full RSBM simplicity

Audit completed 2026-11-15 by the boundary/phase worker. I freshly read the **entire actual** `regular-frame-moments.tex`, first at its initial hash and then again in full after the two spacing-command corrections. I did not edit the TeX. This audit is bound to the corrected source below, not merely to a theorem outline or its Markdown predecessor.

## Exact audited artifacts

```
ef7b862873f7501149dcf0525eaa18b8fd6e16ecbfe77fd12746e57b3f26ba42  regular-frame-moments.tex
e276858cf236b00b38ed7f695818d82086b10935f2f80bb7e3db44cad0d6b845  regular-frame-moments.pdf
```

The scalar assembly's clarified Markdown version was also checked:

```
50bf9df8032bab7817a0239e5fe850ff0a0b4640a3a684c0206d94fae755b80d  scalar-regular-frame-theorem.md
```

The predecessor scalar Markdown audit is `audit-scalar-boundary.md`; its only subsequent change was the clarified statement that the legal compatible lattice has finite index in `K0`, without claiming that the lower-real-dimensional compatible lattice has finite index in `L0`. The TeX uses the correct index throughout.

## Verdict

**PASS: no mathematical gap found in the whole corrected TeX at the hash above.** The TeX faithfully assembles the verified exact count, central local estimate, phase classification, sparse conditional-forcing argument, full vector induction, exact odd-prime scalar coefficient, and real RSBM corollary. The PDF hash matches the parent's reported clean build. This is a source-based mathematical audit, not a claim of formal proof-assistant verification or historical novelty.

## Checks performed

### Model, exact count, and entropy

- The frame is a fixed nonnegative integer degree matrix with common row total `d>=3`, reversible positive integer size multipliers, independent pooled cross-stub bijections, and independent internal pairings. Internal loops are counted through two incidences. Admissibility retains every necessary internal parity.
- The cross factorial weight and internal double-factorial/factorial weight count the labeled-stub configurations exactly. Root assignments appear once, in the ordered-star multinomials.
- The entropy exponent has the correct internal factor `1/2`, type-size weights, and pooled reversal constraints. Repeated physical slots are symmetrized only within a fixed target type. Equality in the symmetrization loss is retained when classifying zeroes.
- The all-slot identity has the correct coefficient `(d-2)/d`; omitting a neighbor is legitimate in every characteristic. The finite-group argument uses actual positive conditional support events and gives the complete common-subspace or bipartite-two-space coset classification, including internal old-type self-incidences. The enlarged class allows all restricted maps required by induction.

### Full-uniform central input

- The legal and unrestricted star laws have the same full physical-table means and positive covariance on the same declared real space. The calculation does not discard repeated-slot fluctuations or divide by the degree in the field.
- The exact weighted reference normalizer is valid in the one-space case and in the two-space case, where reversibility and common degree imply equal total physical populations on the two sides. Zero-dimensional alphabets are harmless omitted modes; the completely zero-dimensional system has one assignment.
- The maximal legal-lattice congruences use the common root-row margin once, not once per slot. The three-slot character calculation gives every period and the exact finite index.
- The finite-support tilted Fourier argument is uniform on a fixed compact mean neighborhood: maximal-lattice aperiodicity, positive tilted covariance, and uniformly positive finite support probabilities justify the relative local estimate and eventual positivity on each relevant affine lattice point.
- Equality of means and covariance makes the relative likelihood difference cubic, while the logarithmic window has exact lattice-index ratio. The weighted reference law is genuinely configuration plus iid labels. Its permutation transposition and label-change bounds are uniformly bounded per input; the total number of exposed inputs is `O(N)`. The `O(1)` loop bias is correctly separated from the independent mean. Thus its subgaussian tail controls the cubic-ratio annulus with no missing polynomial prefactor.

### Sparse forcing and proper-phase induction

- A quotient coset point map is exact for every configuration. Every lifted quotient assignment has an affine fiber bounded by the homogeneous restricted kernel count; exact representatives are not incorrectly presumed to lift before quotienting.
- The dense support certificate counts incidences with multiplicity. It includes every incident support stub, so no extra absent-edge event is hidden. Loops contribute twice to degree and once to the number of edges. The inequality `E-(s+ell)>=(d-2)s/2` is correct.
- The internal forcing switch has exactly `m-1` preimages for each admissible output; the cross forcing swap likewise has a constant preimage count. Earlier prescribed pairs are preserved. Applying these inside independent factors gives the exact conditional graph law after at most `E` switches.
- At most `4E` physical rows change, including when some affected stubs share a vertex. The restricted operator rank comparison is valid also for the bipartite rectangular system. This proves the conditional kernel charge without independence between the certificate and bulk kernel.
- The weighted support enumeration retains all powers of `s,N`, the factorial placements, exterior stub choices, pairing choices, and the exponential-in-support rank charge. The geometric support sum correctly starts at `s=1` in the multigraph law and is `O(N^{-(d-2)/2})M_H`.
- Every proper phase strictly decreases the induction dimension. The finite phase family, central neighborhood, and root-coset neighborhoods cover every entropy zero; the complementary compact type region has negative entropy maximum. The small-size and finite-map maximum steps justify a supremum over all admissible scales.
- Direct simplicity conditioning transfers the **bounded expectation** by a positive probability denominator, without an invalid use of qualitative contiguity for an unbounded statistic. Sizes at which simple factors do not exist are explicitly excluded from this conditional statement; the remaining finite small sizes can be absorbed in the constant.

### Sharp scalar coefficient and full real RSBM corollary

- The compatible integer lattice retains pooled internal even diagonals. The all-zero star table supplies a compatible legal affine origin at every admissible scale.
- Fixed compatible translations have reference-probability ratio `1+o(1)` in the logarithmic window; exact factorial ratios have the same property, with diagonal half-exponents canceling by integer parity and zero pool-total shift. Concentration removes the fixed-width window shells. Hence actual finite compatible-lattice cosets are equidistributed without a presumed modulo-`p` saturation or pooled Gaussian determinant.
- Cross interactions placed in one physical slot force affine annihilator functions independently of multiplicity modulo `p`. The doubled internal symmetric interaction preserves integer parity and forces constant functions at odd primes. An odd cross cycle has the same effect on slopes. Connectivity propagates constancy to all types.
- The doubled-root-margin construction is an actual integer compatible direction: arbitrary cross margins extend using an anchor; internal diagonal entries `2q_ii r_i(x)` are even; pooled tables split into physical tables with common rows. Thus root margins vary freely modulo every odd prime, even if a degree or size multiplier is divisible by that prime. The remaining annihilator is exactly `ker(Q-lambda I)`, giving compatible index `p^(kp-t)` and full-uniform coefficient `p^t`.
- Scalar prime fields have only zero and full subspaces. The `p^t` point maps are exact eigenvectors for every configuration. Their neighborhoods can be chosen pairwise disjoint and separate from the full-uniform neighborhood because every old class has fixed positive size proportion. Point leakage is `o(1)` and the strict complement is `o(1)`, so adding the two coefficients gives exactly `2p^t+o(1)` in the configuration model.
- For the RSBM, an odd prime avoiding `d2` gives old kernel dimension one. Subtracting the deterministic planted modular line from the first moment yields the stated `1/(p-1)` limiting excess-nullity bound. Real excess nullity implies modular excess through vanishing integer minors. Taking the size limit first and then fixed primes arbitrarily large is legitimate; simplicity conditioning has a prime-independent positive denominator. This covers `(2,1)` and odd block sizes for even internal degrees.
- The rational nullspace recovery argument and Hadamard bit bound do not need an analytic spectral gap. The final near-quadratic charged-cost observation is explicitly conditional on separately certified algorithmic and identifiability inputs; it is not claimed from the moment estimate alone. The absence of an effective real failure rate is accurately stated.

## Changes between the two TeX reads

The two reported source corrections were missing backslashes in the spacing commands before `quad` and `qquad`. They are fixed in the audited hash. They do not change the mathematical argument. No remaining source discrepancy from the verified Markdown proofs was found.
