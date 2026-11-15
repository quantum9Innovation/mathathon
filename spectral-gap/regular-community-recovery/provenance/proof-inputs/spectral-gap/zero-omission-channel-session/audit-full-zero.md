# Independent audit of the complete bounded channel-moment chain

Auditor: `/root/zero_phase`, fresh delegated adversarial agent, 2026-11-15.

**Verdict: PASS for the bounded raw finite-field moment theorem in the sources below, including zero omission weights.** The proof is for fixed fields, dimensions, frame data, and maps; it supplies no growing-field estimate. No historical-priority verdict or new algorithmic theorem is included in this audit.

## Exact source hashes

All four mathematical source files were read in full at these SHA256 hashes:

```
5b4deb69c14bd125b99467e6e4c13dddb2d8ab6ad05eb7bacd641f44d6a34f58  bounded-channel-moment-theorem.md
da20fe1cc2196732527922469d12e6a5086979186ee9d7b738866a4acc039a43  central-channel.md
2e6add1ce91ac01ca68c0fe6261ce934594c3d1b72283c6a03a5530fe4bc52fc  boundary-channel.md
1eb6b7fde716997292b5c32e1f1243a80bc3f39fa6e0dae9d6e5c885e9d59004  zero-phases.md
```

All paths are relative to `spectral-gap/zero-omission-channel-session/`. The actual candidate hash is `fbc5df08244c013a5e5102fc3af486047559d0b98319a70ff807b3d118925442`. The older general-frame proof was inspected as read-only context; no conclusion below treats that common-space theorem as a black box proving the heterogeneous extension.

## 1. The theorem and exact type count

The master states precisely the heterogeneous channel hypotheses used in the three modules: present-factor injections, isomorphisms on every positive-weight factor, maps constant across repeated old-target slots, symmetric strict weights with unit physical rows, independent uniform factor configurations, and fixed finite data. The spaces and dimensions may differ across types. Opposite-direction channel maps need not agree or be inverse. Output and root zero spaces are allowed.

The exact matching weight is correct on cross tables, and on internal tables has the required half-edge pairing factor with even diagonal. The root labeling is counted once by the ordered-star multinomial. Uniform logarithmic Stirling error holds at zero profile counts, so the compact complement can be handled without excluding boundary points. The number of profiles is polynomial because the complete legal-star alphabet is fixed and finite.

## 2. Entropy zeros and restriction closure

The separate detailed audit `audit-zero-phases.md` checks the entire entropy/classification proof. The master uses exactly that result, including the unsymmetrized entropy loss and positivity of every mutual-information coefficient `1-2q_ij` even at zero weights. Only active omission equalities are asserted.

The three active physical slots exist at every vertex by the strict one-half bound. The proof conditions the other coordinates only on positive product-support events, then applies a genuinely three-variable fixed-sum reflection argument in the one local output space. This proves uniform active image marginals. Every root type appears as an active neighbor somewhere, irrespective of connectivity of the active subgraph; its law is therefore uniform on an affine root coset. An active retained-product law then forces all inactive image subspaces into the same local output subspace. The stated inclusion and offset conditions are necessary and sufficient, and the uniform star law is unique.

Restriction thus gives the exact same channel class, with active restrictions onto the output subspaces. The correct induction parameter is the **sum** of all root dimensions. Every proper phase strictly lowers it. A phase with all root subspaces full has all output spaces full by one active isomorphism per row; there is one full-uniform phase. At total root dimension zero the same isomorphisms force every output space to be zero and give the single-assignment base case.

The master correctly avoids identifying subspaces across unrelated root spaces. Its explicit forced-zero example `[[0,3],[3,1]]` has the stated unique certificate and supports heterogeneous phases: with zero on-site maps, `H_2` may be any proper subspace of `H_1`, with output subspaces `K_1=H_2`, `K_2=H_1`. In particular its nonbipartite full support does not force a common root subspace.

## 3. Central likelihood-ratio bound

I checked the local table argument against its heterogeneous hypotheses rather than importing the old equal-width calculation:

* One active isomorphism makes the legal-star count exactly `|V_i| product_slots |V_j|/|U_i|` for every root value.
* A third active slot, distinct from any two specified slots, makes the root and those two neighbors product uniform. Thus all table-coordinate means and covariances agree under the constrained and unrestricted laws, even when slot widths differ.
* The conditional-variance calculation identifies precisely the common-root-row table tangent space and proves strict covariance positivity on it. Singleton alphabets and zero-dimensional tangent spaces cause no defect.
* For each fixed root value, the three active isomorphisms give the Cauchy character identity on the full local output space. Compensation by one active coordinate forces every inactive character to be the pullback of the same output character. Root transfers supply the remaining row offset. The congruence map is surjective independently for each root value, and its kernel is the complete maximal legal lattice. The local index `|U_i|^(|V_i|)` is therefore correct.
* The finite-support tilted Fourier inversion works on these maximal lattices with strictly positive covariance. Compact tilts keep all support probabilities uniformly positive and give a uniform spectral gap away from the sole period in a lattice torus. Its local Gaussian expansion yields a relative error, including positivity of the unrestricted denominator at all relevant lattice points. Agreement of the first two cumulants gives the cubic rate-function difference used in the fixed neighborhood.

The normalizer is an exact algebraic identity. Active isomorphisms turn each unit omission row into `log|U_i|=sum_j d_ij q_ij log|V_j|`. Detailed balance and symmetry then give `sum_i n_i log|U_i|=sum_i n_i log|V_i|`. This verifies `K_N E_Q W=1` with no assumption of equal degrees, equal populations, or a common alphabet. The normalized weighted law is exactly a random configuration plus independent uniform root labels.

Under that law, a permutation transposition changes at most four incidences. A root-label change affects at most its own `D` slot indicators and `D` incident partner indicators. The Doob exposure coupling gives a uniform subgaussian table tail. An internal self-partner has probability `(d_ii-1)/(n_i d_ii-1)` and produces only bounded total mean bias, so this concentration is centered within `O(1)` of the independent mean. Integrating the cubic likelihood ratio in a sufficiently small fixed neighborhood is valid; the logarithmic central window alone is not being used to discard the larger annulus. The resulting full-uniform contribution has finite limsup bounded by the product lattice index.

## 4. Boundary certificate and dependence control

The quotient maps are well-defined because every root subspace maps into the relevant output subspace. Active quotient maps are isomorphisms; the proof explicitly allows inactive quotient kernels.

The support certificate selects all active support incidences. An outside vertex with exactly one active incidence has a nonzero term in its zero-root equation, forcing some further nonzero inactive support term. Adding one such edge at that same outside vertex introduces no new vertex. All selected outside vertices have at least two selected support incidences, while every support vertex retains at least three selected physical incidences. Consequently `E-(s+t)>=s/2`, including loops and multiplicities.

Uniform conditional forcing is correct: the cross image swap has exactly `m` preimages; the internal two-edge forcing has `m-1` preimages. Earlier prescribed pairs remain fixed. A certificate of `E` pairs therefore changes at most `4E` equation rows under an exact coupling to its conditional law. Rank comparison for the fixed rectangular restricted operator gives the stated kernel charge `p^(4 r_out E)`. This is the necessary control of the certificate/kernel correlation.

Enumeration does count the selected inactive support stubs using `2^(Ds)`. No unselected-edge absence event or saturation assumption is introduced. Each original solution has a selected certificate; dropping its selection rule and the rest of its quotient equations in an upper bound is legitimate. The labels outside the chosen support are zero, and the number of nonzero support labels is bounded by the stated fixed exponential factor.

The probability bound `(C/n)^E` applies throughout the chosen range because all present factor pools have linear size and at most `Ds` pairs are forced. The factorial count, degree excess, and geometric ratio estimate give `B^s(s/n)^(s/2)`. The sum starts at `s=1`, so the multigraph support-one case is included. Zero-defect fibers and nonempty quotient fibers have size at most or exactly the restricted kernel count, respectively; ambient affine representatives need not solve the original equations.

## 5. Full induction, compact cover, and fixed powers

Near a proper phase, the root-coset mass outside that phase is below the fixed boundary threshold, and the boundary estimate controls the whole such region by the restricted expected kernel. This is an open neighborhood in the relative feasible-profile topology after taking a strict threshold. Near the full phase, sufficiently close star laws have their full physical tables in the central neighborhood. Thus one may choose open neighborhoods wholly inside the proved estimates. There are finitely many zero phases. Their complement in the compact feasible-profile set has strictly negative maximum entropy and contributes only a polynomial times an exponentially decaying factor.

This proves a finite limsup by induction. Each finite smaller admissible size has finite solution count, so a supremum follows. Maximization over the finite set of maps on fixed finite spaces is legitimate. Direct sums preserve all channel and certificate hypotheses, proving all fixed powers of the solution count.

## 6. Optional simple-factor conclusion

The master's direct conditioning assertion is valid for these fixed-degree factors. For completeness, an internal degree-`d` pool has asymptotic mean `(d-1)/2` for loops and `(d-1)^2/4` for unordered parallel-edge pairs, totaling `(d^2-1)/4`. A cross factor with degrees `b,c` has asymptotic parallel-pair mean `(b-1)(c-1)/2`. The factorial moments of finitely many disjoint bad patterns converge to the corresponding powers of these means. Overlapping distinct patterns have strictly more prescribed edges than free physical vertices in their connected union and contribute `o(1)`. Bonferroni truncation of the factorial-moment inclusion-exclusion series then gives the positive zero-bad-event limit. Factors are independent, so their joint simplicity probability stays bounded away from zero.

Each simple internal graph has the same labeled-stub representation count `(d!)^(n_i)`. Each simple cross graph has `(d_ij!)^(n_i)(d_ji!)^(n_j)`. Thus factorwise simple projection is exactly uniform. Conditioning an unconditional expected count costs at most the reciprocal of the simplicity probability, rather than requiring contiguity for an unbounded observable. Matching factors and absent factors cause no extra size constraint; conclusions are restricted to sizes where all required simple factors exist.

## Limits of the verdict

This full audit establishes the stated mathematical moment chain at the exact hashes above. The expected near-quadratic algorithm is only a possible composition with separately proved structural and certified linear-algebra inputs; those are explicitly outside the master theorem's proved scope and outside this audit. A newly compiled integrated TeX artifact needs its own source-bound read to inherit this verdict.

## Final master refresh

The final master `bounded-channel-moment-theorem.md` was reread at SHA256 `9248cfd3b1791d8276d80e4b16de5bfdb49ca9eea662a016086747eac85320bf`. Its only change from the audited master hash above makes explicit that one chooses strict smaller open neighborhoods inside the proved central and boundary bounds before taking the compact complement. This matches Section 5 of this audit and makes no mathematical change to its hypotheses, estimates, or conclusion. All three proof modules retain the exact hashes listed above. **The full-chain PASS is refreshed to this final master hash.** The separate whole-source TeX audit is `audit-tex-zero.md`.
