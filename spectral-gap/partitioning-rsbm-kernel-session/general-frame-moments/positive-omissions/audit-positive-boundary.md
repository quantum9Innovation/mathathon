# Fresh full-source audit: positive-omission bounded moments

Completed 2026-11-15 by the boundary/phase worker. I freshly read the **entire actual master** `positive-omission-theorem.md`, the **entire actual** `central-positive.md`, and the **entire actual** `boundary-positive.md` at the hashes below. I did not edit these files or any frozen predecessor. The central proof was inspected directly, not inferred from the previously regular theorem or a delegated summary.

## Audited versions

```
424c281a4f93713b3dfe31f6145f5bde3e38cbb21d19b477d5dd100b5eb11861  positive-omission-theorem.md
489062a3cb600d2c5d7b3c66dde9300357f53391152868f2bbdee4f8d2380985  central-positive.md
269803d130d344465235060cf5359875b6cbcb00d9763e15cf0f54dfd51075d2  boundary-positive.md
```

The hashes were checked before and after the full reads and agreed. This verdict applies to these versions; later source changes require checking the changed version.

## Verdict

**PASS: no mathematical gap found in the core bounded-moment proof or its stated composition scope.** The result is valid for fixed connected reversible integer frames satisfying the symmetric unit-row certificate with **every active omission strictly positive and strictly below one half**. It permits mixed total degrees, internal degrees zero or one, arbitrary fixed characteristic and target matrix, unequal fixed old populations, repeated slots, and all admissible size residues. The proof does not establish the same bounded moment for an active zero omission, a half-weight boundary, all minimum-degree-three frames, or growing parameters.

The expected near-quadratic recovery conclusion correctly composes this new moment with the separately supplied certified right-kernel primitive and the frozen strict-weight structural theorem. It is not claimed from the moment alone. The source-specific final chain-audit file referenced by the master was still being produced at the time of this read; its absence then is a documentation timing item, not an unproved step in the mathematical composition checked below.

This is a mathematical audit, not formal proof-assistant verification or a historical novelty determination. The optional scalar-positive sharpening is outside this core audit.

## 1. Positive weighted entropy and complete phases

The exact factorial count is the same count for labeled internal pairings and cross bijections with local slot length `d_i`. The star multinomials already assign the roots. The entropy exponent has the correct internal half factor and fixed class-size weights. Uniform Stirling errors and the number of types are polynomial at every fixed finite alphabet; no entry-positivity assumption is made when using this global count.

Within-target-slot symmetrization preserves legal sums and pooled tables and raises entropy. A zero of the unsymmetrized exponent must have zero symmetrization loss by strict Shannon concavity. The weighted omission chain rule uses `sum_s theta_is=1` and gives the local root coefficient `2-d_i`. Pooling reversals yields `1-2theta_ij` on each edge entropy, including the internal factor. The unit-row identity cancels every root entropy, so the weighted loss in master equation (1) is exact.

Both strict inequalities in (P) are used at the correct places: `1-2theta_ij>0` forces every pair mutual information to vanish; `theta_it>0` forces **every** physical omission total correlation to vanish. The proof does not silently replace the second statement by positivity on only selected factors. Condition (P) also implies `d_i>=3`, since at most two slot weights below one half cannot sum to one.

The finite-group lemma remains valid with the local length `d_i`: conditioning the other `d_i-2` variables preserves the two one-coordinate marginals, and variation of a third support coordinate produces the required translation invariance. Root-neighbor independence makes these neighbor laws root-independent. Every old type is seen as a neighbor, so every root marginal is a full affine-coset law. The subspaces agree along old even walks. An internal factor is an old-type self-incidence, even though the final simple graph has no physical loops. Thus the nonbipartite common-subspace and bipartite two-subspace classifications are complete and finite.

The inclusion and quotient equations use the actual multiplicities `d_ij`; they need no invertibility of `d_i`, a multiplicity, or the target map in the field. The sum of independently variable copies of a subspace is that subspace, even when its numerical multiplicity is zero modulo the characteristic. All proper restrictions remain in the same map class and strictly reduce the common dimension or total side dimension.

## 2. The new bipartite normalizer identity

This was checked as a new mixed-degree step rather than inherited from regularity. With no internal factor on a bipartite support,

```
sum_L n_i = sum_(i in L,j in R) n_i d_ij theta_ij
          = sum_(j in R,i in L) n_j d_ji theta_ji
          = sum_R n_j.
```

The middle equality uses reversibility and weight symmetry; the end equalities use the respective unit omission rows. This is equality of **raw total physical populations**, not merely edge or degree-weighted populations. It depends only on the frame and certificate and therefore survives arbitrary subspace restrictions and unequal side-alphabet dimensions.

For the central star laws, the exact normalizer is initially `prod_i(|V_i|/|U_i|)^(n_i)`. It equals one in the common-alphabet class, and in the two-space class it equals `(u/v)^(n_L-n_R)=1` by the identity above. Neither source drops this potentially exponential factor without proof. This is also why the unequal-side bipartite obstruction is correctly excluded by (P).

## 3. Actual mixed-degree central proof

The full physical-slot tables retain repeated-slot fluctuations. Conditional on the root, any two legal neighbor labels are independent uniform because each local degree is at least three. Thus the legal and unrestricted table means and positive real covariance agree, with local covariance `(|V_i||U_i|)^(-1)[Id+(d_i-1)Pi_row]`. Varying local degrees changes the constants and dimensions but not this equality. Zero-dimensional modes are explicitly omitted.

The legal maximal-lattice index remains `|U_i|^(|V_i|)` at each old type. The proof identifies **all** character periods using three slots and an additive Cauchy equation. An individual congruence can be varied by a within-row slot transfer, so no omitted finite period is being assumed away. Legal affine lattices are contained in unrestricted affine lattices; incompatible pooled arrays get zero weight rather than an invented residue restriction.

The tilted local estimate is a relative estimate on a fixed compact mean neighborhood. Positive covariance, a uniformly positive finite tilted support, maximal-lattice aperiodicity, and Fourier inversion justify its exact covolume/determinant prefactor and uniform remainder. Since means and covariance agree, the two analytic rate functions agree through second order and their difference is cubic. Applying this separately at fixed positive type sizes and multiplying gives the stated full-table comparison. The logarithmic-window ratio tends to the actual lattice index.

The normalized weighted unrestricted law is exactly configuration plus iid root labels. Stub-permutation transpositions affect at most four incidences, while one root-label change affects at most `2Dmax`; their `O(N)` exposure martingale has bounded increments. The internal-loop mean correction is only `O(1)` per table and is correctly separated from the independent-star center. Its subgaussian concentration integrates the cubic likelihood ratio on the surrounding fixed neighborhood, with no polynomial loss. This proves a bounded full-uniform contribution for the whole enlarged induction class, including unequal and zero-dimensional parity alphabets.

## 4. Sparse certificate constants and the closed induction

Quotienting by a proper phase and subtracting its old-type quotient point map is legitimate on every configuration, because every physical row has its exact prescribed incidence counts. A fixed quotient assignment has an empty affine fiber or an affine translate of the restricted homogeneous kernel. Exact representatives before quotienting are not presumed.

The mixed-degree certificate uses

```
2i+j=sum_(v in S)deg(v)>=dmin |S|,
ell<=j/2,
E<=Dmax |S|,
E-(|S|+ell)>=(dmin-2)|S|/2.
```

All quantities count incidences and edges with their proper multiplicities. A loop is one certificate edge and two degree incidences. The certificate includes every support stub, so no absent-edge conditioning is hidden. Support-one configurations remain in the sum.

The internal forcing switch has exactly `m-1` preimages of each allowed output; the cross swap likewise has a constant preimage count. They preserve all earlier prescribed stub pairs and give the exact graph law conditional on the whole certificate after at most `E` switches. At most `4E` physical rows change, so the restricted operator's rank comparison bounds the **conditional** kernel moment by `p^(4r_*E) M_H`. This is valid for rectangular two-space operators and controls the rare-certificate/kernel correlation.

The actual remaining pool denominators are `Theta(n)` when the support fraction is chosen using the smallest positive pool coefficient and `Dmax`. Vertex placements, quotient values, exterior stub choices, selected-stub pairings, and the rank charge all appear in the support count. The powers reduce to `(s/n)^(beta s)` with `beta=(dmin-2)/2>0`, while remaining factors are exponential in `s` only. The displayed conservative `B` and epsilon make the support sum geometric from `s=1`, giving `O(n^-beta)M_H`. No equal total degree is used.

The same frame and positive omission certificate remain after restriction, and the bipartite population equality remains exact. Thus every proper phase calls a strictly lower-dimensional instance of the same central/boundary class. The zero-dimensional system has one assignment. The finite family of proper phases, the central neighborhood, and the compact negative-entropy complement close the bounded-moment induction. Finitely many maps and finitely many smaller admissible sizes justify the supremum and uniformity in target matrices.

Direct simplicity conditioning is the correct transfer for an unbounded moment: the finite product of fixed-factor simplicity probabilities stays bounded below; constant labeled-stub multiplicities give exactly the product of uniform simple factors. No extra parity condition is introduced for absent internal factors or cross matchings, and conditional claims explicitly require the simple factors to exist.

## 5. Expected blind-recovery composition and scope

The master uses the actual column-vectorized right-kernel operator `I_r tensor A-R^T tensor I_n`; the transpose is correct for nonsymmetric quotients. Bounded quotient order and graph degree make this an `O(n)`-sparse operator of order `O(n)` with its transpose available. The already certified per-input primitive applies via symmetric linearization, computes a complete basis, and projects to the **right** kernel before enumeration. Its per-input charge is `soft-O(n^2(h_R+1))`; it does not require an exponential moment for the doubled left-plus-right kernel.

Odometer updates generate the right kernel in `O(n p^(h_R))` total operations at fixed parameters, rather than charging `h_R` for every vector. This distinction is necessary: a first exponential moment need not control `E[h_R p^(h_R)]`. Exact one-hot, nonemptiness, and original integer checks remove all false modular candidates. Prescribed cell sizes are not required for these checks.

The new raw moment gives both `E p^(h_R)=O(1)` and `E(h_R+1)=O(1)` at each fixed candidate, including rare large kernels. Averaging the fully charged per-input bounds is therefore legitimate without conditioning on structural success. The finite integer candidate family costs only a fixed factor. The frozen strict-weight structural theorem has the same every-active-positive certificate hypothesis, allows internal degrees zero or one and varying totals, and says every bounded-class equitable partition is a planted coarsening. The true partition is among the candidates; a largest accepted nonempty class count therefore returns it up to names on that event. The runtime is an unconditional expectation, and the recovery guarantee is high probability; these are correctly distinguished.

For this composition check I read the actual frozen per-input theorem statement and the entire nonsymmetric intertwiner extension plus its independent audit, at:

```
bb6ec1086a2d46f4a1d0b66c69aadc2d120b07157ba8e95f3c08ffb187843473  certified-full-kernel.tex
cb893b0def524ba101a4419adf922f0dec60ad3156348c8e91d600887e743df9  intertwiner-extension.txt
b538cdc887287c97153f60a05d10ef4f6171915500cb6f83d4567afc167b9026  intertwiner-independent.txt
```

These are supplied algebraic inputs, not newly proved primitives in the positive-omission packet. The master accurately states that dependency. The strict-weight structural source is likewise an identified frozen input, not a consequence of the finite-field bounded moment alone.

## 6. Examples and exclusions

- For common degree `d>=3`, every active weight `1/d` is positive, below one half, and has unit row.
- For connected `k>=2` with all internal degrees `h_i>=2`, `b_i>0`. With `epsilon=1/(4D)`, active cross weights are positive and below one half; `epsilon b_i<1/4`; hence `(1-epsilon b_i)/h_i` is positive and is strictly below one half, including `h_i=2` because `b_i>0`. The weighted row is exactly one.
- The `K5`-minus-an-edge certificate gives `3(1/3)=1` at each degree-three endpoint and `2(1/3)+2(1/6)=1` at each degree-four vertex. All its factors are matchings between distinct old fibers, so they are simple already.
- A `K_(3,12)` lift has a rectangular bipartite block of dimensions `3N` and `12N`; its full adjacency rank is at most `6N` over every field, so nullity is at least `9N`. Its raw scalar zero moment is exponential. It cannot satisfy the symmetric unit-row certificate because the derived raw population equality would say `3N=12N`. The master uses this as an exclusion, not a purported positive example.

The proof and master consistently exclude active zero omission weights and weights one half. The more heterogeneous phases beyond that boundary are not invoked anywhere in the induction. No growing-frame, growing-field, arbitrary deterministic-factor, or noisy-factor conclusion is present.
