# Fresh complete-source audit of the scalar regular-frame theorem

**Verdict: PASS. No mathematical gap was identified in the stated scalar theorem or its all-parameter RSBM consequence.**

Audit time: 2026-11-15, approximately 11:49 UTC. The complete actual assembly and every mathematical dependency listed below were read, not only the proposed new scalar step. The assembly hash was checked before and after the audit and remained unchanged.

The reviewer developed the central estimate and independently rederived the scalar translation and annihilator arguments. The phase/boundary source and scalar assembly were separately authored and were read afresh in full for this audit. This is a mathematical audit, not proof-assistant verification or a historical-novelty determination.

## 1. Exact audited sources

All paths below are in `spectral-gap/partitioning-rsbm-kernel-session/general-frame-moments/`.

| File | SHA-256 |
| --- | --- |
| `scalar-regular-frame-theorem.md` | `236e56d2d028835bf86b8f6c2a3f29864cdb84cb3140b248ab35143d8b19fa0c` |
| `central-frame.md` | `e64d46ae873a6ce568b76784788b1605a38e249c2f8983451372486eff0315a7` |
| `boundary-frame.md` | `cbfd5c6c8372bbbb1a4e2ef01426bfd93225e54cc7842e9efadc7802fe07f5e4` |
| `bounded-frame-moment-theorem.md` | `6c6da08c6d944e1f9cd76706f08b660fb9be82579549fbae347404e8b99e7e0b` |
| `scalar-lattice-rank.md` | `7738f0c8d2aa86f7e4aaf50ff02f2b6741885076a60625f368c593d5755cc2e2` |
| `scalar-central-equidistribution.md` | `2ca675978aa450a3db04d33d33b571bb0f455e33e006c04f2fde7227c49023e0` |

The last note records the reviewer's independent derivation. The conclusion below is tied to the actual assembled source in the first row, rather than merely to the reviewer's own version.

## 2. The audited theorem and its scope

The actual claim is an exact **configuration-model** fixed-prime scalar moment on a fixed connected nonbipartite degree frame with common degree `d>=3`:

`E |ker_Fp(A_N-lambda I)|=2p^t+o(1)`,

where `p` is odd and fixed, `t=dim_Fp ker(Q-lambda I)`, and the size limit includes every admissible scale. Repeated old-type slots, internal pairings, loops, parallel edges, and unequal fixed type sizes are explicitly retained.

The moment identity is not transported unchanged through simplicity conditioning. Instead, its upper bound first proves the real-nullity conclusion in the configuration law. A prime-independent positive probability of simplicity then transfers that high-probability event. This order is correct and avoids needing any uniform-in-prime error estimate.

## 3. Full-uniform central contribution

The exact weight is the product of pooled cross factorial ratios and pooled internal symmetric-table double-factorial ratios. Root labelings are included exactly once in the star assignments. Recording all physical slots preserves the local iid table description even when several slots have the same target type. The weight depends only on the pooled tables, which is consistent with a uniform pairing or bijection of the actual labeled stubs.

The legal and unrestricted local table laws have the same mean and covariance. Degree at least three makes any two distinct neighbor labels independent uniform conditional on the root. The resulting covariance is positive on exactly the declared common-row-margin space. The maximal legal lattice has index `p^{kp}`; the additive-character proof supplies every period rather than only necessary congruences.

The compact-tilt relative lattice estimate is valid over a fixed neighborhood of the mean. Positive covariance gives the analytic inverse mean map and a common compact tilt neighborhood. Finite support with fixed positive tilted probabilities gives a uniform characteristic-function gap away from the maximal-lattice origin and a uniform Gaussian expansion near it. Therefore every relevant affine lattice point has positive local probability for sufficiently large size, and the legal/unrestricted likelihood ratio is uniform, with cubic rate-function difference.

Under the exactly normalized weighted unrestricted law, configurations followed by iid labels give the actual full tables. Stub permutations represent internal pairings uniformly. A permutation transposition changes at most four directed incidences; a vertex-label change affects at most `2d`. Exposure martingales give a subgaussian tail at scale `sqrt(N)`. Internal loops shift the independent mean only by `O(1)` because a given internal stub has same-owner partner probability `(q_ii-1)/(n_i q_ii-1)`. Integrating the cubic likelihood ratio against this subgaussian tail is valid after shrinking the fixed neighborhood; no polynomial remainder is left.

Thus the bounded central input and logarithmic-window relative ratio used in the scalar assembly are proved with their actual prefactors.

## 4. Exact compatible-coset mass and scalar rank

The compatible direction lattice `K0` is the actual integer subgroup retaining pooled reversals, internal symmetry, and even internal diagonal. At each admissible scale the all-zero table is legal and compatible. The legal-compatible affine set is precisely one coset of `K0 intersect L` inside the unrestricted compatible affine lattice.

For fixed `z in K0`, both the unrestricted local probability ratio and the pairing-weight ratio tend uniformly to one in the logarithmic window. The internal weight calculation is correct: diagonal shifts are even, double-factorial logarithmic powers contribute half the diagonal shift, off-diagonal powers contribute the full upper-triangle shift, and their sum is half the full pool-total shift, hence zero. All physical and pooled entries stay positive of order `N` under a fixed translation.

Concentration and this uniform ratio imply asymptotic total-variation invariance under each fixed `K0` translation, after extending the finite-support measure by zero. This is enough to equidistribute the finitely many actual integer cosets. No Gaussian precision computation or mod-`p` saturation assertion is needed. The central contribution is therefore exactly `I/J+o(1)`.

The annihilator computation for `J` was checked directly:

- Cross two-by-two pooled interactions can be placed in one physical slot of each orientation. They force affine coefficient functions with alternating slopes, with no degree-multiplicity factor.
- Twice a symmetric internal zero-row interaction preserves the even diagonal and forces its coefficient function to be constant for odd `p`.
- An odd cross cycle similarly kills alternating slopes. Connectivity makes all coefficient functions constant.
- The assembly's explicit root-margin construction uses twice arbitrary integer margins. Its cross anchor tables have the required row and column margins. Its internal diagonal tables are even. Each pooled table splits into physical-slot tables with the same common root margin, including when a multiplicity is divisible by `p`.
- Multiplication by two is invertible over the odd prime field, so the necessary root moments vary independently. The residual condition is `(Q-lambda I)c=0`, with the correct orientation of `Q`, not its transpose.

Consequently the annihilator dimension is exactly `t`, `J=p^{kp-t}`, and the exact full-uniform contribution is `p^t+o(1)` for every admissible size residue.

For precision, only `K0 intersect L` is being asserted to have finite index `J` in `K0`. The compatible real span can have lower dimension than the unrestricted common-row space, so the proof does not require `K0` itself to have finite index in `L0`. The assembly's index arguments use the correct relative inclusion.

## 5. Zero phases, sparse point neighborhoods, and the complement

The entropy identity in `boundary-frame.md` was rederived. Averaging the omitted-slot conditional entropy identity over all `d` omissions gives the coefficient `-(d-2)/d` on the undirected weighted pair mutual informations and the coefficient `-1/d` on the omission total correlations. Reversibility and common degree cancel the root entropies exactly. Strict concavity handles the unsymmetrized repeated-slot laws without losing zero phases.

At zero entropy every neighbor pair law is a product and every retained neighbor tuple is a conditional product. The finite-group lemma then yields uniform affine cosets, common on even-walk components. The connected nonbipartite support, including self-incidences from internal factors, has one such component. A scalar `F_p` alphabet has only its zero and full subspaces, giving exactly the full-uniform phase and the `p^t` old-type point maps.

The sparse estimate was checked including the correlation issue. A quotient support certificate contains all support stubs, so no missing-edge conditioning is required. Exterior zero vertices need at least two incident support stubs even with parallel edges. Hence `E-V>=(d-2)s/2`. Internal forcing has exactly `m-1` preimages per permitted output; cross forcing has exactly `m`. Their composition gives the exact conditional factor law. At most four vertex rows change per switch, so the weighted kernel expectation is controlled by the stated rank factor. The certificate enumeration retains support one and sums to `O(N^{-(d-2)/2})` times the lower-dimensional homogeneous moment. At a scalar point phase that moment is exactly one.

The phase neighborhoods can be chosen disjoint and separated from the central full-table neighborhood. Distinct point maps differ on an entire positive-proportion old class. Every remaining feasible profile lies in a compact entropy region containing no zero, whose total contribution is polynomial times an exponentially small factor. Thus the point neighborhoods give `p^t+o(1)`, the central neighborhood gives `p^t+o(1)`, and the complement is `o(1)`. This proves the claimed exact configuration moment.

## 6. All-parameter uniform-simple RSBM consequence

For the two-block degree matrix `[[d1,d2],[d2,d1]]`, positive internal degree supplies a support loop and positive cross degree connects the support. At `lambda=d1-d2`, every fixed odd prime not dividing `d2` has old kernel dimension one. Hence the configuration scalar moment is `2p+o_p(1)` at every admissible block size, including `(2,1)` and odd block sizes when `d1` is even.

If real nullity is at least two, every integer minor of order `2N-1` vanishes and so the mod-`p` kernel has at least `p^2` elements. Markov's inequality gives a limiting configuration failure probability at most `2/p`. Sending fixed admissible primes to infinity proves configuration real nullity one with high probability. No exchange of a growing prime with the size limit occurs.

The event that all independent fixed-degree factors are simple has a positive limiting probability along every admissible size sequence, depending only on the degrees and not on the prime. Conditioning therefore transfers the already-proved high-probability event. The conditional factor laws are exactly the intended independent uniform simple regular and biregular graphs. The planted integer sign vector is always in the real kernel, including before conditioning, so the conclusion is exactly one-dimensionality, rather than merely nullity at most one.

The resulting conclusion needs no outlier gap and implies exact recovery by rational nullspace elimination. Its real failure probability is qualitative `o(1)`; no polynomial rate follows from the fixed-prime argument as written. The known `(2,1)` `Omega(N^-2)` switching lower bound is consistent with it.

## 7. Audit conclusion

All central, compatible-lattice, zero-phase, sparse-boundary, complement, prime-limit, and simplicity-conditioning steps required by the actual scalar assembly were checked. **PASS at the bound hashes above.** This audit does not assert a growing-prime estimate, a polynomial real simplicity rate, or historical novelty.
