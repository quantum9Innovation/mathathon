# Full-chain audit of positive-omission frame moments

Independent source audit, November 15, 2026. This file is confined to the newly authorized positive-omissions directory. The parent regular-frame packet and the frontier/algorithm packets were read only.

**Verdict: PASS.** The actual master and its actual central and boundary proofs establish bounded raw intertwiner moments for the stated fixed mixed-degree frames. Their composition with the frozen strict-weight structural theorem and the certified sparse right-kernel primitive gives unconditional expected soft-O(n^2) blind recovery. The additional scalar note also passes its separate, nonbipartite and odd-prime audit. The conclusions below are bound to the source hashes in the final section.

This is an audit of mathematical validity and composition. It certifies no historical novelty, effective failure rate, growing-prime estimate, zero-active-weight extension, or theorem for every frame of minimum degree three.

## 1. Statement and model actually checked

The frame is a fixed connected nonnegative integer matrix D=(d_ij), with fixed positive integer multipliers a_i and a_i d_ij=a_j d_ji. Type i has n_i=a_i N vertices. Internal stubs are uniformly paired, cross stubs are uniformly bijected, independently between factors. Every internal pool must have even size. An internal loop contributes two adjacency incidences. All statements concern admissible scales; the conditioned statement further requires that the simple factors exist.

The hypothesis is a symmetric weight on **every active factor**, including internal factors:

    0<theta_ij=theta_ji<1/2,     sum_j d_ij theta_ij=1.

It forces every local degree d_i>=3. The field, target dimension, number of types, frame and positive size proportions are fixed. Under these hypotheses the main result is

    sup_N E #{Y: A_N Y=YR}<infinity

for every fixed prime and target dimension, uniformly over the finite family of target matrices R. The proof also treats type-dependent linear maps and two different side alphabets, which are necessary to close the induction. No invertibility of R or of any degree, size multiplier, or old-frame matrix modulo the field characteristic is assumed.

Direct conditioning transfers the raw moment to the independent uniform simple-factor law. Neither the theorem nor the recovery algorithm substitutes qualitative contiguity for this conditioning calculation.

## 2. Exact count and entropy equality

The physical slots are retained throughout. The profile multinomial assigns the roots exactly once. Cross weights are the pooled factorial probabilities of the prescribed stub bijection; internal weights are the pooled double-factorial probabilities, with symmetric tables and even diagonal. Thus loops, repeated slots and internal parities are included in the exact count. Fixed alphabet and degrees give polynomially many profiles and a uniform O(log(N+1)) Stirling error, including profiles with zero entries.

Slot symmetrization is only within a common old target type. It preserves the legal sum and pooled tables, and increases star entropy. Strict concavity ensures that an unsymmetrized zero is already symmetric. At a symmetric star, average the lossless omitted-slot chain rule with the physical-slot weights theta. Reversibility and the weighted unit rows cancel every root entropy even when the d_i differ. The resulting identity is

    Phi = -sum_(i<j) a_i d_ij(1-2theta_ij) I_ij
          -sum_i (a_i d_ii/2)(1-2theta_ii) I_ii
          -sum_i a_i sum_s theta_i,s J_i,s.

All displayed coefficients are positive. Consequently every pair mutual information and every physical omitted-slot total correlation vanishes at zero. This is stronger than merely proving Phi<=0; the equality conditions are what support the finite phase classification. They would not follow from this argument if an active theta were zero.

With d_i>=3, the finite-group reflection/translation argument applies to every omitted-slot product law. It forces uniform affine-coset marginals with a common difference space among all neighbors of a given old type. Compatibility identifies these with the neighboring root marginals. The root subspaces therefore agree along even walks. Connected nonbipartite support has one common subspace; connected bipartite support has one per side. An internal factor supplies an odd self-incidence. Repeated physical slots do not supply additional parity components.

For each allowed set of affine cosets the star law is uniquely uniform on the legal affine support. The permitted map inclusions and quotient coset equations are exactly those in the master. There are finitely many phases at fixed dimensions. Every proper phase lowers the common dimension, or the sum of the two side dimensions. Thus the stated induction class is closed, including unequal side dimensions and zero-dimensional sides. No bounded moment is inferred from entropy alone.

## 3. Mixed-degree central proof

I checked the complete actual central-positive.md, including its exact normalizer rather than replacing local d_i by a common degree.

Let V_i be the root alphabet and U_i its common neighbor alphabet. Uniform legal stars have |V_i||U_i|^(d_i-1) possibilities. With

    K_N=prod_i [|V_i||U_i|^(d_i-1)]^n_i,

the exact two identities are E Z=K_N E_P W and

    K_N E_Q W=prod_i (|V_i|/|U_i|)^n_i.

The second product is one in the common-alphabet case. In the bipartite two-space induction it is (u/v)^(n_L-n_R), so **equality of physical side populations is necessary** here. It follows exactly from the certificate:

    sum_L n_i = sum_(i in L,j in R) n_i d_ij theta_ij
              = sum_(j in R,i in L) n_j d_ji theta_ji = sum_R n_j.

This calculation does not require equal local degrees or equal individual type sizes. It remains valid after restriction to any pair of side subspaces. Together with ordinary stub balance it gives K_N=(uv)^E, with E the total number of cross edges. The normalized weighted reference law is therefore exactly configuration followed by independent uniform physical-vertex labels in both induction classes.

At type i the common-root-row real space has covariance

    Sigma_i=(|V_i||U_i|)^(-1)[Id+(d_i-1)Pi_row,i]

under both legal and unrestricted laws. Root-row and centered-row eigenvalues are respectively d_i/(|V_i||U_i|) and 1/(|V_i||U_i|), so the covariance is positive on the declared space. Pairwise conditional independence uses d_i>=3. The local index calculation by three-slot circle-valued characters gives the complete maximal legal lattice index |U_i|^|V_i|. It includes the affine lattice periods rather than only necessary congruences; singular on-site maps and characteristics dividing local degrees cause no gap.

The fixed-neighborhood inverse-mean tilt, positive covariance and maximal-lattice Fourier inversion establish the actual uniform relative local limit estimate, including eventual positive mass at the relevant central lattice points. The P and Q means and covariances agree; the difference of their rate functions is cubic. Thus the pointwise ratio is bounded by C I exp(C||Delta||^3/N^2) on a small fixed neighborhood and equals I(1+o(1)) in the sqrt(N)log N window.

Under the exact weighted Q law, the exposure martingale has O(N) increments bounded by constants depending on Dmax and the alphabets. Stub-permutation transpositions affect at most four physical incidences; one root-label change affects at most 2Dmax incidences. Pairing a uniform stub permutation consecutively handles internal factors. Internal self-loops shift the mean by only O(1). Therefore the full physical-table deviations have a genuine subgaussian tail. Choosing the fixed neighborhood small makes the cubic likelihood ratio integrable against this tail. The outer part is o(1), without a polynomial prefactor loss; the inner part is bounded using the exact reference probability normalizer. This proves a finite full-uniform contribution, not just a polynomial bound.

## 4. Proper phases and the bounded-moment induction

I checked the complete actual boundary-positive.md, including support size one and internal pairing forcing.

A quotient defect is measured after subtracting the phase's type-constant quotient point map. This quotient point map is an exact solution for every configuration. Its affine lift need not itself be a solution: a given defect has either no lift or an affine translate of the homogeneous restricted solution space. Its fiber cardinality is therefore at most Z_H(G), with no unjustified choice of a global exact coset representative.

For a support of s vertices, let i count internal support edges (loops once), j boundary edges and u reached exterior vertices. Every exterior zero vertex has at least two incident support stubs, counted with multiplicity. Consequently, with beta=(dmin-2)/2>0,

    2i+j>=dmin s,   u<=j/2,   E=i+j<=Dmax s,
    E-(s+u)>=beta s.

These facts permit parallel edges and loops and do not require equal vertex degrees.

The prescribed cross-edge switching gives the exact conditional uniform bijection. For an internal pairing with m free stubs, forcing one given pair has exactly m-1 preimages: the already-present pair and two reconnections for each other pair. This preserves the earlier forced pairs. Each forced edge needs at most one switch and changes at most four physical rows. The resulting rank comparison bounds the conditional lower-space kernel count by p^(4r_*E) times its unconditional expectation. This charge controls the dependence between the rare support certificate and the bulk kernel.

Every active stub pool has size at least a fixed positive multiple of N. For s<=epsilon N the probability of a prescribed valid E-edge certificate is at most (C/N)^E. The support/exterior placements, support values, exterior-stub selections and pairings give

    E #{solutions with s defects}
      <=M_H(N) Dmax s B^s (s/N)^(beta s).

The powers follow from E-(s+u)>=beta s, s^s/s!<=e^s, and the sum of s^u/u! bounded by e^s. The explicit B and epsilon in the actual boundary source are sufficient; Dmax controls the upper counts and dmin supplies the positive exponent. The series begins at s=1 in the configuration law and sums to O(N^-beta) M_H(N). The singleton term has not been discarded by borrowing the separate simple-graph support lemma.

The smaller-dimensional moments are bounded by induction. The finitely many proper-phase root neighborhoods and the central full-uniform neighborhood cover every entropy zero. Their compact feasible complement has strictly negative continuous entropy, and its exact count is poly(N)exp(-cN). This supplies the missing noncentral estimate. Together these are a complete moment proof; the entropy identity by itself would not suffice.

Every fixed internal or cross factor has simplicity probability bounded below along large admissible scales. Simple factors have constant labeled-stub multiplicity, and the finite product of probabilities remains positive. Direct division by this probability transfers the raw moment to precisely the independent uniform simple factors. The finitely many smaller valid sizes are harmless. Degree-zero factors are omitted; fixed factors of degree one cause no exception.

## 5. Structural theorem and charged blind-recovery composition

The full frozen strict-q-blind-frame-recovery.tex was read. Its hypotheses include the present positive certificate, variable total degrees, and internal degrees zero or one. Its weighted identity, quantitative real one-hot entropy gap, and mixed-degree small-support lemma are independently consistent with the present model. The clean unchanged vertex in every old class gives the **integer** equation DT=TR. No lower bound on candidate class masses, distinct candidate rows, nonsingular target, known proportions or known frame is required.

The structural small-support result is for the simple graph and begins at support size two. The moment boundary above is for the configuration law and begins at one. The arguments use these different starts correctly. On the structural event every nonempty equitable partition into at most fixed K cells is a compatible planted coarsening.

The actual frozen certified-full-kernel.tex gives, for every fixed sparse symmetric matrix M over a fixed odd prime field, expected bit work

    soft-O(m(w+m)(h+1))

to compute its complete base-field kernel, where m is its dimension, w its number of nonzeros and h its corank. The proof charges verified extension-field construction, fixed-small-characteristic diagonal preconditioning, shifted-sequence Berlekamp--Massey, capped bad trials, all independent probes, canonical Frobenius descent and verification. Its deterministic lower-rank certificate and verified independent nullvectors cover every unlucky random choice and every exceptional input. The expected bound is per input; it does not assume a typical small corank. The classical preconditioning results cited in that frozen primitive remain explicit external inputs.

The complete frozen intertwiner-extension.txt was re-read. Column vectorization gives

    K_R=I_r tensor A-R^T tensor I_n.

The transpose on R is essential. This operator has O(n) dimension and nonzeros at fixed r,Dmax. For S=[[0,K_R],[K_R^T,0]], corank(S)=2h_R. The certified symmetric primitive therefore costs soft-O(n^2(h_R+1)) per input. The lower-coordinate projections of its complete kernel span the complete **right** kernel of K_R; selecting and canonicalizing those projections costs O(nh_R^2+h_R^3), within the same bound. No unweighted Gram-kernel identity is used.

Enumerating this right kernel by a base-p odometer requires O_p(p^h_R) total digit changes, each an O(n) vector update. Exact nonempty one-hot checks and the original integer AY=YR check take O(n) per candidate. Enumeration thus costs soft-O(n p^h_R), without a hidden h_R multiplier. A single bounded moment E p^h_R controls both this cost and E(h_R+1). The complete all-fixed-target theorem also bounds higher fixed powers through block-diagonal targets, but projection avoids needing that additional moment.

Enumerate every bounded nonnegative integer candidate R of order at most K and row sums at most D. This is a finite family; modular coincidences between candidates do not affect completeness because the final equation is checked over the integers. The true candidate is included. Selecting the largest accepted number of nonempty cells recovers the planted classes up to names on the structural event; all other accepted partitions are coarsenings. Candidate class sizes are checked for positivity, not against unavailable planted sizes.

Averaging the per-input bound over the actual simple law gives **untruncated unconditional expected soft-O(n^2) bit work**. The kernel algorithm itself always returns the verified complete list; only the statistical identification uses the high-probability structural event. The algorithm needs A,K,D and a fixed prime, not the certificate. There are finitely many connected integer true frames at fixed K,D; their reversible positive size ratios are fixed by the frame, so constants may be maximized over the qualifying finite family. No uncharged dense fallback or high-probability truncation is present.

## 6. Covered examples and genuine exclusions

For common total degree d>=3, all active weights 1/d satisfy the certificate.

For a connected frame with k>=2 and every internal degree h_i>=2, connectedness gives b_i=sum_(j!=i)d_ij>0. Set epsilon=1/(4Dmax), every active cross weight epsilon, and theta_ii=(1-epsilon b_i)/h_i. The numerator is positive. If h_i=2, b_i>0 makes the weight strictly below 1/2; if h_i>=3 the strict upper bound is immediate. The unit row equations and symmetry hold exactly. Thus every mixed-internal-degree class stated in the master is covered. This calculation does not cover the isolated one-type degree-two frame.

For K5 minus an edge, the two degree-three vertices connect only to the three degree-four vertices. Weights 1/3 on these six edges and 1/6 on the three edges among degree-four vertices give rows 3/3=1 and 2/3+2/6=1. All active weights lie strictly between zero and one half. Its independent lifts therefore supply the claimed genuinely nonregular example.

The K_(3,12) lift has physical bipartite sides 3N and 12N. Its adjacency rank is at most 6N over every field, so its nullity is at least 9N and its scalar zero moment is at least p^(9N). This independently disproves a bounded-moment theorem for all frames of minimum degree three. It cannot satisfy the certificate because the proved bipartite side-population identity would fail.

Zero active weights are outside the proof: some omission defects then have no positive coefficient, so the all-omissions affine-phase argument need not apply. Half-weight active factors likewise lose an MI coefficient. No conclusion for either boundary is inferred here.

## 7. Additional sharp scalar note

I also read and independently checked the entire actual scalar-positive.md. It is a separate **nonbipartite**, fixed **odd-prime** corollary. Its entropy equality gives exactly the full-uniform phase and p^t point phases, where t=dim_Fp ker(D-lambda I).

The exact integer compatibility subgroup K0 retains cross reversal, common physical root margins, internal symmetry and even diagonal. Fixed K0 translations preserve the logarithmic-window weighted-reference probabilities up to 1+o(1): cross pooled factorial exponents sum to zero, and the internal diagonal/off-diagonal exponent is half the total pooled shift, also zero. Relative local limits and subgaussian tails promote this to total-variation translation invariance. The actual finite quotient K0/(K0 intersect L), rather than an assumed saturated pooled real space, is therefore equidistributed.

The annihilator calculation is sound for arbitrary active multiplicities, including multiplicities divisible by p. Cross zero-margin two-by-two interactions in one physical slot of each orientation force affine annihilator functions with alternating slopes. Twice an internal symmetric interaction has even diagonal and forces its slope to zero in odd characteristic. Connected nonbipartite support kills all slopes. The remaining constants c have functional coefficients (D-lambda I)c on the free root moments.

The root moments really are free: realizing twice any integer zero-total root margins gives cross pooled margins 2d_ij r_i and 2d_ji r_j; the internal diagonal table 2d_ii r_i is symmetric and even; splitting every pool into d_ij physical tables with common row 2r_i is integral. Two is invertible modulo an odd prime. No division by a degree or size multiplier is used. Hence the image index is p^(kp-t), and the central contribution is p^t+o(1).

The direct scalar point-neighborhood count includes singleton configuration supports and uses dmin for its positive exponent and Dmax for its upper counts. It gives one plus o(1) at every point. These neighborhoods and the central neighborhood can be chosen disjoint; the compact remainder is exponentially small. Thus the exact configuration formula E|ker(A-lambda I)|=2p^t+o(1) follows.

For a fixed integer ell, a nonzero maximal minor of D-ell I selects arbitrarily large odd primes with t_p=t_R. Subtracting the deterministic old modular subspace gives a real excess-nullity limsup at most 1/(p-1). The prime is fixed during each size limit, then allowed to tend to infinity. The deterministic planted real eigenspace provides the matching lower bound. Conditioning the already vanishing real-failure event on simplicity uses a frame-dependent lower bound independent of p. This proves equality of real multiplicity with the old-frame multiplicity with high probability. It does **not** assert the exact fixed-prime moment after conditioning or a quantitative growing-prime estimate.

## 8. Source hashes binding this verdict

All files below were read in full; the actual frozen kernel primitive and its full nonsymmetric extension were additionally re-read during this extension audit. SHA256:

| Source | SHA256 |
|---|---|
| `spectral-gap/positive-omission-bounded-moment-root.txt` | `60e40385f2d4236d4279e25da3101f64d1c143ed4238ab41acda739afe5891e0` |
| `positive-omission-theorem.md` | `424c281a4f93713b3dfe31f6145f5bde3e38cbb21d19b477d5dd100b5eb11861` |
| `central-positive.md` | `489062a3cb600d2c5d7b3c66dde9300357f53391152868f2bbdee4f8d2380985` |
| `boundary-positive.md` | `269803d130d344465235060cf5359875b6cbcb00d9763e15cf0f54dfd51075d2` |
| `scalar-positive.md` | `46d5c8e9e9f7df950d16d6bab51a0010ae19fe1fff3799295579d8901f23e5a2` |
| `spectral-gap/partitioning-frontier-session/nonregular-fibers/strict-q-recovery/strict-q-blind-frame-recovery.tex` | `0042ca4067451330f955c9621bc741694369f4743ee4823c70f16f6a87d4c634` |
| `spectral-gap/partitioning-dynamic-session/rsbm-full-kernel/certified-full-kernel.tex` | `bb6ec1086a2d46f4a1d0b66c69aadc2d120b07157ba8e95f3c08ffb187843473` |
| `spectral-gap/partitioning-dynamic-session/rsbm-full-kernel/intertwiner-extension.txt` | `cb893b0def524ba101a4419adf922f0dec60ad3156348c8e91d600887e743df9` |

Unqualified file names in this table refer to the present positive-omissions directory. No source outside this directory was changed by this audit.
