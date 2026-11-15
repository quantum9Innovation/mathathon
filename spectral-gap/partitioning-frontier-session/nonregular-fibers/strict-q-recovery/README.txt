FULL STRICT-WEIGHT BLIND FRAME RECOVERY -- 2026-11-15
==================================================

The full theorem is proved, including the algorithm
---------------------------------------------------
Fix supplied bounds K,D. The true UNKNOWN connected reversible integer
frame Q has k<=K old types, total degrees d_i<=D, and positive block
sizes satisfying edge balance and internal parity. Sample all regular
internal and biregular cross factors independently and uniformly simple.
Internal degrees may be zero or one, and total degrees may differ.

Assume the true frame admits symmetric physical-slot weights
  q_ij=q_ji,   0<q_ij<1/2 on EVERY active factor,
  sum_j d_ij*q_ij=1 for EVERY old type i.
For an internal factor the same slot weight q_ii is used. Strictness
forces every total degree d_i>=3. Neither the frame, its class count,
its block sizes nor its omission certificate is given to the algorithm.

With high probability, EVERY equitable partition with at most K nonempty
classes is a compatible coarsening of the planted partition. Hence the
planted partition is the unique finest partition in that bounded family.
An exact algorithm given only (A,K,D) recovers the partition, k and Q up
to class permutation. Its expected bit work is polynomial UNCONDITIONALLY,
including graphs with rare large binary kernels. A deterministic cap
returns explicit abstention and gives worst-case polynomial bit work.

The all-n-singleton partition is outside the bounded family as n grows.
This theorem makes no boundary-q, all-minimum-degree-three, growing-K,
eigenvalue-simplicity, noise-robustness or practical-runtime assertion.
The earlier K3,12 nonidentifiability counterexample remains outside this
strict class. No historical firstness claim is made.

Actual assembled source and gate
--------------------------------
  strict-q-blind-frame-recovery.tex / .pdf                 8 pages
  SHA256:
  0042ca4067451330f955c9621bc741694369f4743ee4823c70f16f6a87d4c634

This is a standalone full proof: exact configuration count, weighted
entropy, explicit real one-hot gap, simplicity, mixed-degree supports,
integer near-point closure, maximal-class algorithm and bit accounting.
All three child reviewers read its ENTIRE final source and report PASS:
  entropy-audit/ASSEMBLED_FULL_PROOF_AUDIT.md
  support-audit/FULL-STRICT-Q-RECOVERY-AUDIT.txt
  algorithm-audit/ASSEMBLED_ACTUAL_SOURCE_AUDIT.txt

strict-q-recovery-proof-packet.pdf concatenates the eight-page assembled
proof and three detailed independent components (25 pages total).
The concatenation is for review, not a claim of four independent theorems.

Quantitative replacement for the compactness step
-------------------------------------------------
Put q_min=min q_ij>0, c_min=min(1-2q_ij)>0 and
  C_kappa=max(1/q_min, 2(D-1)/c_min).
For every compatible legal real one-hot star collection,
  delta=sum_i alpha_i*(1-max_label rho_i(label))
is its exact minimum normalized disagreement from an old-type point map.
The full proof establishes

  Phi <= -gamma_Q*delta^2,
  gamma_Q=9/[2 D^5 C_kappa] > 0.

The bound has no lower mass assumption for candidate classes, no
distinct-row or nonsingularity assumption on candidate R, and no alpha_min
in its constant. Unused labels and all boundary faces remain included.
This directly supplies the compactness conclusion for delta>=eta.

The weighted identity controls the GLOBAL sum of retained-law divergences:
  sum_i alpha_i sum_t kappa_it <= C_kappa*(-Phi).
The variance lower bound, using mixed degrees and reversibility, is
  sum_i alpha_i(d_i-2)sum_s V_is >= 3*delta.
Pinsker and weighted Cauchy--Schwarz give the stated quadratic gap.

How the rest of the proof closes
--------------------------------
Typed small-support counting uses only d_min>=3, D and a lower bound on
the true old proportions. For a bad row set S with outside neighbor set
W, a internal edges and b outside edges,
  2a+b=sum_(v in S) deg(v)>=d_min*|S|,   b>=2|W|,
so with e=a+b,
  e-|S|-|W| >= (d_min-2)|S|/2.
The witness count gives a SINGLE graph event of failure probability
O_(K,D)(n^(-(d_min-2))) excluding every small AV=VR, simultaneously over
all fields, matrix widths and R. Its simple-graph singleton case and
zero/internal-one/cross-degree-one factors are handled explicitly.

For any integer one-hot candidate close to JT, a clean closed
neighborhood in every old class proves QT=TR over the INTEGERS.
Then V=Y-JT satisfies AV=VR, and the support event forces V=0.
The entropy gap excludes all other candidates macroscopically. A finite
union covers every candidate quotient, including disconnected candidates.

Algorithm and exact costs
--------------------------
Enumerate all r<=K and nonnegative integer r-by-r R with row sums<=D.
For each R compute the binary kernel of I_r tensor A-R^T tensor I_n;
enumerate all its vectors. Accept only integer one-hot matrices with
nonempty classes and the original integer identity AY=YR. After complete
enumeration select a partition with MAXIMAL r. The planted pair is always
included. On the structural event every accepted map is a coarsening,
so this maximum is k and its old-type map is a permutation.

The true-frame certificate is used only in the proof. Candidate R need
not have a certificate. The binary moment applies to EVERY candidate R:
  E_simple 2^(h_R) <= C(K,D)*(n+1)^B,
  F=K+[K(K+3)/2]*2^(2K),   B=K*2^(KD)+F.
This includes the rare graphs and is not conditioned on recovery.

Untruncated base expected bit work is O_(K,D)(n^(B+2)); the conservative
bound O_(K,D)(n^(B+3)) holds as well. Space is O_K(n^2) bits.
Stop after n^(B+4) BASE bit operations. Its O(log n)-bit clock gives
actual deterministic work O_(K,D)(n^(B+5)); interruption probability is
O_(K,D)(n^-2). Return FAILURE/ABSTENTION on interruption, never a partial
maximum. The exponent is theoretical and very large.

A corrected bookkeeping detail is recorded in the algorithm audit:
an OPTIONAL UNCAPPED clock may need O(n), not O(log n), counter bits on
rare exponential enumerations. The assembled proof clocks only its capped
version and never uses the erroneous uncapped-logarithmic estimate.

The structural and capped-recovery failure bound is
  O_(K,D)(n^(-(d_min-2))+n^-2)
      + C(K,D)*(n+1)^B*exp(-gamma_Q*eta^2*n).
Connectedness fixes positive old proportions. Since K,D are fixed, the
qualifying true frames form a finite family; certificate margins and
eventual thresholds may therefore be uniform over that family.

Concrete nonregular, no-internal example
----------------------------------------
For K5 minus one edge, its two endpoints have degree 3 and its other
vertices degree 4. Set q=1/3 on cross-group edges and q=1/6 on edges
among the latter three vertices. Every vertex sum is one and all
weights are strictly below 1/2. Thus the full blind theorem applies to
its independent matching N-lifts, for every positive N. This lies beyond
both the row-regular case and an internal-degree-at-least-two requirement.

check_strict_nonregular_law.py supplies a separate finite-law check:
twelve legal stars per old type, exact matching reversal, degree pattern
(3,3,4,4,4), exact strict weights, delta=3/5, C_kappa=18, gamma_Q=1/4096.
Direct normalized entropy -0.7402603948 agrees with the weighted identity.
Appending an unused sixth candidate label preserves the integer laws.
This is corroboration, not an implementation or timing benchmark.

Supporting proofs, all actual sources
--------------------------------------
entropy-audit/strict-weight-entropy-gap.tex / .pdf           8 pages
  Explicit gap, zero phase, boundary compactness, macro/modular counts,
  finite-frame uniformity. Source SHA256:
  3ad4038397fc6469344b29c0e96922dc17ab41deec48783ce0084c75748f5320
support-audit/mixed-degree-small-support.tex / .pdf         5 pages
  Exact witness count, conditioning, simultaneous small-support event,
  integer clean-vertex closure. Source SHA256:
  b0c449292c23e63e09cdb958ba24430cd594acf1533f9882c12999f6197bd017
algorithm-audit/strict-q-algorithm-composition.tex / .pdf    4 pages
  Independent full composition and corrected clock proof. Source SHA256:
  d3f84c37fea2a44bb798de9935c2fbd317714186c96735ed2e0f46bad11d275f

PROOF-AUDIT.txt maps all source-bound reviews. build.sh rebuilds the PDFs.
SHA256SUMS.txt covers this NEW subdirectory only. All preceding packets
and their manifests remain frozen unchanged.
