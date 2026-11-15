# Independent review of the actual graph resonance synthesis

Date: November 15, 2026, America/Los_Angeles.

Decision: revision 2 is accepted as a complete paper proof at the stated scope. Finding CS-I1 is resolved by the exact revision change recorded below. No unresolved mathematical finding remains in the positive resonance, negative logarithmic splitting or separated mass conclusions. The retuned negative crossing remains explicitly outside the theorem.

## 1. Exact revisions and exposure

The full initial synthesis was read at:

- `root/graph-resonance-v1.md`, SHA256 `d7e03a19f52d7e35bc934471b731d8541af4bc9acd796d0ee0464c9fbb9aad86`.

Acceptance binds the corrected target:

- `root/graph-resonance-v2.md`, SHA256 `907d90af7ea1af8a59ec49c100869046e01e3ffd251e81a55239a054bb59f289`.

The exact file comparison shows only the revision statement and the insertion of additive plus signs before the O_P(1/m) remainders in equations (17) and (18). The missing signs were transcription defect CS-I1, also reported by the other reviewer. Revision 2 resolves it without changing the mathematical argument. Revision 1 remains preserved.

Prior exposure includes the earlier critical-law reviews, authorship of the finite resonance note, separate reviews of the new subspace and selected-resolvent proofs, and discussion of the intended resonance scales. The logarithmic probability proof was read in full as background before this assignment. Its acceptance was not presumed during this audit. The present review reconstructs the synthesis and checks the needed interface, coefficients, rates and normalization from that frozen source. A separate probability review covers its complete internal probability argument.

The dependencies used are:

| Input | SHA256 |
| --- | --- |
| root/subspaces-v1.md | f13fbd47ba04bd638f4bafe940c20d604bfa4a4653df553b4b737f2e3779e87a |
| probability/refined-resolvent-v1.md | bd00db6c2f69813d480f5a86d5d22c8b6fe4922d9cc3d233f72840dddb29f8df |
| resonance/finite-normal-form-v1.md | 59bebac4b6a96d148d48830bf27130223d6820e53e16627720fb7f2f7216eed7 |
| probability/negative-log-scale-v1.md | faced6a02d91d451e4ef0e0989d3d46811da66d809d40e9344e9444012901409 |

This is not a machine formalization or a historical-priority audit. Knowledge of the intended answer is disclosed rather than counted as an independent derivation of the finite target.

## 2. Canonical subspace lemma

The block-diagonal comparison has a spectral gap across the stated contour. Its perturbation norm is exactly the off-diagonal block norm. The resolvent identity therefore gives a dimension-independent projection estimate and rank equality for sufficiently small coupling.

For the canonical isometry, the retained block W_1 is the positive square root of QP_0Q. The identity

\[
 I-QP_0Q=((I-P_0)Q)^*((I-P_0)Q)
\]

on the reference space makes W_1-I second order in the subspace angle. W_2 is first order. Expanding the four blocks of W^T A_0 W gives the asserted bound by a constant times b squared, with the displayed gap and ambient norm factors. This is the needed reason a squared off-subspace estimate suffices. Replacing it by a first-order operator bound would lose the resonance precision.

In the graph applications the ambient scaled operator norm is tight and the complementary gap is fixed. Their product with an o_P(scale) squared coupling remains o_P(scale), without a moment assumption or dimension factor.

## 3. Positive and negative reductions at m^(-1/2)

The reference f removes exactly the selected resonant endpoints. It is a linear combination of e and those coordinate vectors, so both reference spaces lie inside the selected projector controlled by the probability theorem. This point avoids importing an estimate for an unrelated random vector.

For fixed cutoff, each selected symmetric pair has coupling kappa/sqrt(m) to c_+. Antisymmetric pair coupling to the host cancels exactly. The collective diagonal differs from plus or minus kappa by O_P(1/m). Other retained pairs contribute only O_P(1/m) to that diagonal and O_P(m^(-1/2)) to the column norm, after restricting to bounded pair counts and weights. Those restrictions exhaust probability because both quantities are tight.

Consequently the corrected equations (17) and (18) have the stated coefficients. Adding the selected remainder and the graph-to-T error gives compressed error and squared off-subspace error O_P(log^4(n)/m), both o_P(m^(-1/2)). The finite canonical lemma yields the desired effective level matrices with a change of coordinates tending to the identity.

The complementary gap is justified with a fixed cutoff first. Other pair amplitudes differ from the resonant amplitude by integral powers of two, so their levels stay a fixed distance from the selected level. The global remainder has a small fixed-tolerance failure probability bounded by C 2^(-K). Taking n to infinity and then K to infinity supplies the actual complementary gap. No rate estimate has been applied at a growing cutoff.

For p at least one, the positive aggregate block has eigenvalues

\[
 \frac{\tau\pm\sqrt{\tau^2+4\kappa^2p}}2.
\]

Each is separated both from the other and from the dark value tau. The two corresponding eigenvalues are therefore simple with probability tending to one, and their projectors converge. The zero-sum positive pair space is a grouped subspace of dimension p-1. The p=0 case leaves a single collective value with zero shift on this scale.

The negative block has one zero coefficient and p coefficients -tau. When tau is nonzero these two sectors are separated. At tau=0 this first-scale calculation does not identify them. The synthesis uses the finer theorem for that case rather than inferring a basis from a repeated coefficient.

## 4. The second graph normalization

The accepted full-cluster isometry gives exact Gram matrix J^T J=I+Gamma and complementary leakage O_P(s). Hence

\[
 M=J^T P J=I+\Gamma+O_P(s^2).
\]

The inverse-square-root expansion is valid in operator norm near the identity. Its linear term is -Gamma/2 and its remainder is O_P(||Gamma|| squared+s squared). No commutativity of Gamma and T is assumed. Multiplying the exact normalized compression on both sides therefore produces both terms Gamma T and T Gamma, with the correct common factor -1/2.

The complementary compression contributes O_P(s) after division by s. Since ||T|| is tight, all remaining normalization terms have order O_P(||Gamma|| squared+s). The prior derivative rate gives ||Gamma||=O_P(s log^2(n)). Both s and s squared log^4(n) are o(sr). Thus the normalization bridge to the actual graph is proved at the precision required by the logarithmic theorem.

This is stronger than merely knowing that the scaled eigenvalues of the graph are close to those of T. The metric correction cannot be omitted at the logarithmic scale.

## 5. Logarithmic input and its use

The frozen probability input controls the same negative reference coordinates, using f outside the resonant endpoints. Its compressed constant block has coefficients -kappa squared/2 and -a. Its selected metric acts on each antisymmetric pair with coefficient -kappa sr and has negligible collective compression. Multiplication by the leading retained eigenvalue -kappa in the symmetric metric correction adds -kappa squared sr to each pair coefficient. This yields exactly -kappa squared/2 for the collective direction and -(a+kappa squared) for the pairs.

The logarithmic probability argument also supplies squared complementary coupling O_P(1/m). Since sr is comparable to log(n)/m, this is o_P(sr). The normalization error is o_P(sr), so it preserves the compressed coefficients and the required squared-coupling order. The canonical lemma then transfers the retained-matrix conclusion to the actual graph cluster.

The collective coefficient is tied to the finite-host stationary subtraction, rather than to the isolated finite star. The input's cancellation of the truncation length leaves e^T(G-gI)e=-s squared r+o_P(s squared r). Its derivative computation has the length-r factor and the antisymmetric sign required above. The synthesis uses these graph-derived statements and does not substitute the earlier tree-only derivative heuristic for them.

When a differs from -kappa squared/2, the two compressed logarithmic coefficients have a fixed positive separation. Ordinary separated-projector perturbation then gives a simple collective line and a grouped pair subspace. At the retuned value they coincide. Neither the lemma nor the displayed rate identifies a finer splitting or basis there, and the theorem correctly makes no such claim.

## 6. Physical scales, masses and random dimensions

The equality s/sqrt(m)=1/sqrt(n) gives the physical scale in the positive and first negative statements exactly. Multiplication of a logarithmic retained shift by s gives the physical scale s squared r. These are distinct scales.

A positive bright retained vector has fraction A in c_+ and therefore squared constant-host coordinate A/2. The marked-coordinate mass is 1-A/2. The physical lift divides the latter by D=8 in the added vertices and assigns the remaining factor 7/8 to the perpendicular host. This proves the stated three mass coefficients. At zero positive detuning, A=1/2 gives (1/4,3/32,21/32). Pure collective and pair directions give the stated (1/2,1/16,7/16) and (0,1/8,7/8) triples.

These deductions use uniform mass operators and convergent subspace identifications. They do not assume that arbitrary bases within repeated pair levels choose individual pairs.

The phase tends to one half in every resonance regime, so the pair-count mean is 3 c^(3/2)/(4 sqrt(2)). Each fixed p has a strictly positive limiting probability. An unconditional probability error tending to zero remains such an error after conditioning on that event. Tightness handles the unbounded but finite random dimension by first bounding p. No probability estimate is rederived under a rare-pair conditioning.

## 7. Integer tuning and the claimed failure of phase-only selection

The logarithmic tuning construction has n_j asymptotic to 2 m_j 4^j and preserves the required critical ratio. Its bracket tends to one, so the distance floor remains j. The rounding error is negligible relative to s r. Substitution gives w-kappa=a j s_0 plus a negligible error and s=s_0/(1+a j s_0/kappa) to the same precision. The ratio (w-kappa)/(sr) therefore tends to a.

Both a=0 and a=-kappa squared have phase tending to one half and square-root detuning tending to zero. Conditional on one resonant pair, the larger eigenvalue in the negative window is collective in the first case and a pair mode in the second. Their limiting constant-host masses are respectively one half and zero. The claimed failure of a phase-only ordered negative eigenvector law is therefore an actual graph consequence, on events of positive limiting probability.

## Accepted boundary

Revision 2 establishes the actual cubic graph positive avoided crossing, the negative logarithmic splitting including exact leading phase, and the separated physical mass laws. It preserves multiplicities as subspaces. The retuned logarithmic crossing, smaller-scale random coefficients, individual bases within repeated pair groups, and transfer of the isolated finite-star order 1/m correction remain unresolved. Probability, normalization, perturbation and physical mass transfer remain paper arguments, with finite formal components reported separately.
