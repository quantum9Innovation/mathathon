# Independent review of the structural theorem and retuned graph law

November 15, 2026. Reviewer: fresh_referee. Recipient and integrator: root. Revision 1, frozen.

## 1. Decision and exact scope

No blocking mathematical error was found in either target revision. The vector-port theorem is supported at its stated first-order critical scale. The retuned cubic duplication theorem is supported at physical scale s squared, including fixed resonant multiplicity, the unconditional mixture and the grouped physical projectors.

This is an independent paper audit of the supplied arguments and their load-bearing frozen premises. It is not an independent discovery, a historical-priority decision or an end-to-end formal verification. The standard fixed-degree simplicity bound and two-sided host spectral-gap theorem remain imported primary mathematical inputs. Their full published proofs were not re-proved here.

The review does not extend the attachment theorem to several local resonant channels, oriented ports, growing local dimensions, or finer order-s-squared coefficients. It does not extend the retuned theorem to a random graph-adapted beta, conditioning on a shrinking near-coincidence event, or a basis inside the repeated pair group.

The exact reviewed targets are:

| Target | SHA256 |
| --- | --- |
| structural/vector-port-v1.md | ff889b703f36bdf1bea9854c20c41b97578abdd92a474fc5e7c6bcc03472cde8 |
| root/retuned-graph-law-v1.md | 5c2b7bd527a47ca2c870ada456a5bd57e985ffafe5e949cf3dfb595dda537e6e |

Both hashes matched disk before the review. No candidate file or earlier round was edited.

## 2. Independence and evidence read

The review started from root AGENTS.md, the mathematical collaboration skill and input/PROBLEM-v1.md. No existing review or acceptance verdict was read before freezing this report. The input baseline manifest was read for source identities. It lists review filenames and hashes, but their contents and decisions were not consulted.

The following probability-chain hashes were checked against disk:

| Frozen dependency in this round | SHA256 |
| --- | --- |
| probability/collective-limit-v1.md | e492d3dfa506167ba28782e316129146e72f8046e96bbaf50b265e42d3fc307d |
| probability/signed-coupling-v1.md | 68660a0914a02b0a6bf53f2ccef75a2b844859e9dafc7f8a9e106db3921d5fba |
| probability/collective-self-energy-v1.md | a3c6b1b42bed9f7f3c7c5d45c1292df5a207951e709e318db24f6f711c9d9d4d |
| probability/density-and-tuning-v1.md | cf3e7ef384fad52dd78f22fbdb2d121a8c99049f4736012c4a7dfeae14a91098 |
| probability/multiplicity-extension-v1.md | 2649c74230d20b7411cdf1a92276c63b8181e0674e53d5f58e87a63918f796cc |

The following earlier premises were read directly and their hashes checked:

| Earlier dependency, relative to spectral-gap/ | SHA256 |
| --- | --- |
| growing-defects-round-01/probability/proof-v1.md | 56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b |
| close-pair-transition-round-01/root/nonbacktracking-upper-v1.md | d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896 |
| close-pair-transition-round-01/root/cluster-width-v1.md | e40164dcf711cca13d945b666645c26aa8095b835e1e727d2d6d7159a78e7b8f |
| critical-law-round-01/root/effective-operator-v1.md | 13b559897d6ed9253a2fc6dd4dede5dd03914c078558d759542afc9c54d28864 |
| critical-law-round-01/probability/pair-counts-v1.md | 702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29 |
| critical-law-round-01/root/critical-law-v1.md | e379a0b55e81925276d2c3046ec1cc4b25c21e028d22fef53516f4b5828e48f3 |
| critical-subspaces-round-01/probability/refined-resolvent-v1.md | bd00db6c2f69813d480f5a86d5d22c8b6fe4922d9cc3d233f72840dddb29f8df |
| critical-subspaces-round-01/probability/negative-log-scale-v1.md | faced6a02d91d451e4ef0e0989d3d46811da66d809d40e9344e9444012901409 |
| critical-subspaces-round-01/root/subspaces-v1.md | f13fbd47ba04bd638f4bafe940c20d604bfa4a4653df553b4b737f2e3779e87a |

The critical-law proof was read through its truncation, phase and tail arguments. The other listed mathematical files were read through their relevant proofs. The graph-resonance-v2 argument was not required for the new fine-scale transfer: the new application uses its own exact energy-dependent Schur equation, the coarse subspace count and the directly reconstructed probability chain.

## 3. Structural audit

### S1. Polynomial locality and the stationary matrix

Resolved in the target revision, equations (12) through (15).

For one matrix entry of the polynomial b(x)b(x) transpose, write

\[
 b(x)b(x)^T=b(z)b(z)^T-(z-x)R_z(x).
\]

Multiplication by the projected host resolvent gives the compressed term b(z)b(z) transpose times G_E(z), minus E transpose R_z(A)QE. On the fixed-radius locality event, the unprojected polynomial compression equals its tree moment times the identity. Since Q=I-uu transpose, subtracting the projected polynomial adds the positive stationary term R_z(d)J_m/n. Subtracting the corresponding tree integral gives exactly target equation (13), including its sign.

All polynomial degrees and local dimensions are fixed. The required local-tree failures cost O(m/n), and short fixed-distance pairs cost O(m squared/n). Both vanish at criticality. The same event works for the whole z interval, so differentiating this identity is justified. The marked-resolvent derivative theorem is stated for every fixed d and every fixed derivative order before its subcritical specialization. Applying that finite theorem at m of order n to the one-third power is legitimate.

### S2. Extra motif channels and top-cluster inertia

Resolved in the target revision, Sections 1 and 4.

K_*(d) is positive semidefinite because d lies strictly above the tree spectrum. If dI-C had a null vector, positivity of K_0 and K_*(d) would force that vector into span(v), then force the nonzero polynomial p_v to vanish in the tree integral. This is impossible. Thus dI-C is positive definite.

The host complement is positive in zI minus the augmented operator near d. Its Schur block has motif derivative at least the identity. At d minus epsilon, the m resonant directions are negative while the other m(k-1) directions remain uniformly positive. At d plus epsilon every motif direction is positive. The host-to-motif coupling has norm O(s), so the retained endpoint negative inertias are respectively m+1 and zero. These are the inertias of the full operator after adding the positive eliminated host block. The argument therefore counts the actual largest m+1 eigenvalues and establishes a fixed gap below them. It does not rely on applying the older one-vertex interlacing statement to a k-vertex motif.

### S3. Physical lift, exact compressed energy and rates

Resolved in the target revision, equations (17) through (20).

Direct multiplication leaves the motif residual

\[
 \Delta_n(d)(y\otimes v)/\sqrt D
 -b(d)(G_v(d)-g_v(d)I)y/(\beta\sqrt D).
\]

Using the stationary matrix from S1 reduces this to

\[
 (J_my/n)\otimes(\beta b'(d)-p_v'(d)b(d))/\sqrt D.
\]

Its motif direction is orthogonal to v. Consequently J transpose W is zero even though W itself need not vanish. Its norm is O(s squared), J transpose V is exactly the identity, and J transpose HJ=sT is exact. This verifies the additional nonseparable term instead of silently discarding it.

The Gram correction is exactly diag(1,(I-G_v'(d))/D). Its error is O_P(a_n). With ||T||=O_P(1), HJ=O_P(s), and the fixed complementary spectral gap gives ||(I-P)J||=O_P(s). The discarded compressed energy has norm O_P(s squared). Dividing by s, then normalizing the Gram matrix, yields the target O_P(a_n) comparison without a factor m. At criticality a_n=O(n^(-1/3) log squared(n))=o(m^(-1/2)).

The motif mass and host-constant mass are explicit in J. The Gram identity supplies the remaining host mass. The resulting statement is uniform on the entire retained unit sphere. It is stronger than a statement about individual eigenvectors and is sufficient for grouped level projectors.

### S4. Pair law and example

Resolved in the target revision, Section 6.

Projection onto v leaves the scalar polynomial p_v. Its propagation factor is beta squared times g_d(d), divided by D, hence h=g_d(d)kappa squared. The stationary correction has normalized norm O(s). The older whole-space pair-tail estimate is independent of the attachment and applies to G_E. Multiplying by the fixed local coefficient preserves its q^(-K) failure bound. Deleting star entries on the tight number of short-pair endpoints costs O_P(m^(-1/2)). The matching, two-sided truncation and multiplicity-preserving contour arguments therefore apply with the new kappa and h.

For the displayed nonseparable example, the kernel of K_0, its other eigenvalue 55/12, the claimed D and the claimed kappa squared agree with direct tree-moment calculation. In particular, writing p_v(x)=a+bx gives

\[
 g_v(z)=(a+bz)^2g_3(z)-2ab-b^2z.
\]

Differentiating this identity verifies equation (21). A bounded symbolic check corroborated the two stated constants with exact zero differences. This check is not a premise of the general theorem.

## 4. Retuned probability audit

### R1. Raw collective fluctuation and exact centering

Resolved in collective-limit-v1, Sections 3 through 6.

The exact off-diagonal stationary coefficient is -g(1+3L/2)(J-I)/n. The zero-length projected term contributes the 1. It cannot be replaced by the positive-length coefficient alone.

For the nonnegative tail U_R, the fixed-subset quadratic Y has conditional variance bounded by

\[
 C\left(\|U_R\|_F^2/n^2+mL^2/n^2\right).
\]

Equal-edge terms use p_2, shared-endpoint terms use p_3, and disjoint-edge covariances are nonpositive. The two-walk estimate E||U_R||_F squared <= C(n2^(-R)+L^4) then leaves a bound C2^(-K) after division by s to the fourth power. The remaining logarithmic terms vanish.

The exact sampled mean differs from s squared times 3(L-R)/2 by o_P(s squared). Its trace correction is controlled by E tr(U_R)/n <= C(2^(-R/2)+L squared/sqrt(n)), which tends to zero. The averaged diagonal error divided by s squared is O_P(L cubed/m), also tending to zero.

Thus the deterministic cancellation is

\[
 r+\tfrac23\tfrac32(L-R)-\tfrac23(1+3L/2)=-K-2/3.
\]

Both tails are treated at the correct level. The stronger-pair tail is controlled by its occurrence probability, not by its divergent expected amplitude. The weaker centered tail is L2-small. This establishes the compensated law with its exact -2/3 constant.

### R2. The selected-column improvement and signed cancellation

Resolved in signed-coupling-v1, Sections 3 through 4, using the raw estimates in negative-log-scale-v1 and refined-resolvent-v1.

For selected endpoints witnessed by a distance-r partner, the remaining selected tail columns use three distinct marked vertices. Their squared norm after division by s squared is bounded in expectation by

\[
 C p_3 2^r(n2^{-R}+L^4)/s^2
 \le C(2^{-K}/m+L^4/m^3).
\]

The own-partner total is O_P(L cubed/n). Squaring that total controls its squared Frobenius contribution. The diagonal and stationary operator has norm O_P(L cubed/m), whose square times m vanishes. All statements preceding the final conditioning are unconditional.

The residual (Z-wA_V)P_V does not depend on K. Therefore the fixed-K limiting bound C eta^(-1)2^(-K) proves its squared norm is o_P(1/m) after K tends to infinity. This is a real improvement over an O_P(1/m) bound, and is required for the asserted zero limiting coupling.

The raw selected block and selected constant-column estimates are stronger still at the specific scalar contractions. Using

\[
 f=(e-m^{-1/2}\mathbf1_V)/\sqrt{1-|V|/m}
\]

and orthogonality of every selected antisymmetric vector to e and to 1_V cancels the leading pair term. It gives f transpose Za=o_P(s). A mere residual norm bound would not have proved this rate. The candidate uses the required signed calculation.

### R3. Analytic constants and the exact pencil

Resolved in signed-coupling-v1, Sections 5 through 8.

The exact cubic identity is F(z)=2zI-z squared G(z)+A_C-(z+3)J/n. The tree relation 2rho squared-zrho+1=0 gives rho(3)=1/2, rho'(3)=-1/2 and rho''(3)=2. Hence g_3''(3)=172/27 and f''(3)=-136/3. An exact symbolic differentiation check produced those same rational values.

The all-orders marked-resolvent theorem gives F''(3)-f''(3)I=o_P(1). A uniform fixed-gap third-derivative bound then supplies the genuine pencil expansion

\[
 \mathcal T_n(x)=T-x\Gamma+(17/6)s x^2P_M+o_P(s).
\]

The selected derivative term is s(r+1)wA_V. On an antisymmetric direction it combines with the tuning of -w to give

\[
 x_n^0+s((11/6)\kappa^2-\beta_n)+o_P(s)
 =x_n^0+s(33/16-\beta_n)+o_P(s).
\]

For the collective direction, excluding p resonant pairs changes the marked quadratic by -2pw/m and the host star by +p kappa/m. The resulting p(kappa-w)/m is o(s), so it leaves no missing finite-p centering. The exact additional stationary rank-one term contributes 3s/4 to e transpose Ze. The collective analytic term is (17/12)kappa squared s. Together these give the raw collective coefficient (kappa squared/2)C_n+63/32.

All neglected tuning products are bounded by O(s squared r squared)=o(s). No rate for theta_n=ms tending to theta beyond convergence is needed.

### R4. Complementary self-energy and coupled cancellation

Resolved in collective-self-energy-v1, Sections 2 through 6, and multiplicity-extension-v1, Section 5.

The collective tail-column estimate retains 2^(-K) after division of its squared norm by s. The global operator comparison controls the complementary inverse by the resolvent identity. With the actual collective column divided by sqrt(s) tight, these bounds prove the cutoff approximation for Sigma/s by taking n first and K second. No growing cutoff is being smuggled into a fixed-cutoff estimate.

In the finite symmetric pair sector, let delta=m^(-1/2). The reference collective vector excludes only selected resonant endpoints. Its first-order correction contains minus delta times each other symmetric pair vector. Thus its projected complementary coupling is kappa times each selected symmetric pair vector and minus v_j times each other symmetric pair vector. It is not kappa times every pair vector.

The limiting inverse denominators are -kappa-w for selected symmetric channels and -kappa-v_j for the other symmetric channels. Consequently

\[
 m\Sigma^S=-p\kappa^2/(\kappa+w)-\sum_jv_j^2/(\kappa+v_j)+o(1).
\]

This gives the claimed common-process correction. Its stronger-pair tail again uses a rare-event bound. Its weaker tail has expected size O(2^(-K)). Combining with the quadratic using the same counts yields

\[
 t-t^2/(\kappa+t)=\kappa t/(\kappa+t)=J(t).
\]

The scalar constant becomes 63/32-kappa squared/3=51/32. The combined jumps are bounded. The finite second moment follows from the combined representation, not by subtracting the nonexistent separate means.

### R5. Conditioning, density, moments and integer tuning

Resolved in the frozen probability chain.

Every fixed-p event has a limiting positive Poisson probability. The proofs first establish unconditional estimates and joint count convergence, then divide by this positive probability. The finite range 0<=p<=P has a positive minimum limiting conditioning probability. Tightness of p_n therefore suffices for the unconditional mixture after P tends to infinity.

The positive-offset jump size is a_k=kappa/[theta(2^k+1)]. Choosing k=floor(log_2(|t|kappa/theta)) makes |t|a_k lie in [1/2,2] and lambda_k at least 9|t|/32. One term of the characteristic exponent already gives exponential Fourier decay. Fixing P_0 does not affect that positive-offset term. This proves a bounded smooth density and zero probability of coincidence with the deterministic pair coefficient.

The unbounded support in both directions follows from finite zero-count events on initial positive offsets and the independent small centered tail for the negative side, and from an arbitrarily large P_1 for the positive side. Therefore neither ordering is excluded for any finite beta.

The positive and negative offset means cancel in matched pairs. Their variance contributions agree in matched pairs. This gives exactly the displayed conditional mean and variance, without asserting convergence of finite-n moments.

The integer construction keeps the phase in the interior near 1/2, so r_j=j eventually. Rounding n_j to an even integer has error O(1/(n_js_0)) in beta_j, which tends to zero. The remaining detuning error is O(j squared s_0). The construction realizes every finite beta at the specified c.

## 5. Actual graph roots and projectors

### G1. Exact nonlinear equation and root count

Resolved in retuned-graph-law-v1, Sections 5 through 6.

Eliminating the positive host complement and applying the congruence diag(1,8^(-1/2)I), followed by division by s, gives exactly xI minus the stated energy-dependent matrix. The constant host direction is retained, so no singular division by z-3 occurs. The second Schur complement is also exact wherever its complementary inverse exists.

The complementary gap follows from the lattice spacing of all offsets other than zero, the removal of all p selected negative pair directions and the collective negative direction, and the fixed-cutoff then increasing-cutoff operator estimate. It does not require the old O_P(s) cluster approximation to resolve order s within normalized coordinates.

On a bounded fine window, the new diagonal block has uniform o_P(s) error. The direct derivative is O_P(s log squared(n)). Differentiating the complementary inverse gives bounded norm, and its coupling columns are O_P(sqrt(s)) or smaller. Therefore the self-energy derivative is O_P(s), and the full derivative is o_P(1).

It follows that the derivative of xI-B_n(x) is positive definite with probability tending to one. For a sufficiently large tightness window its endpoint matrices have opposite definiteness. Ordered eigenvalues of this pencil therefore cross zero exactly once, counted with multiplicity. Uniform Weyl bounds compare these roots to the ordered diagonal entries at error o_P(s). Inertia and kernel preservation in both exact Schur steps identify them with actual augmented-graph eigenvalues. The coarse rank count excludes additional roots in I_n. Taking the fine-window size to infinity is justified by tightness of L_(n,p).

### G2. Fine separation and physical subspaces

Resolved in retuned-graph-law-v1, Section 7.

The random limiting collective coefficient has no atom at the fixed pair coefficient. After excluding a coefficient gap below 2delta, the normalized block has gap at least 2delta s. Its uniform o_P(s) error forces the collective retained kernel toward the first coordinate and every pair kernel toward the remaining p coordinates. Although the block depends on the root, the same uniform estimate applies at each root. For fixed p, comparing the resulting orthonormal graph eigenvectors gives the grouped projection statement without requiring a common eigenbasis for all energy values.

The second Schur reconstruction adds a complement of norm O_P(sqrt(s)). The first reconstruction is J_x and obeys ||J_x-J_0||=O(s) on the whole coarse bounded window. J_0 transpose J_0 tends to the identity by the actual marked derivative estimate. These statements justify normalization and transfer into graph space.

The exact motif mass is ||v|| squared/8 and the exact constant-host mass is alpha squared before asymptotically harmless normalization. The remaining Gram mass tends to 7||v|| squared/8. The collective vector therefore has masses (1/2,1/16,7/16), and the entire pair subspace has masses (0,1/8,7/8). Sending delta to zero completes the conditional probability conclusion.

No nonzero limiting avoided-crossing entry is used. Random ordering follows from the two diagonal levels, while the signed coupling and induced pair correction are o_P(s). Those are distinct assertions, and the candidate keeps them distinct.

## 6. Findings, limitations and requested integration

No first unsupported inference, scale contradiction or counterexample was established. Checks S1 through S4, R1 through R5 and G1 through G2 are resolved within the exact revisions reviewed above. They required no silent weakening and no correction to either candidate.

No random-graph simulation or unbounded computation was run. One bounded exact symbolic differentiation check corroborated the scalar second derivatives and the displayed vector-port example constants. A first attempt used an unavailable interpreter name, then the same bounded check completed using the installed interpreter. The analytic audit does not depend on that computation.

Proposed review status: reviewed for both exact target hashes. Mathematical promotion remains the integrator's responsibility. The standard simplicity and host-gap inputs, probability asymptotics, root analysis and physical projections remain paper arguments. No new formalization or priority status is proposed.

Requested next action: attach this exact-revision report to both candidate records and retain their present scope and formalization qualifications. If either target or a load-bearing premise changes, mark this review stale and request a new revision-specific check.
