# Review of the next-scale probability chain

Date: November 15, 2026. Reviewer: structural workstream. Revision 1.

Exact targets:

- `../probability/collective-limit-v1.md`, SHA256 `e492d3dfa506167ba28782e316129146e72f8046e96bbaf50b265e42d3fc307d`.
- `../probability/signed-coupling-v1.md`, SHA256 `68660a0914a02b0a6bf53f2ccef75a2b844859e9dafc7f8a9e106db3921d5fba`.
- `../probability/collective-self-energy-v1.md`, SHA256 `a3c6b1b42bed9f7f3c7c5d45c1292df5a207951e709e318db24f6f711c9d9d4d`.

Verdict: accepted as paper results at these exact revisions, with the explicitly frozen earlier probability premises. No open mathematical finding was identified. The actual nonlinear graph-root and physical eigenvector synthesis is not included in this verdict. Historical priority and complete formalization are not certified.

## Exposure and method

The reviewer previously reviewed the critical probability, spectral-law and subspace rounds. During this round the reviewer derived structural attachment theorems. The integrator reported agreement with the first two probability proofs and a candidate self-energy limit before assigning this review. The reviewer then read all three exact files and reconstructed their bounds and constants. No live root synthesis was read before this review was frozen.

The earlier selected-endpoint, mixed derivative and finite-sampling formulas were reopened at their frozen revisions. The review tests the actual order s squared raw quadratic scale and order s retained-pencil scale. It does not infer accuracy from the earlier logarithmic theorem alone.

## 1. Collective quadratic fluctuation

The fixed-size subset variance bound is correct. Writing the quadratic as 2/m times an unordered-pair sum gives an equal-pair contribution bounded by C||H||_F squared/n squared. The contribution from pairs with one common endpoint is bounded by C mL squared/n squared. Four-distinct-endpoint covariances are nonpositive because p_4<=p_2 squared, and the weights are nonnegative. No independent-mark approximation is used.

The conditional mean is exactly (m-1)(n v_R-tr U_R)/(n(n-1)). After division by s squared, its first part differs from v_R by O(L/m). The trace part has coefficient at most C/n. The nonnegative trace and Frobenius estimate give E tr(U_R)/n bounded by C(2^(-R/2)+L squared/sqrt(n)), tending to zero. This resolves the trace at the finer scale, rather than only after an additional division by r.

The normalized tail variance is bounded by

\[
 C\left(n2^{-R}/m^2+L^4/m^2+L^2/m\right).
\]

At criticality n s/m squared tends to 1/theta, so its limiting bound is C2^(-K). The averaged diagonal error divided by s squared is O_P(L cubed/m+L/m+n^(-4)/s squared), which vanishes. An operator maximum-diagonal bound would not be the same argument.

The stationary coefficient includes the j=0 term. Its cancellation with the tail mean is

\[
 r+g(3/2)(L-r-K)-g(1+3L/2)=-K-2/3.
\]

The short-pair coefficient is 2g 2^(phi_n-k)/(ms)=4 2^(phi_n-k)/(3theta_n). Thus equations (23)-(28) have the claimed constants and scale.

The lower-offset truncation uses probability of any omitted pair, not its expected amplitude. The limiting negative-offset sum is finite almost surely but has infinite expectation. The positive centered tail has variance b_0 2^(-K), so it converges in L2 and almost surely. This proves the convergence-together argument without assuming uniform integrability of the full variable.

The count vector is retained through both cutoffs. Conditioning on a fixed count is justified only after joint convergence, and its limiting probability is positive. The endpoint translation C_1 equal in law to C_0-1 is correct. Replacing the integer center r by the full logarithm cancels that translation.

## 2. The selected column improvement

The own-partner tail sum is O_P(L cubed/n). Its squared contribution after division by s squared and multiplication by m is O_P(L^6/m cubed), which vanishes.

For all other selected-column entries, the three-vertex inclusion factor multiplies the deterministic distance degree C2^r and the two-walk Frobenius bound n2^(-R)+L^4. Dividing by s squared gives

\[
 C\left(2^{-K}/m+L^4/m^3\right).
\]

The constants can be chosen independently of K. The selected set is defined by distance r and does not change with K. The diagonal and stationary auxiliary error has norm O_P(L cubed/m), whose square times m vanishes. Thus the left side of signed-coupling equation (14) is independent of K, and taking n first and then K proves the required little-o in (15). This is stronger than a fixed-K O_P(1/m) squared-column bound and is valid without a growing cutoff.

The raw selected block error O_P(L cubed/n), after scaling by 1/s, is o_P(s). The mixed selected vector error O_P(m^(-3/2)L+m^(-5/2)L cubed), including the diagonal and stationary terms, is also o_P(s). Substitution of the exact free-vector formula then cancels the leading pair contribution in f^TZa_-. A norm-only bound would not prove this signed order-s cancellation.

All these expectations were taken before imposing the host gap, matching or the final pair-count event. Restricting at the end to one resonant pair costs a bounded probability factor. The proof does not divide by an individual rare endpoint-pair probability.

## 3. Energy dependence and diagonal constants

The exact Schur pencil is correct and retains the constant host mode. Its derivative is diag(0,I-F'(3+sx)/8). The full derivative error is O_P(sL squared), and the second derivative converges to the scalar tree value. Uniform fixed-gap higher derivative bounds control the Taylor remainder.

Direct differentiation of the tree recursion gives g'(3)=-10/9, g''(3)=172/27 and

\[
 (2z-z^2g(z))''\big|_{z=3}=-136/3.
\]

Hence the actual pencil expansion contains +(17/6)s x squared P_M. Its sign and factor are correct.

The selected metric block has leading term s(r+1)w A_V and error O_P(L^4/n)=o_P(s). The raw collective derivative quadratic is O_P(s squared L squared), and the mixed derivative estimates also vanish after division by s. Replacing e by f costs O_P(sL squared/sqrt(m))=o_P(s). Thus the uses of the stronger form of the old derivative estimates are justified.

On the antisymmetric vector, the metric term is -kappa s(r+1)w to the required precision. Substituting the retuning produces the coefficient (11/6)kappa squared-beta=33/16-beta.

For the collective vector, removing the two endpoints gives f^TZf=e^TZe-2w/m+o_P(s). Its star correction is +kappa/m, which cancels the pair-removal term to this order because w tends to kappa. The exact stationary term in Z contributes 3s/4 to e^TZe. Half of that is 3s/8. The analytic quadratic term contributes (17/12)kappa squared s=51s/32. Their sum is 63s/32, as claimed.

## 4. Complementary inverse and signed Schur term

The complementary inverse admits one fixed bound independently of the auxiliary cutoff K. Here is an explicit reconstruction of that point. In a decoupled short matching model, all nonresonant negative levels have weights w_n 2^(-k) with k nonzero. Since w_n tends to kappa, their distance from -kappa is at least kappa/3 for large n, uniformly over integer k nonzero. Zero and positive levels have larger separation. The two removed modes are the collective negative direction and the unique distance-r antisymmetric direction.

For each fixed K, the count and maximum short weight are tight. Restoring the deleted star entries and replacing the free-star direction by c_- change the compressed complement by o_P(1). Therefore its inverse bound can be taken, for example, as 12/kappa for every fixed K, with failure probability tending to zero. The constant does not grow with K, even though the required large-n event may depend on K.

The global operator tail then transfers the gap to the actual pencil by first taking n large and then K large. The retained reference space depends only on the resonant pair, so this passage does not change the object whose inverse is bounded. The energy interval shrinks by O(s), preserving the same fixed gap.

The antisymmetric complementary column is o_P(sqrt(s)), while the collective column is O_P(sqrt(s)). Cauchy-Schwarz with the inverse bound makes the induced off-diagonal o_P(s), the pair diagonal o_P(s) and the collective diagonal O_P(s). This includes the full complementary correction, not only the direct signed entry. Differentiating the inverse gives a bounded derivative. The coupling derivatives are O_P(sL squared), so the correction varies by o_P(s) across the width-O(s) energy interval.

## 5. Collective complementary law

The collective tail column estimate retains its C2^(-K) factor after squaring and dividing by s. The analytic and auxiliary operator errors have squared norms o_P(s). Replacing e by f is valid because their difference is an O(1/m) constant component plus O(m^(-1/2)) selected coordinates. The selected residual columns and the bounded full comparison make this change negligible relative to sqrt(s).

In the self-energy comparison, restrict the actual collective column divided by sqrt(s) to a fixed large bound. The column difference estimate then bounds the model column on the same event. The resolvent identity with the K-independent gap from Section 4 proves the deterministic inequality (15). Sending n first, then K, and finally removing the large bound proves (16). No moment bound for the largest strong-pair weight is needed.

For the finite arrow calculation, let delta=m^(-1/2). The reference vector is c_0-delta times the sum of nonresonant symmetric pair vectors, up to O(delta squared). Applying S and subtracting its projection onto c_- yields the leading complementary column

\[
 \delta\left(\kappa t_0-\sum_{j\ge1}v_jt_j\right).
\]

The nonresonant coefficient is -v_j, not kappa. This is because c_- excludes only the resonant pair. The leading column lies in positive pair sectors, with inverse denominators -kappa-w_j. Therefore

\[
 m\Sigma^S=-\kappa^2/(\kappa+w_0)
              -\sum_{j\ge1}v_j^2/(\kappa+v_j)+o(1).
\]

The distinguished first numerator can be replaced by w_0 squared because w_0 tends to kappa. The finite-dimensional error is uniform after bounding counts and weights and restricting nonresonant lattice gaps. Stronger omitted pairs are removed by their probability, while the weak tail has expected size O(2^(-K)). This yields the stated D limit.

The collective quadratic and self-energy are approximated through the same short-pair count vector. Their limiting Poisson families are consequently the same family. Subtracting an independent copy would change the theorem. Conditioning on P_0=1 preserves the other independent coordinates and does not alter their means.

## 6. Cancellation, limits and remaining obligations

The coefficient identities (kappa squared/2)b_k=w_k/theta and lambda_k w_k=kappa squared theta/2 are correct. Their cancellation changes each random jump to J(w)=kappa w/(kappa+w). The deterministic constant is 63/32-kappa squared/3=51/32.

For k<=0, J(w_k) is bounded by kappa and the total Poisson intensity is finite. For k>=1, the centered variance series is summable and the deterministic drift is absolutely summable. Thus the coupled difference has finite second moment even though the two separate large-jump terms need not have finite mean. No subtraction of undefined expectations is used.

The accepted results are the compensated resolvent quadratic law, its joint count law, vanishing order-s signed Schur coupling, the two diagonal coefficients and the joint collective self-energy law. A proof that the limiting collective scalar does not coincide with the pair scalar, integer tuning, nonlinear root selection and physical graph eigenvector reconstruction remain separate obligations. They have not been silently included in this acceptance.
