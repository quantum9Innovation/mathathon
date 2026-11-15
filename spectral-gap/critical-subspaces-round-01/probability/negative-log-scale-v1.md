# The logarithmic negative resonance scale

November 15, 2026. Owner: probability workstream. Revision 1, frozen for separate review.

## 1. Statement, scope and exposure

Use the critical cubic model and notation of `refined-resolvent-v1.md`, SHA256 `bd00db6c2f69813d480f5a86d5d22c8b6fe4922d9cc3d233f72840dddb29f8df`. In particular `m/n^(1/3)->c>0`, `s=sqrt(m/n)`, `r=floor(log_2(1/s))`, and G is the marked projected resolvent at 3 on the fixed host-gap event. Put

\[
 g=2/3,\qquad \kappa=3/\sqrt8,\qquad
 w=\frac34\frac{2^{-r}}s,\qquad t_n=sr.
\tag{1}
\]

The variable t_n in this file is a small scale, not the tree recursion parameter. It has order `(log n)/m`. Suppose

\[
 \frac{w-\kappa}{sr}\longrightarrow a\in\mathbb R.
\tag{2}
\]

This implies that the fractional distance phase tends to 1/2. Exact phase 1/2 gives `w=kappa` and a=0.

Let V be the marked vertices belonging to a pair at distance exactly r, and let p be the number of these pairs. With probability tending to one these pairs are disjoint. Their count is tight by the frozen pair-count theorem. On that event define A_V to be their matching adjacency on the marked coordinate space, extended by zero outside V. Let f be the unit constant vector on the marked coordinates outside V, zero on V. The event `2p<m` has probability tending to one.

Define actual retained matrices from the graph by

\[
 T=\begin{pmatrix}0&\kappa e^\top\\\kappa e&Z\end{pmatrix},
 \qquad
 Z=-F(3)/(8s),\qquad
 \Gamma=\operatorname{diag}(0,F'(3)/8-I),
\tag{3}
\]

where F is the cubic pole-free Schur block. Set

\[
 \widehat T=T-\tfrac12(\Gamma T+T\Gamma).
\tag{4}
\]

This file proves statements about these explicit finite graph matrices. A separate normalization theorem is needed to identify (4), with error `o_P(sr)`, with the actual scaled augmented adjacency restricted to its near-3 cluster. That theorem is not assumed to be already established in this file.

For each selected pair choose either endpoint ordering and define its unit antisymmetric vector `a_j=(e_u-e_v)/sqrt(2)`. Let h denote the host coordinate in the retained space, and define the isometry U with columns

\[
 b_-=(h-f)/\sqrt2,\qquad a_1,\ldots,a_p.
\tag{5}
\]

All matrices and isometries can be extended arbitrarily on the exceptional events just excluded.

**Theorem 1.** The following actual retained-matrix estimates hold:

\[
 \left\|\frac{U^\top(\widehat T+\kappa I)U}{sr}
 -\operatorname{diag}\left(-\frac{\kappa^2}{2},
                    -(a+\kappa^2)I_p\right)\right\|
 \xrightarrow{\mathbb P}0,
\tag{6}
\]

\[
 \|(I-UU^\top)\widehat T U\|^2=O_{\mathbb P}(1/m)
 =o_{\mathbb P}(sr).
\tag{7}
\]

Variable p causes no ambiguity. The norm is taken in the realized `(p+1)`-dimensional space, and p is tight. The theorem includes p=0.

At a=0 the collective coefficient is `-kappa^2/2`, while every negative pair coefficient is `-kappa^2`. They are distinct. The crossing parameter suggested by this scale is `a=-kappa^2/2`, where the theorem no longer separates these two sectors. It does not determine individual vectors within a repeated pair sector.

Exposure: the integrator proposed the two coefficient guesses and the normalization expansion in (4). The proof below independently derives the probability coefficients and treats (4) as its explicit object. The earlier refined probability proof was authored in this same workstream. No new probability attempt by another owner was read before freezing. All earlier source hashes remain as recorded in that proof. This revision does not modify an earlier frozen attempt.

## 2. Needed finite estimates and one sharpening

Fix any integer K>=0, put `R=r+K`, and take `L=ceil(C_0 log n)` with C_0 large enough for both the projected resolvent and its first derivative to have operator tails at most `n^(-4)` on H. Let

\[
 U_R=\sum_{j=R+1}^L2^{-j}N_j,\qquad
 T_R=\operatorname{offdiag}(E^\top U_R E).
\tag{8}
\]

Here N_j counts nonbacktracking incidence walks. Its constant row sum is `3*2^(j-1)`. Thus U_R is nonnegative and symmetric, has row sum `v_R=3(L-R)/2`, and satisfies

\[
 \mathbb E\|U_R\|_F^2\le C(n2^{-R}+L^4)=:C H_R.
\tag{9}
\]

For the distance-r indicator D_r, the unequal-length two-walk estimate gives

\[
 \mathbb E\sum_{u,v}D_r(u,v)(U_R)_{uv}\le C2^rL^3.
\tag{10}
\]

These are unconditioned simple-host estimates. Fixed marks can equivalently be sampled as an independent uniform m-subset after the host. A specified v-element set is then included with probability `p_v=(m)_v/(n)_v`. No calculation conditions on the occurrence of a rare selected pair.

The earlier selected row-square estimate can be sharpened. On the short-matching event, split selected entries into their own-partner entries and all remaining columns. The sum of the own-partner entries has expectation at most

\[
 C p_2 2^rL^3=O(L^3/n).
\tag{11}
\]

Consequently its square, divided by s squared, is `O_P(L^6/(n^2s^2))=O_P(L^6/m^4)`. The squared Frobenius norm of the own-partner entries is at most that squared sum.

For every remaining selected-row entry, its row endpoint, the partner witnessing that endpoint and its column endpoint are three distinct marks. The distance degree is at most `C2^r`. The argument of equation (22) in the previous proof therefore gives

\[
 \mathbb E\left[\mathbf1_{M_R}
   \|\text{remaining selected columns of }T_R/s\|_F^2\right]
 \le C p_3 2^r H_R/s^2=O(1/m+L^4/m^3).
\tag{12}
\]

Here M_R is the short-matching event. Its probability tends to one. Combining (11) and (12) proves

\[
 \|(T_R/s)P_V\|_F^2=O_{\mathbb P}(1/m).
\tag{13}
\]

The previous collective-column calculation already gives `||T_R e/s||^2=O_P(1/m)`. The diagonal and stationary auxiliary operator has norm `O_P(L^3/m)`, whose square is `o(1/m)`. The short matching matrix satisfies `||W_R e/s||^2=O_P(1/m)`, because the number of retained pairs and their largest scaled amplitude are tight. It follows that

\[
 \|Ze\|=O_{\mathbb P}(m^{-1/2}),\qquad \|Z\|=O_{\mathbb P}(1),
\tag{14}
\]

and

\[
 \|(Z-wA_V)P_V\|^2=O_{\mathbb P}(1/m).
\tag{15}
\]

In (15), no other short edge is incident to V on M_R. The event of a direct marked edge has probability tending to zero. The exact marked-block formula on its complement is

\[
 Z=\frac9{8s}(G-gI)+\frac3{4ns}J.
\tag{16}
\]

All rates in this section hold for each fixed K, uniformly in the phase. The resulting bounds (14) and (15) concern matrices independent of K. No growing-cutoff estimate is used.

## 3. A finite-sampling variance bound

Let H be any deterministic symmetric nonnegative matrix with zero diagonal, row sums at most CL, and let S be a uniform m-subset. Define

\[
 Y=\frac1m\sum_{u\ne v\in S}H_{uv}.
\]

Then

\[
 \mathbb E(Y\mid H)=\frac{p_2}{m}\sum_{u\ne v}H_{uv},
\tag{17}
\]

and

\[
 \operatorname{Var}(Y\mid H)
 \le C\left[\frac{\|H\|_F^2}{n^2}
                  +\frac{m L^2}{n^2}\right].
\tag{18}
\]

To prove (18), write Y as `2/m` times a sum over unordered pairs. The diagonal terms in the variance expansion have coefficient at most p_2. Terms sharing one endpoint have coefficient at most p_3, and their weighted sum is bounded by a constant times the sum of squared row sums. Terms with four distinct endpoints have covariance `p_4-p_2^2<=0` and nonnegative weights, so they may be discarded in an upper bound. The inequality follows from

\[
 p_4/p_2=\frac{(m-2)(m-3)}{(n-2)(n-3)}\le p_2
\]

for sufficiently large m. Multiplying by `4/m^2`, and using `p_2<=C m^2/n^2` and `p_3<=C m^3/n^3`, proves (18). This proof uses fixed-size sampling exactly and introduces no independent-mark assumption.

Apply this with H equal to the off-diagonal part of U_R. Its exact row sum before diagonal deletion is v_R, so

\[
 \mathbb E(Y\mid U_R)
 =\frac{m-1}{n(n-1)}(nv_R-\operatorname{tr}U_R).
\tag{19}
\]

The difference between the first term and `s^2 v_R` is `O(L/n)`. Also, by Cauchy-Schwarz and (9),

\[
 \mathbb E\operatorname{tr}U_R
 \le\sqrt{n\,\mathbb E\|U_R\|_F^2}
 \le C(n2^{-R/2}+\sqrt n L^2).
\tag{20}
\]

The trace term in (19), divided by `s^2 r`, consequently tends to zero in probability. Taking expectations in (18) gives

\[
 \mathbb E\operatorname{Var}(Y\mid U_R)
 \le C(2^{-R}/n+L^4/n^2+mL^2/n^2).
\tag{21}
\]

After division by `(s^2r)^2`, the three terms are bounded respectively by `C/r^2`, `C L^4/(m^2r^2)`, and `C L^2/(mr^2)`. They tend to zero. Equations (19) through (21) therefore prove

\[
 e^\top T_R e=s^2\frac32(L-R)+o_{\mathbb P}(s^2r).
\tag{22}
\]

## 4. The collective logarithmic drift

The diagonal quadratic term is negligible at the present scale. The single-walk excess-return estimate, averaged over the m marks rather than maximized, gives

\[
 \frac1m\sum_{u\in S}|G_{uu}-g|
 =O_{\mathbb P}(L^3/n+L/n+n^{-4})
 =o_{\mathbb P}(s^2r).
\tag{23}
\]

The diagonal excess before the stationary subtraction is nonnegative, so Markov's inequality applies to that average. This is a different bound from the earlier maximum over all marked diagonal entries.

The short matching has a tight number of edges and a tight largest scaled weight. Hence

\[
 e^\top W_R e=O_{\mathbb P}(s/m)=O_{\mathbb P}(s^2).
\tag{24}
\]

The exact projected nonbacktracking decomposition has off-diagonal stationary term `-g(1+3L/2)(J-I)/n`. Combine this term with (22), (23) and (24). Since `g*(3/2)=1`, the L contributions cancel and give

\[
 \begin{split}
 e^\top(G-gI)e
 &=g s^2\tfrac32(L-R)
   -g s^2(1+3L/2)+o_{\mathbb P}(s^2r)\\
 &=-s^2r+o_{\mathbb P}(s^2r).
 \end{split}
\tag{25}
\]

Replacing `(m-1)/n` by `m/n` in the stationary term costs only `O(L/n)`, which is negligible here. The fixed difference `R-r=K` also contributes only `O(s^2)`.

By (16),

\[
 e^\top Z e=-\kappa^2 sr+o_{\mathbb P}(sr).
\tag{26}
\]

Since `||f-e||=O_P(m^(-1/2))`, equations (14) and (26) imply

\[
 f^\top Z f=-\kappa^2 sr+o_{\mathbb P}(sr).
\tag{27}
\]

Indeed, the change in the quadratic form is `O_P(1/m)=o_P(sr)`. This argument allows f to remove only V, which makes f independent of the auxiliary cutoff K.

## 5. Selected diagonals and the selected constant block

The improved diagonal estimate at the selected endpoints needs no new conditioning argument. Let X_j(u) be the nonnegative weighted excess-return sum used for the j-th ordinary resolvent derivative, with j=0 or 1. The single-walk argument gives

\[
 \mathbb E\sum_u X_j(u)\le C L^{j+3}.
\]

The indicator that u is selected is at most the sum of the marked partners v with `D_r(u,v)=1`. Its deterministic distance degree is at most `C2^r`. Averaging the two-mark inclusion probability first yields

\[
 \mathbb E\sum_{u\in V}X_j(u)
 \le C p_2 2^r L^{j+3}=O(L^{j+3}/n).
\tag{28}
\]

The stationary diagonal contribution is `O_P(L^{j+1}/n)` because |V| is tight. Operator tails remain negligible. Thus

\[
 \|P_V\operatorname{diag}(G-gI)P_V\|
 =O_{\mathbb P}(L^3/n),
\tag{29}
\]

and the analogous first-derivative diagonal bound is `O_P(L^4/n)`.

The selected off-diagonal own-pair tail is `O_P(L^3/n)` by (10) and p_2. The different-pair contribution is bounded using four distinct marked endpoints, as in equation (23) of the previous proof, and is `O_P(L/n)`. The stationary selected block has norm `O_P(L/n)`. Therefore

\[
 \|P_V(G-gI-g2^{-r}A_V)P_V\|
 =O_{\mathbb P}(L^3/n)=o_{\mathbb P}(s^2r).
\tag{30}
\]

In particular,

\[
 P_V Z P_V=w A_V+o_{\mathbb P}(sr).
\tag{31}
\]

The same pair-selected estimates give the mixed bound

\[
 \|P_VZe-wP_Ve\|=o_{\mathbb P}(sr).
\tag{32}
\]

For clarity, the short matching contribution is exactly `wP_Ve`. The tail contribution after division by s is `O_P(m^(-3/2)L+m^(-5/2)L^3)` from the earlier three-endpoint calculation. The selected diagonal contribution and the stationary vector are smaller, using (29) and `||P_Ve||=O_P(m^(-1/2))`.

Every selected antisymmetric vector a_j is orthogonal to both e and f. Equations (15), (32), and `||f-e||=O_P(m^(-1/2))` give

\[
 \max_j|f^\top Z a_j|=o_{\mathbb P}(sr).
\tag{33}
\]

To see why the replacement of e by f is harmless here, write `Za_j=-w a_j+v_j` with `||v_j||=O_P(m^(-1/2))` jointly over the tight set of selected pairs. The leading term is orthogonal to f-e, and the remaining inner product is `O_P(1/m)`.

## 6. Selected derivative and metric correction

For z near 3, the tree recursion parameter is

\[
 \rho(z)=(z-\sqrt{z^2-8})/4,
\]

and the exact projected nonbacktracking identity is

\[
 R_Q(z)=g_3(z)\left[Q+\sum_{j\ge1}\rho(z)^jN_jQ\right].
\tag{34}
\]

It follows from the nonbacktracking generating identity and `z=rho(z)^(-1)+2rho(z)`. On the fixed host-gap event, the series and its first derivative converge in operator norm in a fixed neighborhood of 3. At 3, `rho=1/2`, `rho'/rho=-1`, `g_3=2/3`, and `g_3'=-10/9`. Thus the derivative series has the short off-diagonal term

\[
 (g_3'-g r)2^{-r}A_V
\]

on the selected block. Every weighted tail entry is bounded in absolute value by a constant times L times the corresponding nonnegative U_R entry, while the stationary derivative coefficient is `O(L^2)`. Using (28) for j=1 and the same selected tail bounds as in (30) proves

\[
 \|P_V(G'(3)-g_3'I-(g_3'-g r)2^{-r}A_V)P_V\|
 =O_{\mathbb P}(L^4/n).
\tag{35}
\]

The marked block of Gamma is exactly

\[
 \Gamma_M=-\tfrac18\left(6(G-gI)+9(G'(3)-g_3'I)+J/n\right).
\tag{36}
\]

Substitute (30), (35), `6g+9g_3'=-6`, and `w=3*2^(-r)/(4s)`. This yields

\[
 P_V\Gamma_M P_V=s(r+1)w A_V+o_{\mathbb P}(sr).
\tag{37}
\]

The collective derivative quadratic is much smaller. Apply the old nonnegative ordinary-walk argument to `e^T(G'(3)-g_3'I)e`, instead of bounding the full operator. The averaged diagonal part has expectation `O(L^4/n)`, the off-diagonal part has expectation `O(mL^2/n)`, and the stationary quadratic has the same latter order. Hence

\[
 |e^\top(G'(3)-g_3'I)e|
 =O_{\mathbb P}(L^4/n+mL^2/n)
 =O_{\mathbb P}(s^2L^2)=o_{\mathbb P}(sr).
\tag{38}
\]

Equations (25), (36) and (38) imply `e^T Gamma_M e=o_P(sr)`.

The mixed derivative estimate follows from the same decomposition. Its short selected row is `(g_3'-g r)2^(-r)P_Ve`, of norm `O_P(sr/sqrt(m))`. The weighted selected tail acting on e is at most L times the unweighted bound used for (32). The derivative stationary vector has norm `O_P(sqrt(m)L^2/n)`, and its selected diagonal contribution is bounded by (28). Thus

\[
 \|P_V\Gamma_M e\|=o_{\mathbb P}(sr).
\tag{39}
\]

The full operator derivative bound retained before its coarse simplification is

\[
 \|\Gamma\|=O_{\mathbb P}\left(sL^2+s^2L^4\right)
 =O_{\mathbb P}(sL^2).
\tag{40}
\]

It uses `||G-gI||=O_P(s)`, the all-orders bound for j=1, and `m/n=Theta(s^2)`. Since `||f-e||=O_P(m^(-1/2))`, (40) makes the change from e to f in (38) and (39) `o_P(sr)`. Consequently

\[
 f^\top\Gamma_M f=o_{\mathbb P}(sr),\qquad
 \|P_V\Gamma_M f\|=o_{\mathbb P}(sr).
\tag{41}
\]

## 7. Proof of the corrected retained-operator theorem

Let U be the isometry from (5). The host-to-f coupling in T is `kappa sqrt(1-2p/m)`, which differs from kappa by `O_P(1/m)=o_P(sr)`. Equations (27), (31), and (33) give

\[
 U^\top T U
 =-\kappa I+sr\operatorname{diag}
       \left(-\kappa^2/2,-a I_p\right)+o_{\mathbb P}(sr).
\tag{42}
\]

Equations (37) and (41), and the fact that A_V acts as minus the identity on each a_j, give

\[
 U^\top\Gamma U
 =sr\operatorname{diag}(0,-\kappa I_p)+o_{\mathbb P}(sr).
\tag{43}
\]

The selected column estimates (14), (15), and the exact host star imply

\[
 \|(I-UU^\top)T U\|=O_{\mathbb P}(m^{-1/2}).
\tag{44}
\]

For the collective column, use `||Zf||=O_P(m^(-1/2))`, which follows from (14), `||Z||=O_P(1)` and `||f-e||=O_P(m^(-1/2))`. Its host-star component outside the span of h and f is supported on V and has norm `O_P(m^(-1/2))`. For a selected antisymmetric column the host component vanishes exactly, and (15) controls the remaining error. The tight number of columns preserves the rate.

The error from replacing `U^top Gamma T U` by `(U^top Gamma U)(U^top T U)` has norm at most

\[
 \|\Gamma\|\,\|(I-UU^\top)TU\|
 =O_{\mathbb P}(sL^2/\sqrt m)=o_{\mathbb P}(sr).
\tag{45}
\]

Use (42) and (43) in the product. Its leading term is `-kappa U^top Gamma U`. The product of the two small compressed corrections is negligible. The same reasoning applies to the transposed product. Thus

\[
 U^\top\widehat T U
 =U^\top T U+\kappa U^\top\Gamma U+o_{\mathbb P}(sr).
\]

Equations (42) and (43) prove (6). Finally, `||T||=O_P(1)` and (40) show

\[
 \|(\widehat T-T)U\|=O_{\mathbb P}(sL^2)
 =o_{\mathbb P}(m^{-1/2}).
\]

Together with (44) this proves (7).

## 8. From the compressed block to retained eigenvalues

The complementary gap is handled with a fixed cutoff, followed by increasing that cutoff. For each fixed K, compare T with the short-pair model from the frozen effective theorem. The short marked graph is a matching with high probability, and deleting its finite host couplings changes the model by `O_P(m^(-1/2))`. All nonresonant pair levels have amplitudes `w*2^(-k)` with integer k different from zero. As w tends to kappa, their negative values stay at least a fixed positive distance from `-kappa`. The zeros and all positive levels are also separated.

The negative short-model subspace is spanned by its collective negative vector and the p selected antisymmetric vectors. Its collective vector differs from b_- in (5) by `O_P(m^(-1/2))`, since the difference removes only a tight number of additional nonresonant pair coordinates. The model has a fixed complementary gap around `-kappa` after a small enough fixed window is chosen.

The frozen full-operator tail comparison fails with limiting upper probability at most `C 2^(-K)` at any fixed small error tolerance. Equation (40) gives `||widehat T-T||=o_P(1)`. It follows, by first taking n to infinity for fixed K and then K to infinity, that the compression of widehat T onto the complement of the range of U has a fixed gap around `-kappa` with probability tending to one.

On that gap event, the Schur complement for this block decomposition has self-energy bounded by a constant times the square in (7), uniformly in a fixed neighborhood of `-kappa`. This is `o_P(sr)`. The same inertia and ordered-root comparison used in the frozen deterministic transfer therefore proves that exactly p+1 retained eigenvalues in that neighborhood have logarithmic shifts given by the ordered values

\[
 -\kappa^2/2,\qquad -(a+\kappa^2)
       \text{ with multiplicity }p.
\tag{46}
\]

For a different from `-kappa^2/2`, these form a simple collective level and a p-dimensional pair level when p>0. Their invariant subspaces converge to the corresponding subspaces within (5). This follows by the finite complementary-gap elimination, whose error is `o_P(sr)`, and the positive separation between the two coefficients in (46). It does not select a basis among p repeated pair values.

The comparison probability just described has bound `C 2^(-K)` before the last limit. The claim is not made on a single fixed-K event of probability tending to one without that last step.

## 9. Exact phase, refined tuning and the remaining graph bridge

At exact phase 1/2, condition (2) has a=0. The retained negative collective level is

\[
 -\kappa-\frac{\kappa^2}{2}sr+o_{\mathbb P}(sr),
\]

and the negative pair sector is

\[
 -\kappa-\kappa^2 sr+o_{\mathbb P}(sr).
\]

The latter is lower by `kappa^2 sr/2` to leading order. Thus exact leading-order resonance need not leave the negative collective and pair sectors unresolved. A more finely tuned crossing occurs when `w-kappa` is close to `-kappa^2 sr/2`, which is compatible with the earlier condition `sqrt(m)(w-kappa)->0`.

A separate actual-cluster normalization theorem of the form

\[
 \|A_{\rm eff}-\widehat T\|=o_{\mathbb P}(sr)
\tag{47}
\]

would transfer the retained eigenvalue and separated-subspace conclusions to the graph. The proposed bound `O_P(||Gamma||^2+s)` is sufficient for (47), because (40) gives `s^2L^4=o(sr)` and r tends to infinity. This file does not prove the isometry construction or (47). It identifies the exact probability input and verifies that its needed rates are available.

No assertion is made about a universal negative law at the smaller 1/m scale, the basis inside the p-dimensional pair sector, or the exactly retuned logarithmic crossing `a=-kappa^2/2`. No spatial localization conclusion is inferred here. The result is a paper argument for explicit graph-derived retained matrices, not an end-to-end formalization.

## 10. Requested review

Check the nonpositive disjoint-pair covariance in (18), the cancellation of L and survival of `-s^2 r` in (25), the selected diagonal estimate (28), the sign and factor in the derivative block (37), and the use of the corrected operator (4). Review should separately verify the complementary-gap argument and preserve the explicit graph-normalization bridge (47).
