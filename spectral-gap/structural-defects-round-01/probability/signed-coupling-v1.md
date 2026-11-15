# Vanishing signed coupling at the retuned negative crossing

November 15, 2026. Owner: probability workstream. Revision 1, frozen for separate review.

## 1. Statement and exact graph objects

Use the cubic neighbourhood-duplication model, fixed host-gap event and notation of collective-limit-v1.md, SHA256 e492d3dfa506167ba28782e316129146e72f8046e96bbaf50b265e42d3fc307d. In particular m/n^(1/3)->c>0, s=sqrt(m/n), r=floor(log_2(1/s)), and kappa=3/sqrt(8). Put

\[
 w=\frac34\,2^{-r}/s,\qquad
 \beta_n=\frac{w-\kappa+(\kappa^2/2)sr}{s}.
\tag{1}
\]

Assume beta_n tends to a finite real beta. This is the finer tuning inside the previously identified logarithmic crossing.

Let p_n count marked pairs at distance r. Condition only in the final conclusions on p_n=1, whose probability has a positive limit. Before that conditioning all sampling and walk estimates remain unconditional. On the high-probability matching event let V={a,b} be those two marked coordinates, let f be the unit constant vector on the other marked coordinates, and put

\[
 c_-=(h-f)/\sqrt2,\qquad a_-=(e_a-e_b)/\sqrt2.
\tag{2}
\]

Here h is the retained host coordinate. Let U_- be the isometry with these two columns, and put P=U_-U_-^top and Q_-=I-P. The sign choice of a_- will not matter.

Let B=A E, let F(z)=zI-B^top R_Q(z)B be the exact pole-free Schur block, and define the energy-dependent real symmetric retained matrix

\[
 \mathcal T_n(x)=
 \begin{pmatrix}
 0&\kappa e^\top\\
 \kappa e&xI-F(3+sx)/(8s)
 \end{pmatrix}.
\tag{3}
\]

The exact retained Schur equation for the actual graph eigenvalues at z=3+sx is

\[
 \det(xI-\mathcal T_n(x))=0.
\tag{4}
\]

Indeed, eliminate the host subspace perpendicular to its constant vector, then apply the congruence diag(1,8^(-1/2)I) and divide by s. The retained host-to-marked vector is 3s e, producing the coefficient kappa in (3). Thus (3) is a graph-derived pencil, not an arbitrary perturbation model.

Set

\[
 x_n^0=-\kappa-\frac{\kappa^2}{2}sr.
\tag{5}
\]

For each fixed M, on an event of conditional probability tending to one, the complementary inverse exists with a fixed norm bound uniformly for |x-x_n^0|<=Ms. Define the exact two-dimensional Schur matrix

\[
 \mathcal B_n(x)=U_-^\top\mathcal T_n(x)U_-
 +U_-^\top\mathcal T_n(x)Q_-
   (xI-Q_-\mathcal T_n(x)Q_-)^{-1}
   Q_-\mathcal T_n(x)U_-.
\tag{6}
\]

The inverse is understood on the range of Q_-. Arbitrary extensions off its good event do not affect the probability assertions.

**Theorem 1.** Conditional on p_n=1, uniformly for |x-x_n^0|<=Ms,

\[
 (\mathcal B_n(x))_{12}=o_{\mathbb P}(s),
\tag{7}
\]

\[
 (\mathcal B_n(x))_{22}
 =x_n^0+s(33/16-\beta_n)+o_{\mathbb P}(s).
\tag{8}
\]

There is a tight real random variable L_n such that

\[
 (\mathcal B_n(x))_{11}=x_n^0+sL_n+o_{\mathbb P}(s),
\tag{9}
\]

uniformly on the same interval. One explicit choice, up to an o_P(1) error, is

\[
 L_n=\frac{\kappa^2}{2}C_n+\frac{63}{32}
       +\frac{\Sigma_{n,11}(x_n^0)}s,
\tag{10}
\]

where C_n is the collective quadratic from collective-limit-v1.md and Sigma_n is the second term in (6). That last complementary correction is O_P(s), so it cannot be omitted.

Moreover,

\[
 \sup_{|x-x_n^0|\le Ms}
 \|\mathcal B_n(x)-\mathcal B_n(x_n^0)\|
 =o_{\mathbb P}(s).
\tag{11}
\]

Thus the leading two-dimensional matrix at this scale is diagonal up to a vanishing error. The theorem does not yet identify the law of L_n. If its limit can coincide with 33/16-beta, a still finer analysis would be needed on that coincidence event. No generic avoided crossing or pure eigenvector law is inferred merely from (7).

## 2. Exposure and frozen premises

This workstream authored the probability inputs and the compensated collective theorem. It previously read and reviewed the frozen graph normalization and finite resonance proofs. During this round it received the task to test signed coupling and chose the exact energy-dependent Schur route. No live structural or root attempt from this round was read before freezing this file.

The main frozen inputs are:

- collective-limit-v1.md, SHA256 e492d3dfa506167ba28782e316129146e72f8046e96bbaf50b265e42d3fc307d.
- critical-subspaces-round-01/probability/refined-resolvent-v1.md, SHA256 bd00db6c2f69813d480f5a86d5d22c8b6fe4922d9cc3d233f72840dddb29f8df.
- critical-subspaces-round-01/probability/negative-log-scale-v1.md, SHA256 faced6a02d91d451e4ef0e0989d3d46811da66d809d40e9344e9444012901409.
- critical-subspaces-round-01/root/subspaces-v1.md, SHA256 f13fbd47ba04bd638f4bafe940c20d604bfa4a4653df553b4b737f2e3779e87a.
- critical-subspaces-round-01/root/graph-resonance-v2.md, SHA256 907d90af7ea1af8a59ec49c100869046e01e3ffd251e81a55239a054bb59f289.

The earlier all-orders marked-resolvent estimate, nonbacktracking two-walk bound and pair-count theorem have the hashes recorded in collective-limit-v1.md. The coefficient calculations below are derived explicitly. A bounded symbolic differentiation check corroborated g''(3)=172/27 and the scalar Schur second derivative -136/3, but the proof does not depend on that computation.

## 3. The selected residual column is smaller than its former bound

Fix K>=0, write R=r+K, and let U_R and T_R be the nonnegative nonbacktracking tail and its marked off-diagonal compression. The selected endpoint set V is defined by distance r and does not depend on K.

The previous proof splits selected tail columns into own-partner entries and three-distinct-endpoint entries. Its estimates retain the dependence on K:

\[
 \sum_{\text{selected own partners}}(T_R)_{uv}
 =O_{\mathbb P}(L^3/n),
\tag{12}
\]

and

\[
 \mathbb E\left[
  \mathbf1_{M_R}
  \|\text{remaining selected columns of }T_R/s\|_F^2
 \right]
 \le C\left(\frac{2^{-K}}m+\frac{L^4}{m^3}\right).
\tag{13}
\]

Here L is a sufficiently large fixed multiple of log n and M_R is the short-matching event. To verify (13), the bound is p_3 C2^r times
n2^(-R)+L^4, divided by s squared. Since n=Theta(m^3), 2^r=Theta(m), and s=Theta(1/m), its two contributions have exactly the displayed orders. The constants are independent of K. Each fixed-K exceptional matching and short-path probability tends to zero.

The squared own-partner Frobenius norm is at most the squared sum in (12). After division by s squared and multiplication by m, that is O_P(L^6/m^3), which vanishes. The diagonal and stationary auxiliary operator has norm O_P(L^3/m), whose square multiplied by m also vanishes. The projected series tail is smaller still.

On M_R, the short matrix acts on V as exactly 2^(-r) times its pair adjacency A_V. It has no other short edge incident to V. For

\[
 Z=-F(3)/(8s),
\]

the stationary additional rank-one term has norm O(s), and direct marked edges are absent with probability tending to one. Consequently, for every eta>0,

\[
 \limsup_n\mathbb P\left\{
  m\|(Z-wA_V)P_V\|^2>\eta\right\}
 \le C\eta^{-1}2^{-K}.
\tag{14}
\]

The left side is independent of K. Sending K to infinity after n proves

\[
 \|(Z-wA_V)P_V\|^2=o_{\mathbb P}(1/m)
 =o_{\mathbb P}(s).
\tag{15}
\]

These are unconditional estimates with a tight selected pair count. Restricting to p_n=1 is legitimate only afterwards. No growing-cutoff estimate has been used.

The earlier collective-column argument gives

\[
 \|Ze\|=O_{\mathbb P}(m^{-1/2}),\qquad
 \|Z\|=O_{\mathbb P}(1).
\tag{16}
\]

As ||f-e||=O_P(m^(-1/2)), the same bound holds for Zf.

## 4. Direct signed compression at order s

The raw selected constant-block estimates in the logarithmic proof are sharper than its final logarithmic statement:

\[
 \|P_V(G-gI-g2^{-r}A_V)P_V\|
 =O_{\mathbb P}(L^3/n).
\tag{17}
\]

After division by s this gives

\[
 P_V ZP_V=wA_V+o_{\mathbb P}(s).
\tag{18}
\]

The mixed selected-tail estimate from three-endpoint sampling gives, in scaled coordinates, O_P(m^(-3/2)L+m^(-5/2)L^3). The maximum-diagonal estimate acting on P_Ve contributes at most O_P(m^(-3/2)L^3). The stationary selected vector is smaller. Therefore

\[
 P_VZe=wP_Ve+o_{\mathbb P}(s).
\tag{19}
\]

Let v=e_a+e_b and let delta=m^(-1/2). The exact formula

\[
 f=\frac{e-\delta v}{\sqrt{1-2/m}}
\tag{20}
\]

and the identities e^top a_-=v^top a_-=0 now imply

\[
 f^\top Za_-=o_{\mathbb P}(s).
\tag{21}
\]

Indeed, the e term uses (19), and the v term uses (18). The leading pair adjacency sends a_- to -a_-, so it cancels in both inner products. A norm bound alone would not give (21). The signed cancellation is necessary.

The host-star entry of T against a_- is zero exactly. Thus the direct collective-to-antisymmetric entry of T is o_P(s), while its entire perpendicular column at a_- has norm o_P(sqrt(s)) by (15).

## 5. Energy dependence computes the order-s analytic term

Write

\[
 \Gamma=\operatorname{diag}(0,F'(3)/8-I),\qquad
 P_M=\operatorname{diag}(0,I_m).
\]

The finite derivative estimates give

\[
 \|\Gamma\|=O_{\mathbb P}(sL^2)=o_{\mathbb P}(\sqrt s).
\tag{22}
\]

The j=2 marked-resolvent estimate gives G''(3)-g_3''(3)I=o_P(1). Together with its j=0 and j=1 versions and the exact cubic identity

\[
 F(z)=2zI-z^2G(z)+A_C-(z+3)J/n,
\]

this yields F''(3)-f''(3)I=o_P(1), where

\[
 f(z)=2z-z^2g_3(z).
\]

To compute the scalar, let rho(z)=(z-sqrt(z squared-8))/4 and g_3(z)=rho(z)/(1-rho(z) squared). Differentiation of
2rho squared-z rho+1=0 gives rho(3)=1/2, rho'(3)=-1/2, and rho''(3)=2. Hence

\[
 g_3(3)=2/3,\qquad g_3'(3)=-10/9,\qquad
 g_3''(3)=172/27,
\]

and

\[
 f''(3)=-2g_3(3)-12g_3'(3)-9g_3''(3)=-136/3.
\tag{23}
\]

All fixed local derivatives of F have dimension-independent operator bounds on H_n. Taylor expansion, uniformly for bounded x, therefore gives the actual pencil identity

\[
 \mathcal T_n(x)=T-x\Gamma+\frac{17}{6}s x^2P_M
                  +o_{\mathbb P}(s).
\tag{24}
\]

The coefficient 17/6 is -f''(3)/16. This order-s term was legitimately discarded at logarithmic precision, but is retained here. Equation (24) follows from the exact Schur pencil, so it does not assume an unproved sharper graph-cluster normalization.

The raw selected derivative estimate gives

\[
 P_V\Gamma P_V=s(r+1)wA_V+O_{\mathbb P}(L^4/n).
\tag{25}
\]

Its error is o_P(s). The previous mixed calculation gives
||P_V Gamma e||=O_P(sr/sqrt(m))+o_P(s), which is o_P(s). Replacing e by f costs at most
||Gamma|| ||f-e||=O_P(sL^2/sqrt(m))=o_P(s). Therefore

\[
 f^\top\Gamma f=o_{\mathbb P}(s),\qquad
 f^\top\Gamma a_-=o_{\mathbb P}(s).
\tag{26}
\]

For the first assertion, the earlier ordinary-walk quadratic estimate is
e^top Gamma e=O_P(s^2L^2), and the same replacement bound applies.

## 6. The two direct diagonal coefficients

Since A_Va_-=-a_-, equations (18), (24), and (25) imply, uniformly on the interval of the theorem,

\[
 a_-^\top\mathcal T_n(x)a_-
 =-w-\kappa s(r+1)w+\frac{17}{6}\kappa^2s
       +o_{\mathbb P}(s).
\]

Here x=-kappa+O(sr), and replacing x and w by -kappa and kappa in the indicated correction coefficients costs O(s squared r squared)=o(s). Substituting (1) gives

\[
 a_-^\top\mathcal T_n(x)a_-
 =x_n^0+s\left(\frac{11}{6}\kappa^2-\beta_n\right)
      +o_{\mathbb P}(s)
 =x_n^0+s(33/16-\beta_n)+o_{\mathbb P}(s).
\tag{27}
\]

For the collective diagonal, equations (18)-(20) give

\[
 f^\top Zf=e^\top Ze-2w/m+o_{\mathbb P}(s).
\tag{28}
\]

The normalization factor in (20) changes e^top Ze by o_P(s), because e^top Ze=O_P(sr). The mixed term is -4w/m to leading order and the selected v quadratic is +2w/m. The host-star contribution is
-kappa sqrt(1-2/m)=-kappa+kappa/m+o(s). Since (kappa-w)/m=o(s),

\[
 c_-^\top T c_-=-\kappa+\tfrac12 e^\top Ze+o_{\mathbb P}(s).
\tag{29}
\]

On the high-probability event of no marked edge, the exact marked block is

\[
 Z=\frac9{8s}(G-gI)+\frac3{4ns}J.
\tag{30}
\]

Thus

\[
 e^\top Ze=-\kappa^2sr+s(\kappa^2 C_n+3/4).
\tag{31}
\]

The Gamma term in (24) is negligible on c_- by (26), and c_-^top P_M c_-=1/2. Equations (24), (29), and (31) yield

\[
 c_-^\top\mathcal T_n(x)c_-
 =x_n^0+s\left(\frac{\kappa^2}{2}C_n+\frac{63}{32}\right)
       +o_{\mathbb P}(s).
\tag{32}
\]

The collective quadratic theorem makes this centered coefficient tight, also after conditioning on p_n=1.

## 7. The complementary gap and induced signed coupling

The frozen logarithmic retained-matrix proof supplies a fixed complementary gap about -kappa for the negative reference space spanned by c_- and a_-. Its proof uses each fixed short cutoff, the matching decomposition, and a limiting failure bound C2^(-K), followed by K tending to infinity. The reference space depends only on the distance-r pair, not on K.

By (22) and (24), the energy-dependent matrix differs by o_P(1) from the retained comparison used in that proof. Since x_n^0 tends to -kappa, the inverse in (6) therefore has a fixed norm bound with probability tending to one, uniformly on the stated interval. This step does not assert such a gap on one fixed-K event of probability tending to one without the final cutoff limit.

Equations (15), (21), (22), and (24) give

\[
 \|Q_-\mathcal T_n(x)a_-\|=o_{\mathbb P}(\sqrt s),
\qquad
 \|Q_-\mathcal T_n(x)c_-\|=O_{\mathbb P}(\sqrt s),
\tag{33}
\]

uniformly in that interval. The direct off-diagonal is o_P(s) by (21), (26), and the exact orthogonality f^top a_-=0 for P_M.

Cauchy-Schwarz and the complementary inverse bound now show that the induced off-diagonal in (6) is o_P(s). Its pair diagonal is also o_P(s). Its collective diagonal is O_P(s). Combining these facts with (27) and (32) proves (7)-(10). The vanishing in (7) therefore includes the actual complementary correction, not only the direct star entry.

## 8. Dependence on the energy parameter

Differentiating (3) gives

\[
 \mathcal T_n'(x)=\operatorname{diag}(0,I-F'(3+sx)/8).
\]

The local derivative bounds and (22) imply

\[
 \sup_{|x-x_n^0|\le Ms}\|\mathcal T_n'(x)\|
 =O_{\mathbb P}(sL^2).
\tag{34}
\]

Its variation over the interval is o_P(s). Differentiate the complementary inverse in (6). Its derivative is the negative of the inverse, multiplied by
I-Q_- mathcal T_n'(x) Q_-, multiplied by the inverse. This has bounded operator norm on the good event.

The two coupling columns have norm O_P(sqrt(s)), and their derivatives have norm O_P(sL^2). Consequently the derivative of Sigma_n is
O_P(s+s^(3/2)L^2)=O_P(s), uniformly on the interval. Its variation is O_P(s squared)=o_P(s). This proves (11).

## 9. What this proves and what remains

The theorem rules out a nonzero leading signed mixing coefficient at order s in this actual graph pencil, on the positive-probability event of one resonant pair. It does not assert that the exact graph coupling is identically zero.

The pair diagonal coefficient is deterministic once beta is fixed. The collective coefficient contains the compensated quadratic fluctuation and a complementary-space correction of the same order. Its final law is not supplied by the quadratic theorem alone. Establishing that law, and whether it has atoms at the pair coefficient, is the remaining next-scale obligation.

If the two limiting diagonals are distinct, standard finite-dimensional projector perturbation would select separate collective and pair directions. If they coincide, the vanishing order-s coupling leaves finer behavior unresolved. These alternatives are kept separate.

Requested review: reconstruct the fixed-K to K-infinity improvement in (14)-(15), the signed cancellation in (21), the coefficient -136/3 and the energy-dependent expansion (24), both constants in (27) and (32), and the complementary cross estimate. The actual graph connection is the exact Schur equation (4), not an arbitrary matrix perturbation example.
