# A simple resonant channel for nonseparable polynomial ports

Date: November 15, 2026. Revision 1, frozen for separate review.

Status: paper theorem using the frozen marked-resolvent and marked-pair premises listed in Section 8. It does not claim a new Schur identity or a direct nonnormal edge-operator estimate.

Exposure: the scalar-port route `route-v1.md` was frozen independently before the root scalar-port theorem was read. The latter was then reviewed. This extension was proposed and authorized after that exchange. No live probability attempt from this round was read before freezing this proof.

## 1. Model and hypotheses

Fix d>=3, q=d-1, a real symmetric k by k matrix C, fixed real polynomials p_1,...,p_t and fixed vectors b_1,...,b_t in R^k. Write the vector polynomial

\[
 b(x)=\sum_{a=1}^t p_a(x)b_a.
\tag{1}
\]

The letters b_a are coefficient vectors, while b(x) is their polynomial combination. All local data are fixed as n grows. Let A be a uniform simple labelled d-regular adjacency matrix, and let E select m predetermined distinct host labels. Define the host-to-motif map B by

\[
 B(y_1,\ldots,y_m)=
 \sum_{a=1}^t p_a(A)E
       (b_a^Ty_1,\ldots,b_a^Ty_m)^T,
\]

and the augmented symmetric operator

\[
 \mathcal A=\begin{pmatrix}A&B\\B^T&I_m\otimes C\end{pmatrix}.
\tag{2}
\]

Unlike a scalar filtered port, the different motif directions may couple through different polynomials. In general b(x) is not a fixed vector times one scalar polynomial.

Let nu_d be the root spectral measure of the infinite d-regular tree. For z in a fixed neighborhood of d, define the matrix self-energy

\[
 K_*(z)=\int \frac{b(x)b(x)^T}{z-x}\,d\nu_d(x).
\tag{3}
\]

Assume

\[
 K_0=dI-C-K_*(d)\succeq0,\qquad
 \ker K_0=\operatorname{span}(v),\qquad \|v\|=1,
\tag{4}
\]

and beta=b(d)^Tv is nonzero. Choose the sign of v so beta>0. The remaining k-1 eigenvalues of K_0 have a fixed positive lower bound when k>1. Put

\[
 p_v(x)=b(x)^Tv,\qquad
 g_v(z)=\int\frac{p_v(x)^2}{z-x}\,d\nu_d(x),
\]

\[
 D=1-g_v'(d)>1,\qquad
 \kappa=\frac\beta{\sqrt D},\qquad
 h=g_d(d)\kappa^2.
\tag{5}
\]

The local hypotheses imply dI-C is positive definite. Indeed K_*(d) is positive semidefinite. A null vector of K_0+K_*(d) would lie in span(v) and satisfy g_v(d)=0. This is impossible since p_v is a nonzero polynomial. Thus no internal motif eigenvalue at or above d is concealed by the local calibration.

## 2. The theorem

Let m/n^(1/3) tend to c>0 and s=sqrt(m/n). On the fixed host-gap event write u=n^(-1/2)1, Q=I-uu^T and R_Q(z) for the resolvent on u perpendicular, extended by zero on u. Define

\[
 G_v(z)=E^Tp_v(A)R_Q(z)p_v(A)E,
\]

\[
 T_n=\begin{pmatrix}
 0&\kappa e^T\\
 \kappa e&(G_v(d)-g_v(d)I)/(Ds)
 \end{pmatrix},\qquad e=m^{-1/2}1.
\tag{6}
\]

There is a fixed epsilon>0 such that, with probability tending to one, exactly the largest m+1 eigenvalues of (2) lie in (d-epsilon,d+epsilon). Every other eigenvalue is at most d-epsilon. Write P_n for the corresponding projection. Let

\[
 J_n(\alpha,y)=
 \left(\alpha u+R_Q(d)p_v(A)Ey/\sqrt D,
       y\otimes v/\sqrt D\right).
\tag{7}
\]

There is an isometry U_n onto range(P_n) such that, for

\[
 a_n=s+\frac{m\log^4n+m^2\log^2n}{n},
\]

\[
 \|U_n-J_n\|=O_P(a_n),\qquad
 \|U_n^T(\mathcal A-dI)U_n/s-T_n\|=O_P(a_n)
        =o_P(m^{-1/2}).
\tag{8}
\]

For each fixed K, the largest m+1 eigenvalues, after centering at d and division by s, are approximated in decreasing order by the multiset

\[
 \{\kappa,-\kappa\}
 \cup\bigcup_{\{i,j\}:\ell_{ij}\le r_n+K}
 \{h q^{-\ell_{ij}}/s,-h q^{-\ell_{ij}}/s\}
 \cup\{0\text{ with multiplicity }m-2p-1\},
\tag{9}
\]

where r_n=floor(log_q(1/s)), ell_ij is host distance and p is the number of short marked pairs. This graph of short pairs is a matching with probability tending to one. For every eta>0, the limsup probability of ordered error exceeding eta is at most C eta^(-2)q^(-K). The constants are independent of m and of the predetermined mark labels.

Consequently the same critical distance-phase law holds. Along phi_n=log_q(1/s)-r_n tending to phi, its signed point measure away from zero is

\[
 \delta_\kappa+\delta_{-\kappa}
 +\sum_{j\in\mathbb Z}P_j
  (\delta_{h q^{\phi-j}}+\delta_{-h q^{\phi-j}}),
\tag{10}
\]

where the P_j are independent Poisson variables of means d c^(3/2)q^(j-phi)/(2q). The paired signs and deterministic atoms mean that the complete measure is not Poisson.

The mass forms for a retained unit vector (alpha,y) are, uniformly after applying U_n,

\[
 \bigl(\text{constant host},\text{all motifs},\text{host complement}\bigr)
 =\left(\alpha^2,\frac{\|y\|^2}D,
                 \frac{D-1}D\|y\|^2\right)+o_P(1).
\tag{11}
\]

The same isolated-level projector argument transfers whole pair and collective level subspaces. It retains full multiplicities and makes no choice of basis in a repeated level.

## 3. Exact matrix polynomial identity

Set G_E(z)=E^TR_Q(z)E and

\[
 K_n(z)=B^T R_Q(z) B.
\]

Here the tensor ordering is mark first and motif coordinate second. Define the symmetric matrix polynomial

\[
 R_z(x)=\frac{b(z)b(z)^T-b(x)b(x)^T}{z-x}.
\tag{12}
\]

On the event that the required fixed-radius marked balls are trees and distinct marks are farther apart than twice the largest polynomial degree, polynomial locality gives the exact identity

\[
 \Delta_n(z):=K_n(z)-I_m\otimes K_*(z)
 =(G_E(z)-g_d(z)I_m)\otimes b(z)b(z)^T
      +(J_m/n)\otimes R_z(d).
\tag{13}
\]

Its proof is entrywise polynomial division for each p_a(x)p_b(x), followed by compression on Q. The last sign is positive, exactly as for scalar filtered ports. The event has failure probability O((m+m squared)/n) and is independent of z. Differentiating (13) is therefore valid on the same event. The finite number of coefficient matrices has bounded norms, so the prior estimates yield

\[
 \|\Delta_n(d)\|=O_P(s),\qquad
 \|\Delta_n'(d)\|=O_P(a_n).
\tag{14}
\]

The stationary matrix is explicit:

\[
 R_d(d)=b'(d)b(d)^T+b(d)b'(d)^T.
\tag{15}
\]

Projection onto v in (13) recovers exactly the scalar filtered identity for p_v. Thus G_v-g_v I=O_P(s) and G_v'-g_v'I=O_P(a_n). These are estimates uniform over predetermined marks, not estimates simultaneously over every subset of a realized graph.

## 4. Positive local channels and the actual top cluster

Eliminating the positive host complement from zI-mathcal A leaves the symmetric Schur block

\[
 S_n(z)=
 \begin{pmatrix}
 z-d&-1_m^T\otimes b(d)^T/\sqrt n\\
 -1_m\otimes b(d)/\sqrt n&F_n(z)
 \end{pmatrix},
\quad F_n(z)=I_m\otimes(zI-C)-K_n(z).
\tag{16}
\]

F_n(d)=I_m tensor K_0+O_P(s). Its derivative is at least the identity, since K_n'(z)=-B^TR_Q(z)^2B is negative semidefinite. Both its derivative norm and second derivative norm are bounded on a fixed small interval by the fixed host gap and ||B||<=sum_a ||p_a||_infinity ||b_a||.

At d+epsilon, F_n is at least epsilon/2 with probability tending to one. At d-epsilon, its restriction to R^m tensor v is at most -epsilon/2. The other eigenvalues remain positive with a fixed gap by Weyl's inequality, after choosing epsilon small relative to the positive spectrum of K_0. Thus exactly m eigenvalues of F_n(d-epsilon) are negative and none approach zero. The host-to-motif vector has norm ||b(d)||s=o(1). The two endpoint Schur blocks therefore have m+1 and zero negative eigenvalues. Exact inertia proves the stated largest-cluster count and complementary gap.

There is also an explicit quadratic correction from the nonresonant channels. For z=d+sx with x in a fixed bounded interval, split the motif coordinates into R^m tensor v and its orthogonal complement. The latter block has inverse of bounded norm. Its off-diagonal coupling to the retained constant host and local resonant coordinates is O_P(s). Eliminating it therefore subtracts a Schur term of norm O_P(s squared). This remains O_P(s squared) uniformly on that x interval. The retained kernel block before that subtraction is exactly

\[
 z-v^TCv-G_v(z),
\]

and its scalar tree derivative at d is D. Thus the extra positive channels do not create a new order-s interaction. The next section establishes a stronger physical-space statement without discarding this quadratic correction informally.

## 5. Exact compressed energy and approximate invariance

Put H=mathcal A-dI and

\[
 V_n(\alpha,y)=(\alpha u,\sqrt D\,y\otimes b(d)/\beta).
\]

The norm of V_n is bounded independently of m. Define

\[
 w=\beta b'(d)-p_v'(d)b(d).
\tag{17}
\]

Its inner product with v is zero. Direct multiplication using K_0v=0 and (13) gives

\[
 HJ_n=sV_nT_n+W_n,\qquad
 W_n(\alpha,y)=\left(0,(J_m y/n)\otimes w/\sqrt D\right).
\tag{18}
\]

In particular ||W_n||=O(s squared), J_n^TW_n=0 and J_n^TV_n=I. Hence

\[
 J_n^THJ_n=sT_n
\tag{19}
\]

is exact, despite the nonseparable port. The motif component of HJ_n before simplifying is b(d) alpha 1_m/sqrt(n) plus Delta_n(d)(y tensor v)/sqrt(D). Substitution of (13) and (15) gives (18), including the direction and sign of w.

The Gram identity is also exact:

\[
 J_n^TJ_n=\operatorname{diag}(1,[I-G_v'(d)]/D)
          =I+O_P(a_n).
\tag{20}
\]

Since ||T_n||=O_P(1), equations (18) and (20) give ||HJ_n||=O_P(s). On the complementary spectral subspace H has a bounded inverse, so ||(I-P_n)J_n||=O_P(s). Let M_n=J_n^TP_nJ_n. It equals I+O_P(a_n+s squared). Thus

\[
 U_n=P_nJ_nM_n^{-1/2}
\]

is an isometry onto the cluster. Rank equality uses the inertia count from Section 4. Its distance from J_n is O_P(a_n+s)=O_P(a_n). Moreover

\[
 \|J_n^T(I-P_n)H(I-P_n)J_n\|
 \le\|(I-P_n)J_n\|\,\|(I-P_n)HJ_n\|=O_P(s^2).
\]

Combining this with (19) and the inverse-square-root normalization gives (8). There is no factor of m in the argument. At criticality a_n=O(n^(-1/3)log squared(n))=o(m^(-1/2)).

Equation (20) and the explicit motif component of J_n give (11). This is a physical mass statement, not merely the metric of an abstract pencil.

## 6. Pair law and one nonseparable example

The bottom block of T_n uses only p_v. Apply the exact scalar consequence of (13) and the frozen whole marked-space tail estimate. Its propagation coefficient is p_v(d) squared times g_d(d), divided by D, which is h. The stationary correction divided by s is O(s). For fixed K, delete the star entries at the tight number of short-pair endpoints and use the matching decomposition. The cost tends to zero. Weyl's inequality and (8) prove (9). The frozen two-sided truncation and Poisson counts then prove (10). The projector statement follows by the same contour bound as the earlier critical-subspace theorem. No independence of motif entries is assumed.

A concrete nonnegative weighted example has d=3, k=2 and

\[
 b(x)=(1,x/2)^T,\qquad
 C=\begin{pmatrix}0&c_0\\c_0&0\end{pmatrix},\qquad
 c_0=(\sqrt{21}-1)/2.
\]

The first new vertex couples to the marked host vertex with weight one. The second couples to each of its three neighbors with weight one half. The two new vertices are joined by weight c_0. These two host coupling patterns cannot be written as one scalar polynomial times one fixed vector.

Tree moments give

\[
 K_*(3)=\begin{pmatrix}2/3&1/2\\1/2&3/4\end{pmatrix},
\qquad
 K_0=\begin{pmatrix}7/3&-\sqrt{21}/2\\-\sqrt{21}/2&9/4\end{pmatrix}.
\]

Its eigenvalues are zero and 55/12. Its unit kernel is

\[
 v=(3\sqrt3,2\sqrt7)^T/\sqrt{55},\qquad
 p_v(x)=(3\sqrt3+\sqrt7 x)/\sqrt{55}.
\]

Therefore

\[
 D=(134+16\sqrt{21})/55,\qquad
 \kappa^2=(90+18\sqrt{21})/(134+16\sqrt{21}),\qquad
 h=2\kappa^2/3.
\tag{21}
\]

The internal top eigenvalue c_0 is strictly below 3. This example is weighted and is not presented as an unweighted graph. The separate scalar theorem already supplies two genuinely different unweighted examples. The present example specifically tests nonseparability of the port vectors.

## 7. Scope and route decision

This theorem allows several polynomial coupling directions at one marked center with one simple local critical channel. The propagation still reduces to a scalar because only one local channel is resonant. It does not cover independently oriented host ports, arbitrary irregular hosts, growing local dimensions or multiple local critical channels.

The degree-corrected Bethe-Hessian identity in `route-v1.md` remains valid for the unweighted cases, but it has not improved the critical error. The selected route is now the self-adjoint local-channel reduction. The term W_n in (18) is an explicit example of an error that vanishes in a separable port and survives at order s squared in the broader class. It cannot be ignored in a theorem aiming at finer physical order-s-squared effects.

## 8. Frozen premises

The marked derivative theorem is `growing-defects-round-01/probability/proof-v1.md`, SHA256 `56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b`. The nonbacktracking bound is `close-pair-transition-round-01/root/nonbacktracking-upper-v1.md`, SHA256 `d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896`.

The whole-space pair approximation is `critical-law-round-01/root/effective-operator-v1.md`, SHA256 `13b559897d6ed9253a2fc6dd4dede5dd03914c078558d759542afc9c54d28864`. The pair-count premise is `critical-law-round-01/probability/pair-counts-v1.md`, SHA256 `702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29`. The limiting-law argument is `critical-law-round-01/root/critical-law-v1.md`, SHA256 `e379a0b55e81925276d2c3046ec1cc4b25c21e028d22fef53516f4b5828e48f3`. The contour and physical-subspace argument is `critical-subspaces-round-01/root/subspaces-v1.md`, SHA256 `f13fbd47ba04bd638f4bafe940c20d604bfa4a4653df553b4b737f2e3779e87a`.

No infinite-tree calculus, asymptotic probability theorem or physical subspace theorem in this extension is asserted to have been formally encoded. Priority for general local-channel reduction is not claimed.
