# A uniform interaction theorem for filtered single-port attachments

Date: November 15, 2026. Revision 1, frozen for separate review.

Status: complete paper argument conditional only on the frozen marked-resolvent and marked-pair theorems specified below. The direct Hashimoto route is assessed separately in Section 7. No new nonbacktracking identity or general perturbation principle is claimed.

Prior exposure: the accepted growing-defect, close-pair, critical-law and critical-subspace rounds were read before this attempt. The author developed a finite resonance calculation and reviewed several of those proofs. During this attempt the integrator reported having a separate filtered-port theorem, but its statement and proof were not read before this file was frozen. All derivations below use the displayed model and the frozen prior inputs.

## 1. Model and local resonance criterion

Fix d>=3, q=d-1, a real polynomial f, a real symmetric k by k matrix C and a nonzero vector b in R^k. These data do not depend on n. Let A be the adjacency of a uniform simple labelled d-regular graph, and let E select m predetermined distinct marks, with m/n^(1/3) tending to c>0. Put s=sqrt(m/n), u=n^(-1/2)1 and Q=I-uu^T.

At each mark attach a k-dimensional gadget with internal matrix C and port vector b. The augmented real symmetric matrix is

\[
 \mathcal A_n=
 \begin{pmatrix}
 A& f(A)E\otimes b^\top\\
 E^\top f(A)\otimes b&I_m\otimes C
 \end{pmatrix}.
\tag{1}
\]

Here a block column at mark i maps a gadget vector y_i to f(A)e_i times b^T y_i. This defines the block notation in (1). General data can give weighted matrices. The examples below are ordinary unweighted graph attachments.

Let A_tree be the adjacency on the infinite d-regular tree and define

\[
 g_f(z)=\langle\delta_o,f(A_{\rm tree})(zI-A_{\rm tree})^{-1}
 f(A_{\rm tree})\delta_o\rangle.
\]

Assume f(d) is nonzero and the local matrix

\[
 K_0=dI_k-C-g_f(d)bb^\top
\tag{2}
\]

is positive semidefinite with a one-dimensional kernel. Choose a unit kernel vector v and put beta=b^T v. Assume beta is nonzero, and choose its sign so beta f(d)>0. Define

\[
 D=1-\beta^2g_f'(d),\qquad
 \kappa=\frac{\beta f(d)}{\sqrt D},\qquad
 h=\frac{\beta^2f(d)^2g_d(d)}D=g_d(d)\kappa^2,
\tag{3}
\]

where g_d is the ordinary tree diagonal resolvent. Since g_f'(d) is negative, D>1.

Condition (2) is a local simple critical resonance with all other local channels separated below d. When dI-C is positive definite, it is equivalent to

\[
 g_f(d)b^\top(dI-C)^{-1}b=1.
\tag{4}
\]

Indeed, conjugate (2) by (dI-C)^(-1/2). The result is the identity minus a rank-one matrix. Conversely, the assumptions in (2), including beta nonzero, imply dI-C is positive definite. A vector in the kernel of K_0+g_f(d)bb^T would have to lie in the kernel of K_0 and be orthogonal to b, which is impossible.

## 2. Uniform theorem at critical growing rank

Write R_Q(z)=Q(zI-A restricted to u-perpendicular)^(-1)Q on the fixed two-sided host-gap event. Set

\[
 G_f(z)=E^\top f(A)R_Q(z)f(A)E,
\]

\[
 \mathcal T_n=
 \begin{pmatrix}
 0&\kappa e^\top\\
 \kappa e&\beta^2(G_f(d)-g_f(d)I)/(Ds)
 \end{pmatrix},\qquad e=m^{-1/2}1.
\tag{5}
\]

There is a constant epsilon>0 such that with probability tending to one the largest m+1 eigenvalues of (1) lie in (d-epsilon,d+epsilon), and every other eigenvalue is at most d-epsilon. Let P_n be their spectral projection. Define the physical map

\[
 J_n(a,y)=\left(a u+\frac{\beta}{\sqrt D}R_Q(d)f(A)Ey,
                  \frac{y\otimes v}{\sqrt D}\right).
\tag{6}
\]

There is an isometry U_n from R direct sum R^m onto range(P_n) such that, with

\[
 a_n=s+\frac{m\log^4n+m^2\log^2n}{n},
\]

\[
 \|U_n-J_n\|=O_P(a_n),\qquad
 \|U_n^\top(\mathcal A_n-dI)U_n/s-\mathcal T_n\|
       =O_P(a_n)=o_P(m^{-1/2}).
\tag{7}
\]

Constants depend only on the fixed local data, d, c and a fixed host-gap choice. They have no factor depending on m. The assertions hold uniformly over predetermined mark choices, not simultaneously over every subset of a realized graph.

There is also a whole-cluster pair approximation. Put r_n=floor(log_q(1/s)), and fix an integer K>=0. On the short marked matching event, form the m+1 element multiset

\[
 \{\kappa,-\kappa\}
 \cup\bigcup_{\{i,j\}:\operatorname{dist}(i,j)\le r_n+K}
       \{h q^{-\operatorname{dist}(i,j)}/s,
         -h q^{-\operatorname{dist}(i,j)}/s\}
 \cup\{0\text{ with multiplicity }m-2p-1\},
\tag{8}
\]

where p is the number of those pairs. The defining event has probability tending to one. If z_(n,K) is its decreasing ordering, extended arbitrarily on the exceptional event, then for every eta>0,

\[
 \limsup_n\Pr\left(
 \max_{1\le j\le m+1}|(\mu_j-d)/s-z_{n,K,j}|>\eta\right)
 \le C\eta^{-2}q^{-K}.
\tag{9}
\]

Thus the accepted lattice critical-law argument transfers to this entire class with constants (3). Along a phase limit phi, the limiting signed measure away from zero has deterministic atoms at plus and minus kappa and paired atoms at plus and minus h q^(phi-j), with independent multiplicities of means

\[
 \frac d{2q}c^{3/2}q^{j-\phi}.
\tag{10}
\]

This theorem does not yet transfer the finer logarithmic resonance coefficients. The finite host response and gadget metric can affect those coefficients.

## 3. Exact filtered resolvent identity

Define the polynomial in x

\[
 r_z(x)=\frac{f(z)^2-f(x)^2}{z-x}.
\]

Its degree is at most twice the degree of f minus one. The expression is a polynomial even when x=z, with the value obtained by continuity. If f is constant, r_z is zero.

With probability tending to one, every marked fixed-radius ball is a tree and all distinct marks have distance exceeding twice the degree of f. The failure probability is O((m+m squared)/n), with a constant depending on the fixed radius and d. The bound follows from finite configuration-model exploration and label symmetry, with only a fixed simplicity-conditioning factor. On that event,

\[
 E^\top r_z(A)E=\tau_{\rm tree}(r_z)I
\]

simultaneously for z, because it is an identity for a fixed finite collection of powers of A. The radius can be chosen conservatively larger than twice the polynomial degree.

The exact scalar identity f(x) squared divided by z-x equals f(z) squared divided by z-x minus r_z(x), applied on Q, now gives

\[
 G_f(z)-g_f(z)I
 =f(z)^2(G_E(z)-g_d(z)I)+r_z(d)J_m/n.
\tag{11}
\]

The last term has a plus sign because the polynomial is compressed on Q rather than the whole host space. In particular r_d(d)=2f(d)f'(d). Differentiation also gives

\[
 \begin{split}
 G_f'(d)-g_f'(d)I
 ={}&2f(d)f'(d)(G_E(d)-g_d(d)I)\\
 &+f(d)^2(G_E'(d)-g_d'(d)I)
 +\left.\partial_zr_z(d)\right|_{z=d}J_m/n.
 \end{split}
\tag{12}
\]

The prior critical value estimate and the prior finite derivative estimate therefore give

\[
 \|G_f(d)-g_f(d)I\|=O_P(s),
 \qquad
 \|G_f'(d)-g_f'(d)I\|=O_P(a_n).
\tag{13}
\]

The stationary corrections are O(m/n)=O(s squared). Local resolvent derivatives have dimension-independent bounds from the fixed host gap and bounded norm of f(A).

## 4. Gap, inertia and exact physical lift

Eliminate the host space perpendicular to u from zI-mathcal A. Its remaining Schur block is

\[
 \begin{pmatrix}
 z-d&-f(d)\,1_m^\top\otimes b^\top/\sqrt n\\
 -f(d)\,1_m\otimes b/\sqrt n&F(z)
 \end{pmatrix},
\quad
 F(z)=I_m\otimes(zI_k-C)-G_f(z)\otimes bb^\top.
\tag{14}
\]

At d, F(d)=I_m tensor K_0+O_P(s). On a sufficiently small fixed interval about d, its derivative is positive definite and at least the identity, since the derivative of a resolvent is negative semidefinite. Its operator norm is bounded by a fixed constant on that interval.

Choose epsilon smaller than the host gap and small relative to the positive eigenvalues of K_0. At d+epsilon, F is positive definite with lower bound epsilon/2 with probability tending to one. At d-epsilon, its restriction to the m-dimensional local kernel space is at most -epsilon/2, and its restriction to the orthogonal local space is bounded below by a positive constant. The min-max principle gives exactly m negative eigenvalues of F(d-epsilon), separated from zero. The host-to-gadget vector in (14) has norm |f(d)| ||b|| s, tending to zero. The full Schur block consequently has m+1 negative eigenvalues at d-epsilon and none at d+epsilon. The eliminated host block is positive at both endpoints. Inertia proves the asserted cluster count and complementary gap.

For H=mathcal A-dI, define the map

\[
 V_n(a,y)=(a u,\sqrt D\,y\otimes b/\beta).
\]

Its norm is bounded independently of m. Using K_0v=0, direct multiplication yields

\[
 HJ_n=sV_n\mathcal T_n,
 \qquad J_n^\top V_n=I,
 \qquad J_n^\top HJ_n=s\mathcal T_n,
\tag{15}
\]

and

\[
 J_n^\top J_n
 =\operatorname{diag}\left(1,
          [I-\beta^2G_f'(d)]/D\right).
\tag{16}
\]

The gadget part of HJ_n is b tensor the vector

\[
 a f(d)1_m/\sqrt n+
       \beta(G_f(d)-g_f(d)I)y/\sqrt D,
\]

which verifies both the sign and the non-kernel gadget direction in (15). The latter direction cannot simply be replaced by v. The identity J_n^T V_n=I is what makes the compression exact despite that difference.

The proof of the earlier finite isometry lemma uses only (15), a bounded norm for V_n, the Gram estimate and the complementary gap. It therefore applies verbatim with its bound for ||V|| replaced by the fixed value above. More explicitly, the leakage (I-P_n)J_n has norm O_P(s). For M_n=J_n^T P_n J_n one has M_n=I+O_P(a_n+s squared). Set U_n=P_nJ_nM_n^(-1/2). Rank equality makes this an isometry onto the cluster. The complementary compression has norm O_P(s squared), and inverse-square-root normalization proves (7) after division by s. At criticality a_n=O(n^(-1/3)log^2(n))=o(m^(-1/2)).

## 5. Pair interaction and the limiting law

Substitute (11) at d into (5). The bottom block is a fixed scalar multiple of (G_E-g_d I)/s plus a stationary rank-one term of norm O(s). The accepted nonbacktracking estimate approximates (G_E-g_d I)/s by g_d W_(n,K)/s with failure bound C eta^(-2)q^(-K). Its coefficient is precisely h in (3).

For fixed K, the marked short graph is a matching with a tight number of edges. Removing the collective coupling to its 2p endpoints costs kappa sqrt(2p/m), tending to zero in probability. The remaining collective eigenvalues are plus and minus kappa sqrt(1-2p/m). Their replacement by plus and minus kappa costs O_P(1/m). Direct-sum ordering and Weyl's bound, together with (7), give (9).

The pair-count law is unchanged because it depends only on the host and the marks. Its uniform lower-offset tail and the operator upper-cutoff estimate allow exactly the two-sided truncation used in the frozen critical-law proof. This establishes (10), every fixed number of upper and reflected lower cluster order statistics, and the signed measure away from zero. Multiplicities are retained. The signed measure is not globally Poisson, because its two signs are paired and its collective atoms are deterministic.

For any retained unit vector (a,y), the physical mass forms are a squared in the constant host direction, ||y|| squared divided by D on all gadget vertices, and (D-1)||y|| squared divided by D on the perpendicular host, with a uniform vanishing error after applying U_n. This follows directly from (6), (7) and (16). It does not select individual vectors inside repeated levels.

## 6. Two unweighted examples

Neighbourhood duplication in the cubic host is k=1, C=0, b=1 and f(x)=x. The tree identity gives g_f(3)=3 and g_f'(3)=-7. Thus D=8, kappa=3/sqrt(8) and h=3/4, recovering the accepted model.

A genuinely different attachment is a triangle at each marked host vertex, with the host joined to two of its three new vertices. Take k=3, C the triangle adjacency, b=(1,1,0) and f(x)=1. This adds triangles and attaches at the host vertex, rather than creating a new vertex with the host's neighbourhood. All edges have weight one.

Here g_3(3)=2/3 and g_3'(3)=-10/9. The local matrix has eigenvalues 0, 11/3 and 4, with unit kernel vector

\[
 v=(3,3,2)/\sqrt{22},\qquad\beta^2=18/11.
\]

Consequently

\[
 D=31/11,\qquad \kappa=\sqrt{18/31},\qquad h=12/31.
\tag{17}
\]

The new graph has n+3m vertices but only m+1 eigenvalues in the critical near-3 cluster. The other local channels stay a fixed distance below 3. In a pair-only physical subspace the gadget and perpendicular-host masses are 11/31 and 20/31 respectively, subject to the same projector transfer as in the prior subspace argument. A bounded exact symbolic check of the three-by-three local matrix confirmed its eigenvalues and kernel. That check is supplementary to the explicit algebra, not the proof of the random statement.

## 7. What the direct Hashimoto route does and does not add

For either unweighted augmented graph, write D_aug for its actual degree matrix, B_aug for its oriented-edge nonbacktracking matrix, and

\[
 H_{\rm aug}(t)=I-t\mathcal A+t^2(D_{\rm aug}-I).
\]

The classical Ihara-Bass identity relates det(I-tB_aug) to det H_aug(t), including its familiar factors at t=plus or minus one. With z=t^(-1)+(d-1)t, the exact adjacency identity is

\[
 t(zI-\mathcal A)
 =H_{\rm aug}(t)-t^2(D_{\rm aug}-dI).
\tag{18}
\]

The degree correction is supported on the gadget and its incident host vertices. It is nonzero for both examples. Dropping it changes the adjacency eigenproblem and is not an admissible shortcut. For general weighted data, an appropriate weighted correspondence must be derived instead of inserting weighted entries into the unweighted degree formula.

Eliminating bulk edge coordinates can express the same local boundary self-energy in an oriented-edge language. On the regular host, however, the exact generating identity already used in the prior proofs produces (11) and the same propagation q^(-distance). A determinant correspondence alone gives no new uniform resolvent or projector bound for the nonnormal edge operator. The present argument obtains those bounds through a self-adjoint physical lift and the accepted marked estimates.

Route assessment: direct Hashimoto analysis has not yet supplied additional critical precision. Its main potential value is extension to several ports or a nonregular finite-type host, where the scalar polynomial identity (11) is insufficient. For the present single-port class, the proved scope gain comes from the local resonance criterion and exact physical lift, rather than from a new edge-operator estimate. The four-hour run should not spend its remaining budget merely rewriting the same scalar estimates on oriented edges.

## 8. Frozen premises and limits

The prior marked value, derivative and nonbacktracking tail bounds are those of the growing-defect proof `56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b`, the close-pair nonbacktracking proof `d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896`, and the critical effective proof `13b559897d6ed9253a2fc6dd4dede5dd03914c078558d759542afc9c54d28864`. The geometric count law is `702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29`, and its critical-law integration is `e379a0b55e81925276d2c3046ec1cc4b25c21e028d22fef53516f4b5828e48f3`. The finite physical-isometry proof is `f13fbd47ba04bd638f4bafe940c20d604bfa4a4653df553b4b737f2e3779e87a`.

The result covers one filtered host port, a fixed finite gadget and a simple local resonance. It does not prove a multiple-port matrix-valued law, a new nonregular-host law, a direct Hashimoto pseudospectral estimate or the retuned negative crossing. Historical priority is assigned to a separate workstream. Familiar Schur, Ihara-Bass, min-max and projector tools are credited as existing methods. The finite supporting algebra and the random-graph application are not claimed fully formalized.
