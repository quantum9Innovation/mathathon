# Critical spectral subspaces and their physical lift

November 15, 2026. Owner: root. Revision 1, frozen for separate review. The proof uses the accepted critical-law packet and classical spectral projection estimates. It adds an explicit isometric identification of the actual graph cluster, level-subspace convergence and a spatial concentration statement for pair subspaces.

## 1. Model and notation

Let A be the adjacency of a uniform simple labelled cubic graph on n vertices, with n even. Choose m distinct labels before sampling, with m/n^(1/3) tending to c>0. Let E be their coordinate inclusion and

\[
\mathcal A=\begin{pmatrix}A&AE\\E^\top A&0\end{pmatrix},\quad
s=\sqrt{m/n},\quad D=8,\quad\kappa=3/\sqrt8,\quad h=3/4.
\]

Write u=n^(-1/2)1, Q=I-uu^T, B=AE and R=(3I-A_Q)^(-1) on u perpendicular, extended by zero on u. All constructions are made on a fixed two-sided host-gap event, whose probability tends to one, and extended arbitrarily off it. Put

\[
F(z)=zI-B^\top Q(zI-A_Q)^{-1}QB,\qquad
e=m^{-1/2}1,
\]

\[
T=\begin{pmatrix}0&\kappa e^\top\\\kappa e&-F(3)/(Ds)\end{pmatrix}.
\tag{1}
\]

Let P be the orthogonal projection onto the largest m+1 eigenvalues of the actual augmented graph. The preceding cluster-width and interlacing results imply that this is the complete near-3 cluster, with its complement below 3 by a fixed positive gap, with probability tending to one. They also give ||T||=O_P(1).

Define a linear map from the retained coordinate space R direct sum R^m into the actual n+m dimensional graph space:

\[
J(a,v)=\left(a u+RBv/\sqrt D,\ v/\sqrt D\right).
\tag{2}
\]

This map includes the host response to the added coordinates. It is not merely the inclusion of the added vertices.

## 2. A quantitative finite isometry lemma

The following deterministic argument works with any isolated host mode d, scalar D>0 and bounded B. In this section replace 3 by d. Set H=mathcal A-dI, let P be a commuting orthogonal projection of rank m+1, and assume the spectrum of H on its orthogonal complement lies in (-infinity,-gamma], gamma>0. Define J and T by (1)-(2), using b=B^T u and the upper-right block b^T/(s sqrt(D)) in T.

Let

\[
\epsilon=\|F'(d)/D-I\|,\quad v_D=\sqrt{\max(1,D)},\quad
\beta=s v_D\|T\|/\gamma,\quad t=\epsilon+\beta^2.
\]

If t<=1/2, the matrix M=J^T P J is positive definite, and

\[
U=PJ M^{-1/2}
\tag{3}
\]

is an isometry from the retained space onto range(P). There is an absolute constant C such that

\[
\|U-J\|\le\beta+C(1+\sqrt\epsilon)t,
\tag{4}
\]

\[
\left\|U^T H U/s-T\right\|
\le C t\|T\|+2s v_D^2\|T\|^2/\gamma.
\tag{5}
\]

To prove this, define V(a,v)=(a u,sqrt(D)v). Direct block multiplication gives the three exact identities

\[
J^T J=\operatorname{diag}(1,F'(d)/D),\qquad
HJ=sVT,\qquad J^T HJ=sT.
\tag{6}
\]

For the last identity, J^T V=I, because RB takes values perpendicular to u. On the complementary spectral space, H has inverse norm at most 1/gamma. Thus

\[
\|(I-P)J\|\le\gamma^{-1}\|(I-P)HJ\|\le\beta.
\]

Consequently ||M-I||<=epsilon+beta^2=t. Functional calculus on [1/2,3/2] gives ||M^(-1/2)||<=sqrt(2) and ||M^(-1/2)-I||<=Ct. This proves (3)-(4). Rank equality makes the isometric image all of range(P).

Since H commutes with P,

\[
J^T P H P J=sT-J^T(I-P)H(I-P)J.
\]

The norm of the second term is at most

\[
\|(I-P)J\|\|(I-P)HJ\|
\le s^2 v_D^2\|T\|^2/\gamma.
\]

Insert M^(-1/2) on both sides and use its preceding bounds. This gives (5), without a factor depending on the cluster dimension. The exact identities, rather than an eigenvalue-only comparison, are what supply the graph subspace identification.

## 3. Precision in the critical graph model

The accepted derivative estimate, before imposing subcritical growth, gives

\[
\|F'(3)-DI\|
=O_P\!\left(\frac{m\log^4 n+m^2\log^2 n}{n}\right).
\tag{7}
\]

Here the explicit algebra expressing F' through the centered resolvent and its first derivative, together with the host-gap operator bounds, is the same as in the earlier graph theorem. The value error is O_P(s), so any additional value term from that algebra is absorbed in the estimates below. Equivalently, one may add O_P(s) to the right side of (7), without affecting any conclusion.

Set a_n=s+(m log^4(n)+m^2 log^2(n))/n. At m/n^(1/3)->c,

\[
a_n=O(n^{-1/3}\log^2 n)=o(m^{-1/2}).
\]

The finite lemma and ||T||=O_P(1) therefore prove

\[
\|U-J\|=O_P(a_n),\qquad
\|U^T(\mathcal A-3I)U/s-T\|=O_P(a_n)=o_P(m^{-1/2}).
\tag{8}
\]

These estimates hold on the actual full cluster and are stronger than what is needed for the first-order subspace theorem. They do not by themselves approximate T by pair blocks to this finer precision.

## 4. Level-subspace theorem

Write r_n=floor(log_2(1/s)) and phi_n=log_2(1/s)-r_n. Work along a subsequence with phi_n->phi in [0,1]. The endpoint phases represent the same lattice after reindexing. Its positive levels are

\[
w_k(\phi)=\tfrac34 2^{\phi-k},\qquad k\in\mathbb Z.
\]

Fix a nonzero level x in {kappa,-kappa} union {w_k(phi),-w_k(phi)}. Choose rho>0 so that the closed interval [x-4rho,x+4rho] contains no zero and no other distinct limiting level. This is possible because the levels are locally discrete away from zero. A collision between a pair level and a collective level is treated as one level.

If x=sigma w_k(phi), sigma in {1,-1}, let C_n(x) be the set of marked pairs at host distance r_n+k. Each such pair {a,b}, with a fixed ordering of its endpoints, defines the retained unit vector

\[
f_{ab}^{\sigma}=(0,(e_a+\sigma e_b)/\sqrt2).
\tag{9}
\]

If x is not a pair level, this collection is empty. If x=sigma kappa, also include

\[
v_\sigma=(1,\sigma e)/\sqrt2.
\tag{10}
\]

Let V_n(x) be their span and Q_n(x) its orthogonal projection. These vectors are linearly independent with probability tending to one. They need not be exactly mutually orthogonal when the positive collective vector is included. Define V_n and Q_n arbitrarily on the exceptional event.

Let P_n(x) be the actual graph spectral projection onto eigenvalues in

\[
3+s(x-\rho,x+\rho).
\]

Then

\[
\|P_n(x)-UQ_n(x)U^T\|\xrightarrow{P}0,
\qquad
\|P_n(x)-\operatorname{Proj}_{J V_n(x)}\|\xrightarrow{P}0.
\tag{11}
\]

With probability tending to one, its rank equals

\[
|C_n(x)|+\mathbf1_{\{x=\kappa\text{ or }x=-\kappa\}}.
\tag{12}
\]

The pair count converges to a Poisson variable of mean (3/4)c^(3/2)2^(k-phi). The theorem covers its positive probability of being zero and its positive probability of being larger than one. It does not select a basis inside a repeated pair level.

## 5. Proof of the subspace approximation

Fix K large enough to include the target offset k when present. The accepted effective-operator argument gives the short-interaction matrix S_(n,K), with full constant host star and pair weights h 2^(-ell)/s, satisfying, for every eta>0,

\[
\limsup_n\Pr(\|T-S_{n,K}\|>\eta)\le C\eta^{-2}2^{-K}.
\tag{13}
\]

For fixed K its short marked graph is a matching with a tight number p_(n,K) of edges. Delete the host couplings to its 2p endpoints. The resulting direct sum S^0_(n,K) differs from S_(n,K) by norm kappa sqrt(2p/m)=o_P(1). Its free-star levels are plus and minus kappa sqrt(1-2p/m). Its pair blocks have their exact signed weights.

For large n the spectral projector of S^0_(n,K) around the circle of radius rho centered at x is the span of the target pair vectors and, when appropriate, its free-star collective vector. Replacing the latter by (10) changes this projector by o_P(1), since the free marked constant vector differs from e by O_P(sqrt(p/m)). The target vectors remain independent since p is tight and m tends to infinity.

For clarity, the needed projection estimate follows directly from the resolvent identity on that circle. When the reference spectrum has distance at least rho/2 from the contour and the operator perturbation has norm at most rho/4, the perturbed spectrum has distance at least rho/4 from it. Integrating the resolvent identity bounds the difference of the two projections by C||perturbation||/rho. This bound is independent of multiplicity and matrix size.

Apply it to U^T(mathcal A-3I)U/s, then S_(n,K), then S^0_(n,K), using (8) and (13). For each epsilon>0,

\[
\limsup_n\Pr(\|P_n(x)-UQ_n(x)U^T\|>\epsilon)
\le C_{x,\rho,c}\epsilon^{-2}2^{-K},
\tag{14}
\]

after increasing the constant if necessary. The complementary graph spectrum is separated from this contour by the fixed host gap for large n. Now send K to infinity. The target Q_n(x) does not depend on K, so (14) proves the first assertion of (11). Projection norm less than one implies equality of finite ranks, giving (12).

Finally, (8) makes J uniformly close to the isometry U. On every subspace V, the projection onto JV differs from U Proj_V U^T by at most C||J-U|| once that error is small. Indeed, J restricted to V has smallest singular value at least 1-||J-U||, and normalization bounds the distance of each unit vector of JV to UV. Equal dimensions give the reverse projection bound. This proves the second assertion of (11).

## 6. Mass operators and collisions

Let P_u project onto the one-dimensional vector (u,0) in the actual graph space, and let P_add project onto all added vertices. From (2) and (8), uniformly over retained unit vectors (a,v),

\[
\|P_u U(a,v)\|^2=a^2+o_P(1),\qquad
\|P_{\rm add}U(a,v)\|^2=\|v\|^2/D+o_P(1).
\tag{15}
\]

The perpendicular host mass is (D-1)||v||^2/D+o_P(1). These are uniform statements on entire subspaces, including arbitrary linear combinations of different eigenvectors in the cluster. In operator form on range(P),

\[
\left\|P P_{\rm add}P-\frac1D(P-P P_u P)\right\|=o_P(1).
\tag{16}
\]

For a level without a collective mode, all unit vectors of range(P_n(x)) consequently have masses

\[
(\text{constant host},\text{added},\text{perpendicular host})
=(0,1/8,7/8)+o_P(1).
\tag{17}
\]

For a collective level without a pair collision, the subspace is one-dimensional with masses (1/2,1/16,7/16)+o_P(1).

At a collective-pair collision, the subspace has rank p+1 with p=|C_n(x)|. The operator P_n(x)P_u P_n(x) has at most one nonzero eigenvalue, and this eigenvalue tends to 1/2. To see this, use (11) and the projection of the retained host coordinate onto V_n(x). For the negative level it has squared norm exactly 1/2. For the positive level that squared norm is (1/2)/(1-p/m), which tends to 1/2 because p is tight. Thus the sum of constant-host masses over any orthonormal basis of the physical level subspace tends to 1/2. There is no claim that a chosen basis allocates this mass equally.

Equation (16) gives the corresponding basis-independent added and perpendicular-host mass operators. Individual resonant eigenvector masses require a finer spectral splitting and are treated separately.

## 7. Spatial concentration of the pair subspace

Suppose the fixed level x has no collective mode. Let V_end be the set of all endpoints of pairs in C_n(x). Its cardinality is tight. Let N_L be the union of host balls of radius L about these endpoints, together with their associated added vertices. Then, for every epsilon>0,

\[
\lim_{L\to\infty}\limsup_{n\to\infty}
\Pr\left\{\sup_{\psi\in\operatorname{range}(P_n(x)),\ \|\psi\|=1}
\|\mathbf1_{N_L^c}\psi\|>\epsilon\right\}=0.
\tag{18}
\]

Take the supremum to be zero when the subspace is zero. This is concentration near the union of the relevant pair endpoints. It does not assert that each eigenvector chooses one pair.

To prove it, on the two-sided gap event write P_host=A/3 with ||P_host Q||<=rho_0<1. Since B=AE,

\[
R B=\sum_{j\ge1}P_{\rm host}^j Q E.
\]

The operator tail after j=L has norm at most rho_0^(L+1)/(1-rho_0). For a retained vector v supported on t endpoints, the unprojected finite sum sum_(j=1)^L P_host^j E v is supported on their radius-L host balls. Its projection correction is -L u u^T E v, with norm at most L sqrt(t/n)||v||. Hence for J(0,v), the norm outside N_L is at most

\[
D^{-1/2}\left(\frac{\rho_0^{L+1}}{1-\rho_0}+L\sqrt{t/n}\right)\|v\|.
\tag{19}
\]

The pair subspace V_n(x) has exactly this support property. Use (11), the near-isometry of J, tightness of t, and then send L to infinity. This proves (18). No conditioning on a rare marked-pair event or simultaneous tree-ball assumption is needed.

## 8. Dependencies and limitations

The preceding [effective-operator proof](../../critical-law-round-01/root/effective-operator-v1.md), SHA256 13b559897d6ed9253a2fc6dd4dede5dd03914c078558d759542afc9c54d28864, supplies (13), matching, tight pair counts, and the value estimate. The [critical law](../../critical-law-round-01/root/critical-law-v1.md), SHA256 e379a0b55e81925276d2c3046ec1cc4b25c21e028d22fef53516f4b5828e48f3, and [pair-count theorem](../../critical-law-round-01/probability/pair-counts-v1.md), SHA256 702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29, supply the level list and count limits. The [nonbacktracking upper proof](../../close-pair-transition-round-01/root/nonbacktracking-upper-v1.md), SHA256 d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896, records the finite derivative bound before growth specialization. The earlier [transfer theorem](../../growing-defects-round-01/root/transfer-v1.md), SHA256 deb05e53631ad4d273f48b2d6253014352c1263010d3990ebcc4e0b616351b99, supplies the Schur definitions and cluster separation.

The proof concerns fixed nonzero levels at criticality, predetermined marks and the cubic H=0 model. It does not determine a basis inside a repeated level, a law at the accumulation point zero, or a normalized-Laplacian mixing statement. The operator identities and probability arguments above are paper proofs. Finite formal components are listed separately, with no end-to-end formalization claim.
