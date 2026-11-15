# A common interaction law for locally filtered finite attachments

November 15, 2026. Owner: root. Revision 1, frozen for independent review. Status: proposed paper theorem, not yet integrated into the canonical ledger.

Exposure: the author read the accepted SG-22 through SG-28 proofs and the shared problem packet. No live structural or probability proof from this round was read before this revision. The prior-source worker reported that general decoration and Schur reduction identities are established. Novelty is not asserted for those identities.

## 1. Model and local resonance data

Fix d>=3, put q=d-1, and let A be a uniform simple labelled d-regular adjacency matrix on n vertices, with nd even. Let E select m predetermined distinct labels. Let p be a fixed nonzero real polynomial. Let C be a fixed real symmetric k by k matrix with largest eigenvalue strictly smaller than d, and let b be a nonzero vector in R^k. Define

\[
L=p(A)E,\qquad
\mathcal A=
\begin{pmatrix}
A&L(I_m\otimes b^\top)\\
(I_m\otimes b)L^\top&I_m\otimes C
\end{pmatrix}.
\tag{1}
\]

The lower coordinates consist of m copies of a fixed finite attachment. General p, C and b give a real symmetric locally supported weighted operator. A separate example below is a simple unweighted graph.

Let nu_d be the root spectral measure of the infinite d-regular tree, and define, for real z in a fixed neighborhood of d,

\[
g(z)=\int\frac{1}{z-x}\,d\nu_d(x),\qquad
k_p(z)=\int\frac{p(x)^2}{z-x}\,d\nu_d(x),\qquad
f(z)=b^\top(zI-C)^{-1}b.
\tag{2}
\]

The neighborhood is chosen above both 2 sqrt(q) and the largest eigenvalue of C. In particular f(z)>0. Assume the critical local calibration

\[
f(d)^{-1}=k_p(d).
\tag{3}
\]

This calibration is possible by scaling any nonzero b, since k_p(d)>0. Set

\[
a=(f^{-1})'(d)-k_p'(d)>0,\qquad
\kappa=\frac{|p(d)|}{\sqrt a},\qquad
h=\frac{p(d)^2g(d)}a=g(d)\kappa^2,\qquad
\eta=\frac{(f^{-1})'(d)}a.
\tag{4}
\]

Both terms defining a are strictly positive after the subtraction, since f'<0 and k_p'<0. Hence 0<eta<1. Also

\[
g(d)=\frac{q}{d(d-2)},\qquad
g'(d)=-\frac{q(q^2+1)}{d^2(d-2)^3}.
\tag{5}
\]

For the interaction theorem assume p(d) is nonzero. The cancellation case is treated separately.

## 2. Structural theorem

Write s=sqrt(m/n). The constants below may depend on the fixed local data d,p,C,b and the fixed host gap. They do not depend on n,m or the predetermined choice of marks.

If m^3/n tends to zero, there are exactly m+1 eigenvalues near d, these are the largest m+1 eigenvalues, and their ordered displacements divided by s differ by o_P(1) from

\[
\kappa,\quad 0\text{ with multiplicity }m-1,\quad-\kappa.
\tag{6}
\]

At criticality m/n^(1/3) tends to c>0. Put

\[
r=\lfloor\log_q(1/s)\rfloor,\qquad
\phi_n=\log_q(1/s)-r.
\]

For each fixed K>=0, form the marked graph whose edges are pairs at host distance at most r+K. With probability tending to one it is a matching with a tight number p_(n,K) of edges. Form the m+1 element multiset

\[
\mathcal Z_{n,K}=
\{+\kappa,-\kappa\}
\cup\bigcup_{\{u,v\}:\ell_{uv}\le r+K}
\{+h q^{-\ell_{uv}}/s,-h q^{-\ell_{uv}}/s\}
\cup\{0\text{ with multiplicity }m-2p_{n,K}-1\}.
\tag{7}
\]

Outside the matching event it can be defined arbitrarily. If z_(n,K,j) denotes its decreasing ordering, then for every epsilon>0,

\[
\limsup_n
\mathbb P\left\{\max_{1\le j\le m+1}
\left|(\mu_j(\mathcal A)-d)/s-z_{n,K,j}\right|>\epsilon\right\}
\le C\epsilon^{-2}q^{-K}.
\tag{8}
\]

Along phi_n tending to phi, the normalized cluster therefore converges as a point measure away from zero to

\[
\delta_\kappa+\delta_{-\kappa}
+\sum_{j\in\mathbb Z}P_j
\left(\delta_{h q^{\phi-j}}+\delta_{-h q^{\phi-j}}\right),
\tag{9}
\]

where the P_j are independent Poisson variables with means

\[
\lambda_j=\frac{d c^{3/2}}{2q}q^{j-\phi}.
\tag{10}
\]

The notation in (9) means addition of measures. Every fixed number of upper and reflected lower order statistics has the corresponding joint limit. The distribution depends on the distance phase. As in SG-26, there is no single limiting law over all admissible size sequences at fixed c.

The result is a structural critical law and a subcritical collective law. It does not yet assert the general postcritical sharp necessity statement throughout m=o(sqrt(n)).

## 3. Exact reduction retaining the host mode

Let u be the constant unit host vector, Q=I-uu transpose, and R_Q(z) the inverse of zI-A on u perpendicular, extended by zero on u. Work on a fixed host gap event of probability tending to one. Define

\[
G(z)=E^\top R_Q(z)E,\qquad
K(z)=E^\top p(A)R_Q(z)p(A)E,\qquad
F(z)=f(z)^{-1}I_m-K(z).
\tag{11}
\]

Then for z in a fixed interval about d,

\[
\#\{\mu_j(\mathcal A)>z\}
=n_-\left(
\begin{pmatrix}
z-d&-p(d)\mathbf1_m^\top/\sqrt n\\
-p(d)\mathbf1_m/\sqrt n&F(z)
\end{pmatrix}
\right).
\tag{12}
\]

Here n_- counts strictly negative eigenvalues with multiplicity.

To prove (12), write the coordinates of each motif as

\[
y_i=\frac{(zI-C)^{-1}b}{f(z)}t_i+y_i^\perp,
\qquad b^\top y_i^\perp=0,\qquad t_i=b^\top y_i.
\tag{13}
\]

This is an invertible linear change of coordinates. Its energy satisfies

\[
y_i^\top(zI-C)y_i=f(z)^{-1}t_i^2
+(y_i^\perp)^\top(zI-C)y_i^\perp.
\tag{14}
\]

The latter block is positive definite. The host-motif coupling depends only on t_i. Eliminating all these positive blocks leaves the symmetric matrix with blocks zI-A, -L and f(z)^(-1)I. Splitting off the constant host vector and eliminating the positive host complement gives (12) by an invertible triangular congruence. This proves an inertia identity, including at z=d, without dividing by z-d.

Also

\[
F'(z)=(f^{-1})'(z)I_m+
E^\top p(A)R_Q(z)^2p(A)E
\tag{15}
\]

is uniformly positive definite on a sufficiently small fixed interval, and F'' is bounded there in operator norm independently of m and n. These bounds use only the fixed local data and host gap.

## 4. Polynomial locality and the uniform random error

For real z define the polynomial

\[
D_z(x)=\frac{p(z)^2-p(x)^2}{z-x}.
\tag{16}
\]

The quotient is a polynomial, including at x=z. It has degree at most 2 deg(p)-1, with the zero polynomial when p is constant. The exact functional-calculus identity is

\[
p(A)R_Q(z)p(A)=p(z)^2R_Q(z)-D_z(A)+D_z(d)uu^\top.
\tag{17}
\]

For a fixed polynomial degree, with probability tending to one all marked neighborhoods needed for its diagonal moments are trees and no distinct marks are within distance 2 deg(p). A fixed-radius exploration gives failure probability O(m/n+m^2/n). Thus this event holds in both regimes of the theorem. On this event, simultaneously for z throughout the interval,

\[
E^\top D_z(A)E=
\left(\int D_z(x)\,d\nu_d(x)\right)I_m.
\]

Consequently the exact identity becomes

\[
K(z)=k_p(z)I_m+p(z)^2(G(z)-g(z)I_m)+D_z(d)J_m/n.
\tag{18}
\]

All z derivatives of this identity are valid on the same event. In particular

\[
F(d)=-p(d)^2(G(d)-g(d)I_m)-2p(d)p'(d)J_m/n.
\tag{19}
\]

The accepted SG-22 estimate gives ||G(d)-g(d)I||=o_P(s) in the subcritical regime. At criticality the accepted SG-26 effective proof gives ||G(d)-g(d)I||=O_P(s), ||G'(d)-g'(d)I||=o_P(1), and the whole marked-space tail estimate

\[
\limsup_n\mathbb P\left\{
\left\|(G(d)-g(d)I)/s-g(d)W_{n,K}/s\right\|>\epsilon
\right\}
\le C\epsilon^{-2}q^{-K}.
\tag{20}
\]

Here W has entries q^(-ell_uv) for distinct marked pairs at distance at most r+K, and zero otherwise. These are unconditional simple-graph estimates. No expectation is conditioned on the host gap or on a rare pair.

Since ||J_m/n||=m/n=s^2, equations (18)-(20) give

\[
\|F(d)\|=O_P(s),\qquad
\|F'(d)-aI_m\|=o_P(1)
\tag{21}
\]

at criticality, with o_P(s) replacing the first bound subcritically.

## 5. Eigenvalue transfer and the pair law

Define the retained matrix

\[
T_n=
\begin{pmatrix}
0&p(d)e^\top/\sqrt a\\
p(d)e/\sqrt a&-F(d)/(as)
\end{pmatrix},
\qquad e=m^{-1/2}\mathbf1_m.
\tag{22}
\]

Congruence of the matrix in (12) by diag(1,a^(-1/2)I) gives

\[
s[xI-T_n+\mathcal E_n(x)]
\]

at z=d+sx, with

\[
\sup_{|x|\le B}\|\mathcal E_n(x)\|
\le a^{-1}B\|F'(d)-aI\|+C B^2s=o_P(1)
\tag{23}
\]

for every fixed B. Also ||T_n||=O_P(1). Applying ordered eigenvalue comparison and the exact inertia identity, first on ||T_n||<B/2 and then letting B increase, proves

\[
\max_{1\le j\le m+1}|(\mu_j-d)/s-\lambda_j(T_n)|=o_P(1).
\tag{24}
\]

At fixed small endpoints d plus or minus gamma_0 the same identity and positivity of F' show that exactly m+1 eigenvalues are in that fixed interval, with every other eigenvalue below d-gamma_0. Thus these are the actual top cluster, although adding km motif coordinates prevents using the old m-row interlacing argument unchanged.

Equation (19) and (20) approximate T_n by the star-plus-matching matrix with star coefficient p(d)/sqrt(a) and matching weights h q^(-ell)/s. Deleting the host couplings at the tight number of matched coordinates costs O_P(m^(-1/2)) for fixed K. The remaining star has eigenvalues approaching plus and minus kappa, and each matching block has its two signed eigenvalues. Weyl's inequality proves (8).

The accepted SG-25 finite-window Poisson counts, shortest-distance tightness, and (8) then prove (9)-(10) by the same two-sided truncation argument as SG-26. They are host-and-mark statements independent of the attachment. They do not require a new independence assumption for the defect entries.

## 6. Physical lift and mass operators

Define

\[
M=\frac{(dI-C)^{-1}b}{f(d)},\qquad
\mathcal J(\alpha,v)=
\left(\alpha u+R_Q(d)p(A)Ev/\sqrt a,\
v\otimes M/\sqrt a\right).
\tag{25}
\]

In the lower component, v tensor M lists the m motif vectors v_i M. Direct multiplication gives

\[
\mathcal J^\top\mathcal J=\operatorname{diag}(1,F'(d)/a),
\quad
(\mathcal A-dI)\mathcal J=s\mathcal V T_n,
\quad
\mathcal J^\top\mathcal V=I,
\tag{26}
\]

where

\[
\mathcal V(\alpha,v)=(\alpha u,\sqrt a\,v\otimes b).
\tag{27}
\]

In particular J transpose (Acal-dI) J=s T_n. The exact relations use b transpose M=1 and ||M|| squared=(f^(-1))'(d).

Let P be the actual top-cluster projection. Its complementary spectral gap is fixed with probability tending to one, and (26) gives ||(I-P)J||=O_P(s). Since J transpose J=I+o_P(1), the matrix J transpose P J is positive definite with probability tending to one. Therefore

\[
\mathcal U=P\mathcal J(\mathcal J^\top P\mathcal J)^{-1/2}
\tag{28}
\]

is an isometry onto the actual cluster, satisfies ||U-J||=o_P(1), and satisfies

\[
\|\mathcal U^\top(\mathcal A-dI)\mathcal U/s-T_n\|=o_P(1).
\tag{29}
\]

This follows by the dimension-free proof of the finite isometry lemma in SG-27, with ||V|| bounded by the fixed local data. Its hypotheses and three identities have been verified above for the present model.

Uniformly on retained unit vectors (alpha,v), the physical masses in the constant host direction, all motif vertices, and the perpendicular host directions differ by o_P(1) from

\[
|\alpha|^2,\qquad \eta\|v\|^2,\qquad(1-\eta)\|v\|^2.
\tag{30}
\]

The motif identity is exact for J. The perpendicular host Gram matrix tends to (1-eta)I by (15), (21) and (25).

At each fixed nonzero critical level, the actual spectral projection is consequently approximated by the lift of the matching pair subspace, together with the collective vector if its level coincides. The proof is the fixed-level gap, cutoff and projection argument of SG-27 applied to (20), (22) and (29). Retain full pair subspaces when there is multiplicity. A pure pair level has mass triple (0,eta,1-eta). A collective level separated from pair levels has mass triple (1/2,eta/2,(1-eta)/2).

No spatial tail theorem or finer resonance-scale error is claimed in this revision.

## 7. Recovery and a different unweighted attachment

For p(x)=x, C=(0) and b=sqrt(d-2), equation (3) holds and

\[
a=\frac{2q^2}{(d-2)^3},\quad
\kappa=\frac{d(d-2)^{3/2}}{\sqrt2q},\quad
h=\frac{d(d-2)^2}{2q},\quad
\eta=\frac{(d-2)^2}{2q^2}.
\tag{31}
\]

Thus the theorem recovers the accepted weighted duplication law, and the cubic unweighted case has eta=1/8.

For a genuinely different simple unweighted cubic construction, take p=1 and let C be the adjacency matrix of the star K_(1,7). Let b be the coordinate vector of its center. At each marked host vertex attach one new star center by a single edge, with seven new leaves attached to that center. All eight new vertices belong to that one motif. Its largest internal eigenvalue is sqrt(7)<3. Direct elimination of its seven leaves gives

\[
f(z)=\frac{z}{z^2-7},\qquad
f(3)^{-1}=\frac23=g(3),\qquad
a=\frac{26}{9}.
\]

Therefore

\[
\kappa=\frac3{\sqrt{26}},\qquad
h=\frac3{13},\qquad
\eta=\frac8{13}.
\tag{32}
\]

The same one-third critical scale, geometric Poisson pair law and physical subspace conclusion follow. Its pair masses are (0,8/13,5/13), while separated collective masses are (1/2,4/13,5/26). This is a theorem for actual unweighted augmented graphs, subject to the random-host and predetermined-mark assumptions.

## 8. A cancellation boundary with exact compact modes

The condition p(d) nonzero is substantive. Take p(x)=d-x, C=(0), b=1. Then k_p(d)=d=f(d)^(-1), so the local resonance calibration holds but p(d)=0. Suppose the marked vertices form an independent set in any finite d-regular host. Let

\[
\mathcal B=
\begin{pmatrix}
A&(dI-A)E\\
E^\top(dI-A)&0
\end{pmatrix}.
\tag{33}
\]

For every t in R^m, direct multiplication shows

\[
\mathcal B(Et,t)=d(Et,t).
\tag{34}
\]

Indeed the host coordinate is AEt+(dI-A)Et=dEt, and the lower coordinate is E transpose (dI-A)Et=dt since E transpose A E=0. Also (u,0) is an exact eigenvector at d because (dI-A)u=0. These m+1 vectors are linearly independent when t ranges over the coordinate vectors, since their added coordinates force every coefficient except the host coefficient to vanish.

Thus the eigenvalue d has multiplicity at least m+1, including m modes each supported on one host vertex and its added vertex. For the random host and m=o(sqrt(n)), the independent-mark event has probability tending to one. These signed weighted attachments do not exhibit the claimed nonzero collective-pair competition. They are not offered as a counterexample within nonnegative simple unweighted attachments.

The cancellation example establishes why coupling to the constant host mode belongs among the structural hypotheses. It does not classify all possible zero-coupling models.

## 9. Dependencies and review requests

The exact prior source revisions are bound in input/PRIOR_BASELINE.json. The proof uses SG-22's marked resolvent and derivative estimates, SG-25's Poisson counts and matching geometry, SG-26's marked whole-space truncation and order-statistic tightness, and the deterministic isometry argument in SG-27. It does not use the unresolved retuned negative crossing.

Review should reconstruct the energy decomposition and inertia count, the sign of the stationary correction in (18), the scalar derivative a, the fixed-gap top-cluster argument for km new vertices, the metric and physical mass identities, and the unweighted star constants. Check that the stated random error is uniform in m through the critical range and that the cancellation example is explicitly signed.

This is a paper proof awaiting independent review. No asymptotic probability, infinite tree calculus or graph subspace theorem has yet been formally encoded for this new model.
