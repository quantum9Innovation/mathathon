# Two scales of collective-pair resonance in the actual graph

November 15, 2026. Owner: root. Revision 1, frozen for separate review. This proof integrates the separately frozen subspace, probability and finite-matrix arguments. Its conclusion concerns the actual augmented cubic graph, not only a formal effective matrix.

## 1. Model, coordinates and scope

Use the critical cubic H=0 model of [subspaces-v1.md](subspaces-v1.md), SHA256 f13fbd47ba04bd638f4bafe940c20d604bfa4a4653df553b4b737f2e3779e87a. Thus m/n^(1/3)->c>0, s=sqrt(m/n), kappa=3/sqrt(8), and

\[
r=\lfloor\log_2(1/s)\rfloor,\qquad
w=\frac34\frac{2^{-r}}s,\qquad\delta=m^{-1/2}.
\]

Throughout the resonance statements w tends to kappa, equivalently the distance phase tends to 1/2. Let p_n count marked pairs at host distance r. Its limiting law is Poisson with mean

\[
\lambda_* =\frac{3c^{3/2}}{4\sqrt2}.
\tag{1}
\]

For any fixed p>=0, the assertions below may be read conditionally on p_n=p. This conditioning is legitimate for convergence statements, since its probability tends to exp(-lambda_*)lambda_*^p/p!, which is positive. The probability proofs establishing the estimates do not condition on a rare pair. Tightness also gives the equivalent unconditional mixture statement over p.

Let V contain the 2p_n endpoints of those pairs, let f be the unit constant marked vector outside V, and let h be the retained host coordinate. On the matching event, define

\[
c_+=(h+f)/\sqrt2,\qquad c_-=(h-f)/\sqrt2,
\]

\[
a_j^+=(e_{u_j}+e_{v_j})/\sqrt2,\qquad
a_j^-=(e_{u_j}-e_{v_j})/\sqrt2.
\tag{2}
\]

These are vectors of the retained coordinate space. Each chosen family c_sigma,a_1^sigma,...,a_p^sigma is orthonormal. The actual physical lift and isometry are J and U from the subspace theorem. All eigenvalue windows below have fixed sufficiently small radius around plus or minus kappa in coordinates (mu-3)/s. They select that level of the critical cluster, not necessarily the globally largest eigenvalues.

## 2. Positive avoided crossing

Suppose

\[
\tau_n=\sqrt m(w-\kappa)\longrightarrow\tau\in\mathbb R.
\tag{3}
\]

Conditional on p_n=p>=1, exactly p+1 graph eigenvalues lie in the positive window with probability tending to one. Write its largest and smallest eigenvalues as mu_+ and mu_-. Then

\[
\sqrt n(\mu_\pm-3-\kappa s)
\xrightarrow{P}\xi_\pm(p,\tau)
=\frac{\tau\pm\sqrt{\tau^2+4\kappa^2p}}2.
\tag{4}
\]

The other p-1 scaled shifts tend to tau. When p=0 there is just one eigenvalue in that window, whose scaled shift tends to zero.

For p>=1 the two extreme eigenvalues in the window are simple with probability tending to one. Put Delta=sqrt(tau squared+4 kappa squared p) and

\[
A_+=\tfrac12(1-\tau/\Delta),\qquad
A_-=\tfrac12(1+\tau/\Delta).
\tag{5}
\]

For either associated real unit graph eigenvector, its three squared masses converge in probability to

\[
\left(\frac{A_\pm}{2},\
\frac{1-A_\pm/2}{8},\
\frac{7(1-A_\pm/2)}8\right)
\tag{6}
\]

in the constant host direction, added vertices and perpendicular host component respectively. Up to overall sign, its retained direction converges to the corresponding eigenvector of

\[
\begin{pmatrix}0&\kappa\sqrt p\\\kappa\sqrt p&\tau\end{pmatrix}
\tag{7}
\]

in the basis c_+ and p^(-1/2)sum_j a_j^+. The p-1 dimensional dark subspace converges to the zero-sum combinations of the a_j^+. Individual vectors within that grouped subspace are not selected.

At tau=0, each of the two bright graph eigenvectors has masses

\[
(1/4,\ 3/32,\ 21/32).
\tag{8}
\]

The only host randomness appearing in these leading coefficients is the Poisson multiplicity p. There is no additional random entry in the leading two-dimensional mixing matrix.

## 3. Negative side at the same scale

Under (3), the p+1 negative-window graph eigenvalues, after centering at 3-kappa s and multiplying by sqrt(n), converge as an ordered multiset to

\[
\{0\}\cup\{-\tau\text{ with multiplicity }p\}.
\tag{9}
\]

If tau is nonzero, the collective eigenvector and the grouped antisymmetric pair subspace are separated at this scale. Their masses are respectively (1/2,1/16,7/16) and (0,1/8,7/8), uniformly on the unit sphere of the grouped pair subspace. When tau=0, equation (9) alone does not select them. The next theorem resolves exact leading resonance and most finer detunings.

## 4. The logarithmic negative splitting

Suppose instead that the finer parameter satisfies

\[
\frac{w-\kappa}{sr}\longrightarrow a\in\mathbb R.
\tag{10}
\]

This implies tau_n->0. Conditional on p_n=p, the p+1 negative-window graph eigenvalues have ordered shifts

\[
\left\{\frac{\mu-3+\kappa s}{s^2r}\right\}
\xrightarrow{P}
\left\{-\frac{\kappa^2}{2}\right\}
\cup\left\{-(a+\kappa^2)\text{ with multiplicity }p\right\}.
\tag{11}
\]

If a differs from -kappa squared/2, the collective eigenvalue is simple, its eigenvector converges under the physical lift to c_-, and the remaining p-dimensional subspace converges to the span of the a_j^-. The mass triples are the same pure collective and pair triples stated after (9).

In particular, at exact phase 1/2, w=kappa and a=0. The graph has

\[
\mu_{\rm coll}=3-\kappa s-\frac{\kappa^2}{2}s^2r
 +o_P(s^2r),
\]

\[
\mu_{\rm pair,j}=3-\kappa s-\kappa^2s^2r
 +o_P(s^2r).
\tag{12}
\]

Thus the negative collective eigenvalue is above the negative pair group by kappa squared times s squared r divided by two, to leading order. Exact leading resonance produces positive mixing at scale n^(-1/2), but a smaller deterministic negative separation at scale s squared r, of order n^(-2/3)log n.

At the retuned value a=-kappa squared/2, (11) has a repeated coefficient. The combined negative subspace remains identified, but this theorem does not identify its finer splitting or basis. This is a different, more finely tuned crossing from exact phase w=kappa.

## 5. Deterministic reduction for an isolated subspace

We state the finite estimate used in both applications. Let A_0 be self-adjoint, let Q be an orthogonal projector, and decompose it into blocks A_11,A_12,A_21,A_22. Suppose the spectrum of A_11 lies within g/4 of lambda_0, the spectrum of A_22 has distance at least g from lambda_0, and b=||A_21|| is sufficiently small compared with g. Then the spectral projection P_0 of A_0 onto the window about lambda_0 has rank rank(Q), and

\[
\|P_0-Q\|\le Cb/g.
\tag{13}
\]

The canonical isometry W=P_0 Q(QP_0Q)^(-1/2), from range(Q) onto range(P_0), satisfies

\[
\|W^T A_0 W-A_{11}\|
\le C\left(g^{-1}+\|A_0\|g^{-2}\right)b^2.
\tag{14}
\]

For (13), compare A_0 with its block diagonal part and integrate the resolvent identity on a circle of radius g/2 about lambda_0. The contour stays a fixed distance from both spectra when b is small. Rank equality follows because the projection difference is less than one.

For (14), put W_1=QW and W_2=(I-Q)W. The polar construction gives W_1=(QP_0Q)^(1/2) on range(Q). Also

\[
\|I-QP_0Q\|=\|(I-P_0)Q\|^2\le Cb^2/g^2.
\]

Hence ||W_1-I||<=Cb squared/g squared and ||W_2||<=Cb/g. Expand W^T A_0 W into its four blocks. The diagonal terms cost C||A_0||b squared/g squared, and the mixed terms cost Cb squared/g. This proves (14) without a dimension factor. In particular, a squared off-subspace norm that is o(epsilon) suffices for an effective approximation at scale epsilon.

## 6. Proof at the positive square-root scale

Let A_eff=U^T(mathcal A-3I)U/s. The subspace theorem gives

\[
\|A_{\rm eff}-T\|=O_P(s\log^2 n)=o_P(\delta).
\tag{15}
\]

The [selected-sector proof](../probability/refined-resolvent-v1.md), SHA256 bd00db6c2f69813d480f5a86d5d22c8b6fe4922d9cc3d233f72840dddb29f8df, compares T with the full-star short-pair matrix S_K. If Q selects the host coordinate, e, and the endpoints in V, it proves

\[
\|Q(T-S_K)Q\|=O_P(\log^3 n/m),\qquad
\|(T-S_K)Q\|^2=O_P(\log^4 n/m).
\tag{16}
\]

The smaller positive or negative reference space in (2) lies inside this selected coordinate space, since f is a linear combination of e and the endpoint coordinates. Thus (16) applies to each reference projection.

Fix K. On events where the number of short pairs and their largest scaled weight are bounded, direct multiplication of S_K gives, in the positive reference basis,

\[
Q_+ S_K Q_+
=\kappa I+\delta
\begin{pmatrix}0&\kappa\mathbf1_p^T\\
\kappa\mathbf1_p&\tau_n I_p\end{pmatrix}
O_P(1/m).
\tag{17}
\]

The star on the unselected coordinates has coefficient kappa sqrt(1-2p/m). Other retained pair blocks contribute only O_P(1/m) to its collective diagonal. Each selected symmetric pair has host coupling kappa/sqrt(m) to c_+. Its pair weight is w. The off-subspace column norm of S_K is O_P(m^(-1/2)). The bounded events exhaust probability because the short pair count and largest weight are tight.

For the negative reference basis the corresponding compression is

\[
Q_- S_K Q_-
=-\kappa I+\delta\operatorname{diag}(0,-\tau_n I_p)
O_P(1/m).
\tag{18}
\]

The host coupling to every antisymmetric vector is exactly zero. Its off-subspace norm has the same bound.

The complement has a fixed gap from the chosen level with probability tending to one. To justify this claim, first use the exact matching decomposition for S_K. Every other lattice level is separated by a fixed positive amount, and the reference collective vector changes by O_P(m^(-1/2)) if other short pairs are removed. The global comparison has limiting failure probability at most C 2^(-K) at a fixed small norm tolerance. Take n to infinity for fixed K and then K to infinity. This establishes the actual complementary gap, without a growing-cutoff assertion.

Equations (15)-(18) give compressed error O_P(log^4(n)/m) and squared off-subspace norm of that same order, apart from the complementary-gap exceptional event just controlled. Both are o_P(delta). Apply the finite lemma, first for fixed K and then let K increase in the failure bound. The compression on the actual level subspace is (17) or (18) up to o_P(delta), with a near-identity change of coordinates.

The positive matrix in (17) has the p-1 dark directions and the two-dimensional block (7). The [finite normal-form proof](../resonance/finite-normal-form-v1.md), SHA256 59bebac4b6a96d148d48830bf27130223d6820e53e16627720fb7f2f7216eed7, gives its eigenvalues and projectors. Distinct bright roots and their gaps from the dark value justify the simple-eigenvector conclusions. The mass identities of the subspace theorem convert collective fractions into (6). Since s delta=1/sqrt(n), the physical scaling in (4) follows exactly. The negative diagonal matrix gives (9) and its separated subspaces when tau is nonzero.

All these estimates are uniform on each fixed bound for p. Taking that bound to infinity handles the tight random dimension. Conditioning on a fixed p of positive limiting probability then gives the stated conditional convergence, without redoing any rare-event probability calculation under that conditioning.

## 7. A second-order graph normalization identity

The finer negative theorem requires retaining the metric correction. Define

\[
\Gamma=\operatorname{diag}(0,F'(3)/8-I),\qquad
\widehat T=T-\tfrac12(\Gamma T+T\Gamma).
\]

Then

\[
\|A_{\rm eff}-\widehat T\|
=O_P(\|\Gamma\|^2+s)=o_P(sr).
\tag{19}
\]

Here is the explicit proof. In the finite isometry construction, write P for the full graph-cluster projection and M=J^T P J. The exact Gram identity gives

\[
M=I+\Gamma-J^T(I-P)J=I+\Gamma+O_P(s^2),
\]

because ||(I-P)J||=O_P(s). Functional calculus near the identity gives

\[
M^{-1/2}=I-\Gamma/2+O_P(\|\Gamma\|^2+s^2).
\]

The exact compression identity proved in the subspace theorem is

\[
J^T P(\mathcal A-3I)P J/s=T+O_P(s).
\]

Multiplying on both sides by M^(-1/2), and using ||T||=O_P(1), proves the first equality in (19). The finite derivative bounds give ||Gamma||=O_P(s log^2 n). Since r has order log n and s has order 1/m, both s/(sr) and s squared log^4(n)/(sr) tend to zero. This proves the last equality.

Equation (19) is an operator estimate for the actual graph cluster. It is the missing normalization bridge in the separately frozen logarithmic probability argument.

## 8. Proof of the logarithmic graph theorem

The [logarithmic retained-matrix proof](../probability/negative-log-scale-v1.md), SHA256 faced6a02d91d451e4ef0e0989d3d46811da66d809d40e9344e9444012901409, proves, in the negative reference coordinates (2),

\[
Q_-\widehat T Q_-
=-\kappa I+sr\operatorname{diag}
(-\kappa^2/2,-(a+\kappa^2)I_p)+o_P(sr),
\tag{20}
\]

and squared complementary coupling O_P(1/m)=o_P(sr). It also supplies the complementary-gap argument with the fixed-cutoff order of limits.

By (19), replacing widehat T by A_eff changes (20) by o_P(sr). Its added squared column error is also o_P(sr), since the square of an o_P(sr) operator is o_P(sr), and cross terms are bounded by twice the sum of squares. The complementary gap persists. Apply the finite lemma (13)-(14). The resulting actual negative-level compression has the two coefficients in (11), up to o_P(sr).

If those coefficients are distinct, ordinary separated-projector perturbation at scale sr identifies the collective line and the grouped pair subspace. The isometries used in this reduction converge to the reference inclusion, and the full-cluster isometry U converges to the physical lift J. The previously proved mass operators therefore give the asserted graph masses. Multiplication of the retained displacement by s yields the physical scale s squared r and proves (11)-(12).

The two logarithmic coefficients have different sources. The collective term comes from the cancellation of the long-walk stationary contribution, leaving e^T(G-gI)e=-s^2r+o_P(s^2r). The pair term comes from the selected derivative metric, whose matching block is s(r+1)w times the pair adjacency. Normalization in (19) turns that metric into the extra negative pair shift. Omitting either term gives an incorrect finer prediction.

## 9. Integer tuning and failure of a phase-only basis law

All finite tau values in (3) are attainable by admissible integer n,m, by the construction in the finite normal-form proof. Thus the first-order phase alone does not determine positive mixing.

All finite logarithmic parameters a in (10) are also attainable. Choose m_j nearest to sqrt(2)c^(3/2)2^j, put s_0=1/(sqrt(2)2^j), and choose n_j nearest even to

\[
2m_j4^j\left(1+\frac{a j s_0}{\kappa}\right)^2.
\tag{21}
\]

The bracket tends to one. The resulting s equals s_0/(1+a j s_0/kappa) up to negligible rounding error, the distance floor is r=j, and w-kappa=a j s_0 plus negligible rounding error. Consequently (w-kappa)/(sr)->a and m/n^(1/3)->c. All these sequences have phase tending to 1/2 and tau_n tending to zero. At a=0, n_j=2m_j4^j gives exact phase for every j.

Nevertheless their negative eigenvector ordering differs. Conditional on p_n=1, at a=0 the larger eigenvalue within the negative window is collective and its constant-host mass tends to 1/2. At a=-kappa squared, the larger eigenvalue within that same window is a pair mode and its constant-host mass tends to zero. This is an actual random-graph distinction on events of positive limiting probability, not only a perturbation counterexample for an abstract matrix.

Therefore neither the first-order phase nor the additional assertion tau=0 determines an ordered negative eigenvector law. The logarithmic detuning resolves that ambiguity away from a=-kappa squared/2. At that exceptional retuned value a still finer analysis is required.

## 10. What is established and what remains

The graph subspace theorem, positive avoided crossing, negative logarithmic splitting at exact phase, and their separated mass laws are proved with explicit graph-to-matrix bridges. Integer distances do not prevent tuning the finer parameters. Multiplicities require grouped pair subspaces, and no arbitrary basis inside such a group is asserted to select a single pair.

The exactly retuned logarithmic crossing, including possible random coefficients and basis selection below scale sr, is not resolved here. The isolated finite-star coefficient of order 1/m is not transferred to the graph. These are narrower remaining questions than the original leading collective-pair resonance. The finite formal packet verifies supporting matrices and eigenvectors, while probability, projector perturbation, normalization asymptotics and physical mass transfer remain reviewed paper steps. Priority is assessed separately and no historical-firstness claim is made.
