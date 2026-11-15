# Finite collective-pair resonance and its precision boundary

Date: November 15, 2026, America/Los_Angeles. Revision 1, frozen for separate review.

Status: complete finite-matrix argument and an integer tuning construction. The transfer to the random graph is conditional on a sharper approximation stated below. No new random-graph estimate or historical-priority claim is made here.

Prior exposure: the critical-law proof and effective-operator proof, the assigned candidate resonance matrix, and the coordinator's proposed scale were known before this derivation. No new probability attempt or new graph subspace proof was read. The exact finite algebra below was derived from the displayed matrix.

## 1. Actual finite matrix and invariant coordinates

Fix kappa>0 and a positive integer p. Let m>2p and f=m-2p. On one host coordinate, f free coordinates and p disjoint pairs of coordinates, define the real symmetric matrix S_m as follows. The host is coupled to every one of the m other coordinates with coefficient kappa/sqrt(m). Each pair has off-diagonal weight w_m>0. Every other entry is zero.

For pair j, define unit symmetric and antisymmetric vectors

\[
 a_j=(e_{j,1}+e_{j,2})/\sqrt2,
 \qquad b_j=(e_{j,1}-e_{j,2})/\sqrt2.
\]

Let h denote the host unit vector, let u be the unit constant vector on the f free coordinates, and put a=p^(-1/2) sum_j a_j. Direct multiplication gives

\[
 S_m b_j=-w_m b_j,
 \qquad
 S_m a_j=w_m a_j+\kappa\sqrt{2/m}\,h.
\tag{1}
\]

Thus all p antisymmetric vectors are exact eigenvectors at -w_m. The symmetric vectors sum_j t_j a_j with sum_j t_j=0 form an exact eigenspace of dimension p-1 at +w_m. Free-coordinate vectors with coordinate sum zero form an exact zero eigenspace of dimension f-1.

The remaining three-dimensional invariant subspace has the orthonormal basis (h,u,a). Its matrix is exactly

\[
 R_m=\begin{pmatrix}
 0&\alpha_m&\beta_m\\
 \alpha_m&0&0\\
 \beta_m&0&w_m
 \end{pmatrix},
 \qquad
 \alpha_m=\kappa\sqrt{1-2p/m},
 \quad \beta_m=\kappa\sqrt{2p/m}.
\tag{2}
\]

The dimensions p+(p-1)+(f-1)+3 sum to m+1. Hence this is a full orthogonal decomposition, including multiplicities. Its characteristic polynomial on the last subspace is

\[
 \det(zI-R_m)
 =(z-w_m)(z^2-\kappa^2)-\frac{2\kappa^2p w_m}{m}.
\tag{3}
\]

Indeed, expansion first gives (z-w_m)(z squared-alpha_m squared)-beta_m squared times z. Substituting alpha_m squared=kappa squared minus beta_m squared gives (3).

All these identities are exact for each m. Antisymmetric cancellation does not assume w_m is close to kappa.

## 2. Positive resonance at the square-root scale

Put delta_m=m^(-1/2) and assume

\[
 \tau_m=\delta_m^{-1}(w_m-\kappa)\longrightarrow\tau\in\mathbb R.
\tag{4}
\]

Define c_+=(h+u)/sqrt(2) and c_-=(h-u)/sqrt(2). In the ordered basis (c_+,a,c_-), equation (2) becomes

\[
 \begin{pmatrix}
 \alpha_m&g\delta_m&0\\
 g\delta_m&w_m&g\delta_m\\
 0&g\delta_m&-\alpha_m
 \end{pmatrix},
 \qquad g=\kappa\sqrt p.
\tag{5}
\]

Here alpha_m=kappa+O(delta_m squared). The two eigenvalues of this matrix near +kappa satisfy

\[
 z_{m,\pm}=\kappa+\delta_m\xi_\pm+o(\delta_m),
 \qquad
 \xi_\pm=\frac{\tau\pm\sqrt{\tau^2+4\kappa^2p}}2.
\tag{6}
\]

Their normalized eigenvectors converge, up to sign and in the moving coordinates (c_+,a,c_-), to the two normalized eigenvectors of

\[
 M_\tau=\begin{pmatrix}0&\kappa\sqrt p\\
 \kappa\sqrt p&\tau\end{pmatrix}
\tag{7}
\]

embedded with zero c_- coordinate. In addition there are p-1 exact positive dark eigenvalues w_m, whose scaled shifts tend to tau.

For completeness, these conclusions follow directly from (5). Its difference from diag(kappa,kappa,-kappa) is O(delta_m), so exactly two roots lie near kappa and their scaled shifts are bounded. For an eigenvector (x,y,t) at z near kappa, its third equation gives

\[
 t=\frac{g\delta_m}{z+\alpha_m}y=O(\delta_m)y.
\]

Substitution in the first two equations and division by delta_m gives the effective two-by-two eigenvalue equation with matrix

\[
 \begin{pmatrix}
 (\alpha_m-\kappa)/\delta_m&g\\
 g&\tau_m+g^2\delta_m/(z+\alpha_m)
 \end{pmatrix}.
\tag{8}
\]

This converges uniformly for bounded scaled z to (7). Its two distinct roots are (6), because p>0. The eliminated coordinate tends to zero, while x squared plus y squared tends to one. The same equations identify each limiting rank-one eigenprojector. This proves both the eigenvalue and eigenvector conclusions without choosing a basis in the dark eigenspace.

Write Delta=sqrt(tau squared+4 kappa squared p). The upper branch has collective mass and aggregate pair mass

\[
 |\langle c_+,v_+\rangle|^2=\frac12(1-\tau/\Delta),
 \qquad
 |\langle a,v_+\rangle|^2=\frac12(1+\tau/\Delta)
\tag{9}
\]

in the limit. The lower branch interchanges these two values. These formulas follow from the spectral projector (M_tau-xi_- I)/Delta. At tau=0, both masses are one half. The actual host coordinate of the finite matrix has half the collective mass. These are finite-matrix masses, not yet masses in the original graph eigenvectors.

## 3. The negative side and a finer exact crossing

The third eigenvalue of R_m tends to -kappa. Equation (3) implies

\[
 z_{m,-\mathrm{coll}}
 =-\kappa+\frac{\kappa p}{2m}+o(m^{-1}).
\tag{10}
\]

To see this, isolate z+kappa in (3). The product (z-w_m)(z-kappa) tends to 4 kappa squared and w_m tends to kappa. Multiplication by m then gives the coefficient kappa p/2. The normalized eigenvector in this three-dimensional sector tends to c_-.

By contrast, the p antisymmetric pair vectors remain exact eigenvectors at -w_m. Therefore the whole negative resonant cluster, centered at -kappa and divided by delta_m, has limiting matrix

\[
 \operatorname{diag}(0,-\tau I_p)
\tag{11}
\]

in its collective and antisymmetric pair coordinates. There is no avoided crossing at this scale in the finite model. When tau=0, (11) is fully degenerate.

Even the exact finite model can have a negative eigenvalue coincidence. Substituting z=-w_m into (3) gives the crossing condition

\[
 w_m^2=\kappa^2(1-p/m).
\tag{12}
\]

This falls within tau=0. The invariant collective and antisymmetric spaces are still defined, but an arbitrary eigenvector of a repeated eigenvalue can mix them. Exact cancellation is not a license to identify every eigenvector with one chosen pair vector.

The coefficient in (10) applies to the matrix with just these p pair blocks. Additional nonresonant pair blocks generally change the order m^(-1) collective correction.

## 4. Other finitely many pair levels

The positive normal form survives the presence of a fixed number r of additional pair blocks of positive weights v_(m,j), provided their weights are uniformly bounded and their distances from kappa are bounded below by a positive constant. Replace f by m-2(p+r), retain the resonant aggregate a, and use one symmetric coordinate for each additional pair.

Every additional symmetric coordinate has host coupling kappa sqrt(2/m). The antisymmetric coordinate still decouples exactly. In the positive resonant decomposition, the complementary eigenvalues have a fixed gap from kappa, while all couplings to that complement have size O(delta_m). The complementary Schur resolvent is uniformly bounded. Its correction to the resonant block is therefore O(delta_m squared). The collective diagonal change caused by replacing p with p+r in alpha_m is also O(delta_m squared). After division by delta_m these corrections vanish, leaving (7) and its p-1 dark directions.

This argument is uniform when p and r range over a fixed finite bound and the weight and gap bounds are fixed. It does not treat an infinite collection of weak levels or assert a bound for the actual random-graph remainder.

## 5. Integer tuning in the cubic model

For the original critical cubic model,

\[
 \kappa=3/\sqrt8,\qquad h=3/4,\qquad
 w_{n,\ell}=h\,2^{-\ell}/s,\qquad s=\sqrt{m/n}.
\]

At offset zero, ell=r_n=floor(log_2(1/s)). The resonant phase is phi=1/2, since h times sqrt(2)=kappa. Equivalently,

\[
 \frac{w_{n,r_n}}\kappa
 =\sqrt{\frac{n}{2m4^{r_n}}}.
\tag{13}
\]

For any c>0 and any prescribed finite tau, choose an integer m_j nearest to sqrt(2)c^(3/2)2^j. Let n_j be a nearest even integer to

\[
 2m_j4^j\left(1+\frac{\tau}{\kappa\sqrt{m_j}}\right)^2.
\tag{14}
\]

For sufficiently large j the bracket is positive. The bounded rounding error in n_j has vanishing relative size and vanishes even after multiplication by sqrt(m_j). Direct substitution gives

\[
 \frac{m_j}{n_j^{1/3}}\longrightarrow c,
 \qquad r_{n_j}=j,
 \qquad
 \sqrt{m_j}(w_{n_j,j}-\kappa)\longrightarrow\tau.
\tag{15}
\]

Indeed, the first limit follows from m_j squared divided by 2 times 4^j tending to c cubed. The logarithm of 1/s is j+1/2+o(1), which identifies its floor. Equation (13) then proves the last limit. Even n_j are admissible sizes for simple cubic graphs once sufficiently large. At tau=0, taking n_j=2m_j4^j gives exact phase 1/2 and exact w=kappa for every j.

Thus integer constraints do not force tau=0 or select one positive mixing angle. All these size sequences have the same first-order phase limit. Their finite normal forms have different weights (9). Phase alone cannot determine next-scale positive mixing when a resonant pair is present. This is a statement about the displayed finite reduction and admissible parameters, not an unconditional random-graph mixing theorem.

## 6. Conditional graph bridge and a precise limitation

Suppose a graph-to-matrix isometry, or another justified reduction, identifies its resonant cluster with the finite model above plus a self-adjoint error E_m satisfying

\[
 \|E_m\|=o_{\mathbb P}(\delta_m).
\tag{16}
\]

Assume also the stated fixed gap from other levels. Then Weyl's bound gives (6) for the perturbed eigenvalues. The positive branch gaps from each other and from the dark level are positive constants times delta_m. Standard spectral-subspace perturbation bounds therefore transfer their rank-one projectors and the grouped dark subspace. When tau is nonzero, the negative collective projector and the grouped antisymmetric pair subspace transfer at the same precision. Individual vectors inside a repeated dark or antisymmetric subspace are not selected.

In the graph's unscaled adjacency units, delta_m corresponds to s/sqrt(m)=n^(-1/2). A first-order o_P(1) approximation in scaled coordinates is insufficient for (16). A proof of (16), or weaker sufficient estimates on the selected blocks and their Schur complements, is an additional random-graph obligation.

At tau=0, even (16) does not determine individual negative eigenvectors or transfer (10). An explicit precision counterexample uses p=1 and w_m=kappa. Let u_m and b be exact orthonormal negative collective and antisymmetric eigenvectors of S_m. Add

\[
 E_m=m^{-3/4}(u_m b^\top+b u_m^\top).
\tag{17}
\]

Its norm is m^(-3/4)=o(delta_m). The original separation is kappa/(2m)+o(m^(-1)), which is smaller than this perturbation. The two perturbed eigenvectors therefore approach equal mixtures of u_m and b. For E_m=0 they remain in the separate invariant directions. Both errors satisfy (16), yet give different finer bases. This is a counterexample to an inference from the error bound alone, not a constructed random-graph counterexample.

The robust negative conclusion at tau=0 is the full resonant subspace and zero next-scale splitting. Selecting its finer basis requires stronger estimates or additional exact graph structure. The positive avoided-crossing coefficient, negative cancellation and integer tuning are proved above independently of that unresolved graph question.

## 7. Attribution and review request

The effective two-by-two reduction is ordinary degenerate perturbation theory. Projector stability across a separated spectral cluster is standard subspace perturbation theory. The companion priority audit records inspected primary sources. No novelty is claimed for these tools, for bright and dark coordinates, or for avoided crossings in general.

Requested separate review: verify the exact characteristic polynomial, factors of sqrt(2), signs of the negative correction, dimension counts, integer tuning and the distinction between the finite theorem, conditional graph transfer and the tau=0 precision obstruction. The random-graph claim may be upgraded only by a separately frozen and reviewed probability and isometry bridge.
