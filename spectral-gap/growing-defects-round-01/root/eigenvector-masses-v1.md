# Mass and direction of the collective defect modes

November 15, 2026, America/Los_Angeles.

Status at freezing: complete paper extension awaiting separate exact-revision review. This note uses the H=0 case of the frozen growing-defect graph theorem. It does not assert spatial localization of the full host component or a bulk-edge transition.

## 1. Statement

Use the fixed-d weighted model of [graph-theorem-v1.md](graph-theorem-v1.md) with H=0, deterministic marked labels, and \(m^3(\log n)^2/n\to0\). In particular,

\[
\mathcal A_n=
\begin{pmatrix}A_n&B_n\\B_n^\top&0\end{pmatrix},
\qquad B_n=\sqrt{d-2}\,A_nE,
\]

\[
s_n=\sqrt{m/n},\qquad
D=D_d=\frac{2(d-1)^2}{(d-2)^2},\qquad
\kappa=\kappa_d>0,\qquad e=e_m=m^{-1/2}\mathbf1_m.
\]

Write a real unit eigenvector of \(\mathcal A_n\) as \(\psi=(h,y)\), where h is its original-host component and y is its new-vertex component. Let

\[
u=n^{-1/2}\mathbf1,\qquad x=\langle u,h\rangle,\qquad h_\perp=Qh.
\]

For the top eigenvalue \(\mu_1\), put sigma=1. For \(\mu_{m+1}\), put sigma=-1. With probability tending to one these two eigenvalues are simple, and for either associated unit eigenvector, with arbitrary sign,

\[
x^2\xrightarrow{\mathbb P}\frac12,\qquad
\|y\|^2\xrightarrow{\mathbb P}\frac1{2D},\qquad
\|h_\perp\|^2\xrightarrow{\mathbb P}\frac{D-1}{2D},
\tag{1}
\]

\[
\|\sqrt D\,y-\sigma x e\|\xrightarrow{\mathbb P}0.
\tag{2}
\]

For m>=2, the following statements hold uniformly over every real unit eigenvector whose eigenvalue is one of \(\mu_2,\ldots,\mu_m\):

\[
x^2=o_{\mathbb P}(1),\qquad
\left|\|y\|^2-\frac1D\right|=o_{\mathbb P}(1),\qquad
\left|\|h_\perp\|^2-\frac{D-1}{D}\right|=o_{\mathbb P}(1),
\tag{3}
\]

\[
|\langle e,y\rangle|=o_{\mathbb P}(1).
\tag{4}
\]

Uniformly means that the supremum of each displayed error over those unit eigenvectors tends to zero in probability. It does not include arbitrary linear combinations of eigenvectors with distinct eigenvalues. Repeated middle eigenvalues and arbitrary choices of basis within their eigenspaces are covered.

For the unweighted cubic model, D=8. Each of the two collective modes has asymptotically one half of its squared norm in the host constant direction, one sixteenth on the added vertices, and seven sixteenths in the perpendicular host component. Each intermediate unit eigenvector has asymptotic added-vertex mass one eighth and perpendicular-host mass seven eighths, with vanishing mass in the constant host direction.

## 2. Inputs and exact eigenvector reconstruction

The graph theorem gives exactly m+1 eigenvalues in \(d+[-Ls_n,Ls_n]\) with probability tending to one, where L is fixed. Uniformly in j,

\[
\frac{\mu_1-d}{s_n}\to\kappa,\qquad
\frac{\mu_{m+1}-d}{s_n}\to-\kappa,\qquad
\max_{2\le j\le m}\frac{|\mu_j-d|}{s_n}\to0.
\tag{5}
\]

All convergences here and below are in probability. When m=1, the middle maximum is omitted. Interlacing and the host gap place the next eigenvalue below d by a fixed positive amount.

On that same good event, for any one of these eigenvalues z the host-complement inverse exists. The original eigenvector equation gives exactly

\[
h_\perp=(zI-A_Q)^{-1}QB_ny,
\]

\[
K(z)\binom{x}{y}=0,\qquad
K(z)=
\begin{pmatrix}
z-d&-b^\top\\
-b&F(z)
\end{pmatrix},
\quad b=B_n^\top u.
\tag{6}
\]

The pair (x,y) is nonzero. Otherwise the first identity would give h_perp=0 and the full eigenvector would be zero.

Because the inverse is real symmetric, unit normalization gives the exact identity

\[
1=x^2+y^\top
\left(I+B_n^\top Q(zI-A_Q)^{-2}QB_n\right)y
=x^2+y^\top F'(z)y.
\tag{7}
\]

The derivative approximation at d and the dimension-free second-derivative bound of the graph proof imply

\[
\sup_{|z-d|\le Ls_n}\|F'(z)-DI_m\|\to0.
\tag{8}
\]

There is no factor m in this step. It follows by adding \(Ls_n\sup\|F''\|\) to the derivative error at d.

## 3. The normalized effective vector

Put

\[
w=\binom{x}{\sqrt D\,y}.
\]

Since ||y||<=1 for a full unit eigenvector, equations (7) and (8) yield, uniformly over all relevant eigenvectors,

\[
|\|w\|^2-1|
=|y^\top(DI-F'(z))y|\to0.
\tag{9}
\]

Use the same congruence \(S=\operatorname{diag}(1,D^{-1/2}I_m)\) as the finite transfer theorem. Equation (6), with \((x,y)=Sw\), implies

\[
\left((z-d)I-s_n\mathcal M_{d,m}(0)+\mathcal E_n(z-d)\right)w=0.
\]

The graph proof bounds

\[
\sup_{|t|\le Ls_n}\frac{\|\mathcal E_n(t)\|}{s_n}\to0.
\]

As ||w|| is uniformly bounded, this proves the uniform residual estimate

\[
\left\|
\left(\mathcal M_{d,m}(0)-\frac{z-d}{s_n}I\right)w
\right\|\to0.
\tag{10}
\]

This is a statement about the actual full eigenvectors reconstructed through the Schur equations, not an assumption that they equal effective eigenvectors.

## 4. Two collective modes

The effective matrix has the exact orthonormal eigenvectors

\[
v_+=\frac1{\sqrt2}\binom1e,\qquad
v_-=\frac1{\sqrt2}\binom1{-e},
\]

with eigenvalues kappa and -kappa. Its orthogonal complement consists of \((0,v)\) with v perpendicular to e and has eigenvalue zero.

For z=mu_1, equation (5) gives (z-d)/s_n→kappa. All other effective eigenvalues are separated from this value by at least kappa/2 on events of probability tending to one. Decomposing w into the three exact orthogonal sectors in (10) therefore shows

\[
\|(I-v_+v_+^\top)w\|\to0.
\]

Together with (9), this gives \(|\langle v_+,w\rangle|^2\to1\). Hence \(x^2\to1/2\), \(D\|y\|^2\to1/2\), and \(\|\sqrt D\,y-xe\|\to0\). The same argument at z=mu_(m+1) gives the negative sign in (2).

The two actual eigenvalues are simple with probability tending to one. For m>=2, the ordered comparison (5) separates each from its nearest middle eigenvalue by a positive multiple of s_n. For m=1, it separates them from each other. The fixed host gap and interlacing separate mu_(m+1) from every remaining eigenvalue.

Finally, orthogonality of the host decomposition gives

\[
\|h_\perp\|^2=1-x^2-\|y\|^2,
\]

which proves the last limit in (1).

## 5. Intermediate modes

For an intermediate eigenvalue z, equation (5) gives (z-d)/s_n→0 uniformly. Combining this with (9) and (10) proves

\[
\|\mathcal M_{d,m}(0)w\|\to0
\]

uniformly over its unit eigenvectors. But the explicit block action gives

\[
\|\mathcal M_{d,m}(0)w\|^2
=\kappa^2\left(x^2+D|\langle e,y\rangle|^2\right).
\tag{11}
\]

Since kappa is a fixed positive constant, x→0 and \(\langle e,y\rangle\to0\) uniformly. Equation (9) then gives \(D\|y\|^2\to1\), and the exact full normalization gives the remaining host mass. This proves (3) and (4), without choosing a basis in a repeated middle eigenspace.

All suprema are well defined on the finite graph probability space. The estimates hold uniformly on the unit spheres of the specified eigenspaces. On exceptional events, the theorem makes no spectral classification and the quantities may be extended arbitrarily for convergence statements.

## 6. Meaning and limits

At criticality the two extreme modes are hybrids. Half their mass remains in the extended constant direction of the original host. The result does not call them purely localized eigenvectors. The intermediate modes have no leading constant component and involve combinations of defects orthogonal to the common coupling.

Neither the mass law nor its effective-vector direction asserts a decay profile in graph distance. Such a claim would need a separate spatial resolvent estimate. The theorem does not give the residual eigenvalue scale of the intermediate modes, and it does not describe the H nonzero case near collisions of its effective eigenvalues.

The proof uses the same frozen probability input and deterministic transfer as graph-theorem-v1.md. No additional random-graph theorem, numerical approximation or independence assumption is used.
