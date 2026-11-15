# A finite error bound for a growing resonant spectral cluster

November 15, 2026, America/Los_Angeles.

Status at freezing: complete paper argument awaiting separate review. The Schur complement, inertia and eigenvalue perturbation tools are classical. No novelty claim attaches to those tools or to growing-rank transfer in general.

## 1. Exact finite-dimensional statement

Let A be a real symmetric n by n matrix. Let u be a unit vector with Au=d u. Write Q=I-uu^\top and A_Q for the restriction to u perpendicular. Assume

\[
\lambda_{\max}(A_Q)\le d-\gamma,\qquad \gamma>0.
\tag{1}
\]

Let B be an n by m real matrix, m>=1, and let C be real symmetric m by m. Define

\[
\mathcal A=\begin{pmatrix}A&B\\B^\top&C\end{pmatrix},
\qquad b=B^\top u,
\]

\[
F(z)=zI_m-C-B^\top Q(zI-A_Q)^{-1}QB.
\tag{2}
\]

The inverse acts only on the space perpendicular to u. It is not the full inverse of zI-A at its pole.

Let D be real symmetric positive definite with \(\lambda_{\min}(D)\ge a>0\). Let Z be any real symmetric m by m matrix. Put M=||B|| and

\[
T=
\begin{pmatrix}
0&b^\top D^{-1/2}\\
D^{-1/2}b&-D^{-1/2}ZD^{-1/2}
\end{pmatrix}.
\tag{3}
\]

For \(0<h<\gamma\), set

\[
\eta_h=\frac1a\left(
\|F(d)-Z\|+h\|F'(d)-D\|
+\frac{M^2h^2}{(\gamma-h)^3}
\right).
\tag{4}
\]

If

\[
\|T\|+\eta_h<h,
\tag{5}
\]

then exactly m+1 eigenvalues of \(\mathcal A\), counted with multiplicity, lie in \((d-h,d+h)\), and these are its largest m+1 eigenvalues. If they are denoted \(\mu_1\ge\cdots\ge\mu_{m+1}\), and the eigenvalues of T are \(\theta_1\ge\cdots\ge\theta_{m+1}\), then

\[
\max_{1\le j\le m+1}|\mu_j-d-\theta_j|\le\eta_h.
\tag{6}
\]

Moreover,

\[
\mu_{m+2}\le\lambda_2(A)\le d-\gamma
\tag{7}
\]

whenever that index exists. The constants in (4) have no additional dependence on m or n.

## 2. The exact reduction and eigenvalue count

Choose an orthonormal basis whose first host vector is u, and reorder the coordinates as the host complement, u, and the new coordinates. For z in [d-h,d+h], the host-complement block

\[
L(z)=zI-A_Q
\]

is positive definite. Eliminating that block by an invertible triangular congruence reduces \(zI-\mathcal A\) to the direct sum of L(z) and

\[
K(z)=
\begin{pmatrix}
z-d&-b^\top\\
-b&F(z)
\end{pmatrix}.
\tag{8}
\]

For completeness, for any symmetric block matrix \(\begin{pmatrix}L&V\\V^\top&J\end{pmatrix}\) with invertible L, the matrix

\[
U=\begin{pmatrix}I&-L^{-1}V\\0&I\end{pmatrix}
\]

satisfies

\[
U^\top
\begin{pmatrix}L&V\\V^\top&J\end{pmatrix}U
=\begin{pmatrix}L&0\\0&J-V^\top L^{-1}V\end{pmatrix}.
\]

Sylvester's law of inertia therefore gives the exact identity

\[
\#\{j:\mu_j(\mathcal A)>z\}
=n_-(K(z)),
\tag{9}
\]

where \(n_-\) counts strictly negative eigenvalues with multiplicity. There is no pole at d in K.

## 3. Uniform linearization

Differentiation of the actual resolvent gives

\[
F'(z)=I_m+B^\top Q(zI-A_Q)^{-2}QB,
\]

\[
F''(z)=-2B^\top Q(zI-A_Q)^{-3}QB.
\tag{10}
\]

Consequently, on the whole interval,

\[
\|F''(z)\|\le\frac{2M^2}{(\gamma-h)^3}.
\]

The integral Taylor remainder proves, for every |t|<=h,

\[
\|F(d+t)-Z-tD\|
\le\|F(d)-Z\|+h\|F'(d)-D\|
+\frac{M^2h^2}{(\gamma-h)^3}.
\tag{11}
\]

Congruence of K(d+t) by \(S=\operatorname{diag}(1,D^{-1/2})\) yields

\[
\widetilde K(t)=SK(d+t)S=tI_{m+1}-T+\mathcal E(t),
\qquad \|\mathcal E(t)\|\le\eta_h.
\tag{12}
\]

The error has only a lower-right block. Multiplication on both sides by \(D^{-1/2}\) costs at most 1/a, giving exactly (4).

## 4. Ordered spectral comparison

Order the eigenvalues of \(\widetilde K(t)\) increasingly as \(\kappa_j(t)\), j=1,...,m+1. Since the increasingly ordered eigenvalues of \(tI-T\) are \(t-\theta_j\), Weyl's inequality gives

\[
|\kappa_j(t)-(t-\theta_j)|\le\eta_h.
\tag{13}
\]

At t=-h all eigenvalues are strictly negative, and at t=h all are strictly positive, by (5). Equation (9) shows that exactly m+1 eigenvalues of \(\mathcal A\) lie strictly between d-h and d+h and none lie above d+h.

Fix j and take any sufficiently small \(\xi>0\). At

\[
t=\theta_j+\eta_h+\xi
\]

equation (13) gives \(\kappa_j(t)>0\). Thus there are at most j-1 negative eigenvalues, and (9) implies \(\mu_j\le d+t\). At

\[
t=\theta_j-\eta_h-\xi
\]

it gives \(\kappa_j(t)<0\). There are at least j negative eigenvalues, so \(\mu_j>d+t\). All test points lie in (-h,h) when xi is sufficiently small, by (5). Letting xi decrease to zero proves (6). This argument covers repeated effective eigenvalues and growing multiplicities without differentiating individual eigenvalue branches.

Finally, A is a principal submatrix of \(\mathcal A\). Principal-submatrix interlacing after adding m rows and columns gives \(\mu_{m+2}\le\lambda_2(A)\). This proves (7) and finishes the finite theorem.

## 5. A structural asymptotic consequence

Consider any sequence of these matrices, with m allowed to grow. Assume that gamma and a are bounded below by positive constants, ||B|| is bounded, and \(s_n\to0\). Suppose

\[
\|T_n\|\le C s_n,\qquad
\|F_n(d_n)-Z_n\|=o(s_n),\qquad
\|F_n'(d_n)-D_n\|=o(1).
\tag{14}
\]

Choose h_n=L s_n with fixed L>C+1. Formula (4) gives \(\eta_{h_n}=o(s_n)\), and (5) holds eventually. Therefore all m+1 near-resonant eigenvalues are approximated in ordered maximum error o(s_n) by the eigenvalues of T_n.

The same conclusion holds in probability if the hypotheses hold on events whose probability tends to one and the error statements hold in probability. Indeed, the deterministic theorem applies on the intersection of those events with \(\eta_{h_n}/s_n<L-C\). Its probability tends to one.

This is a whole-cluster statement. The reference Z_n may retain nontrivial detuning or interactions, rather than replacing them by zero. No limiting empirical distribution for T_n is needed.

## 6. The collective and orthogonal modes

When Z=0, write \(v=D^{-1/2}b\), \(\beta=\|v\|\). If beta>0, the matrix T acts on pairs \((x,y)\in\mathbb R\oplus\mathbb R^m\) by

\[
T(x,y)=(\langle v,y\rangle,xv).
\]

Its two unit eigenvectors

\[
\frac1{\sqrt2}(1,v/\beta),\qquad
\frac1{\sqrt2}(1,-v/\beta)
\]

have eigenvalues beta and -beta. The orthogonal subspace \(\{(0,y):\langle v,y\rangle=0\}\) has dimension m-1 and eigenvalue zero. These spaces give the complete orthogonal decomposition. If beta=0 then T=0.

For D=8I and \(b=3\mathbf1_m/\sqrt n\), this yields

\[
\beta=\frac3{\sqrt8}\sqrt{\frac mn}.
\]

The intermediate modes are the combinations of defects perpendicular to their common coupling vector. Their smaller-scale behavior remains in the error or in an explicitly retained Z. The zero effective eigenvalues are not a claim that the corresponding finite-graph eigenvalues equal d exactly.

## 7. Scope

This statement requires an isolated host mode with a fixed gap to the complementary spectrum. It does not treat a resonance at the bulk edge, where the inverse and derivative bounds degenerate. It concerns adjacency or another specified symmetric operator, not automatically random-walk mixing. Its application to random graphs requires independent verification of (14) for the actual localized perturbation.
