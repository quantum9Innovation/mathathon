# General separated-scale matrix-power limit

This self-contained lemma supplies the reverse-Schur/LDU generalization of the rank-one construction. It applies to an arbitrary fixed positive definite matrix and uniformly to compact positive definite families.

## Statement

Let \(0<\alpha<1\), let \(S\in\mathbb R^{n\times n}\) be positive definite, and put

\[
 a_i=\delta^{n-i},\quad
 D_\delta=\operatorname{diag}(a_i),\quad
 B_\delta=D_\delta^{1/2}S D_\delta^{1/2},
 \qquad 0<\delta<1.
\]

Define the reverse Schur pivots

\[
 p_i=S_{ii}-S_{i,>i}S_{>i,>i}^{-1}S_{>i,i}
     =\frac{\det S_{i:n,i:n}}{\det S_{i+1:n,i+1:n}},
\]

where the empty determinant is one. Then

\[
 D_\delta^{-\alpha/2}B_\delta^\alpha D_\delta^{-\alpha/2}
 \longrightarrow\operatorname{diag}(p_1^\alpha,\ldots,p_n^\alpha)
\]

in operator norm as \(\delta\downarrow0\). The convergence is uniform as \(S\) ranges over an arbitrary compact subset of the positive definite cone.

## Diagonal entries

Write \(c_\alpha=\sin(\pi\alpha)/\pi\). The fractional-power formula is

\[
 B^\alpha=c_\alpha\int_0^\infty
 t^{\alpha-1}B(B+tI)^{-1}\,dt.
\]

For its \(i\)-th normalized diagonal, substitute \(t=a_i s\):

\[
 a_i^{-\alpha}(B_\delta^\alpha)_{ii}
 =c_\alpha\int_0^\infty s^{\alpha-1}
 \left[1-s(S+s a_iD_\delta^{-1})^{-1}_{ii}\right]ds.
\]

For every fixed \(s>0\), the first \(i-1\) diagonal entries of \(s a_iD_\delta^{-1}\) diverge, its \(i\)-th entry is \(s\), and its remaining entries tend to zero. Partitioning before index \(i\), the inverse of the earlier principal block tends to zero. Its Schur complement on indices \(i:n\) tends to

\[
 S_{i:n,i:n}+s e_1e_1^T.
\]

Its inverse \((1,1)\)-entry is \((p_i+s)^{-1}\). Consequently the bracket tends to \(p_i/(p_i+s)\).

Choose \(M\) with \(S\preceq MI\). Then \(B_\delta\preceq MD_\delta\). The inverse-order identity shows that the function \(X\mapsto X(X+tI)^{-1}\) preserves positive semidefinite order. Thus

\[
 0\leq[B_\delta(B_\delta+a_i s I)^{-1}]_{ii}
 \leq\frac{M}{M+s}.
\]

The function \(s^{\alpha-1}M/(M+s)\) is integrable on \((0,\infty)\). Dominated convergence yields

\[
 a_i^{-\alpha}(B_\delta^\alpha)_{ii}
 \longrightarrow
 c_\alpha\int_0^\infty s^{\alpha-1}\frac{p_i}{p_i+s}\,ds
 =p_i^\alpha.
\]

## Off-diagonal entries

Set \(E=S-I\), \(m=\lambda_{\min}(S)>0\),

\[
 W_t=\operatorname{diag}\sqrt{\frac{a_i}{a_i+t}},
 \qquad H_t=I+W_t E W_t.
\]

Then

\[
 B_\delta+tI=(D_\delta+tI)^{1/2}
 H_t(D_\delta+tI)^{1/2},\qquad
 H_t\succeq\min(1,m)I.
\]

The elementary second resolvent identity gives

\[
 H_t^{-1}-I=-W_t K_t W_t,\qquad
 K_t=E-EW_tH_t^{-1}W_tE.
\]

In particular,

\[
 \|K_t\|\leq K_S:=[\|S-I\|+\|S-I\|^2/\min(1,m)]
\]

uniformly in \(t\) and \(\delta\). For \(i\ne j\), since the resolvent of \(D_\delta\) is diagonal,

\[
 |(B_\delta+tI)^{-1}_{ij}|
 \leq K_S\frac{\sqrt{a_i a_j}}{(a_i+t)(a_j+t)}.
\]

The off-diagonal fractional integral and the scalar divided-difference identity now give

\[
 \begin{aligned}
 |(D_\delta^{-\alpha/2}B_\delta^\alpha
                      D_\delta^{-\alpha/2})_{ij}|
 &\leq K_S(a_i a_j)^{(1-\alpha)/2}
     \frac{a_j^\alpha-a_i^\alpha}{a_j-a_i}\\
 &=K_S x^{(1-\alpha)/2}\frac{1-x^\alpha}{1-x},
 \quad x=a_i/a_j,\quad i<j.
 \end{aligned}
\]

This tends to zero. Symmetry treats \(i>j\), and fixed-dimensional entrywise convergence proves norm convergence.

## Uniformity and the rank-one specialization

On a compact positive definite family, \(m\) has a common positive lower bound, \(M\) and \(\|S-I\|\) have common finite upper bounds, and every trailing principal inverse is bounded. The finite-dimensional Schur-complement convergence above is therefore uniform for each fixed \(s>0\). Apply dominated convergence to the supremum of the diagonal-integrand errors, using the same common integrable majorant. The off-diagonal bound is already uniform. This proves the asserted uniform convergence.

For \(S=I+vv^T\), \(v_i^2=z_i\), the determinant lemma gives

\[
 p_i=\frac{1+\sum_{j\geq i}z_j}{1+\sum_{j>i}z_j}.
\]

Choosing \(z_i=(r_i-1)\prod_{j>i}r_j\) gives \(p_i=r_i\), exactly recovering the rank-one separated-scale lemma.

The conclusion is special to \(0<\alpha<1\): at \(\alpha=1\), the normalized matrix is exactly \(S\), whose off-diagonal entries generally persist. Above one the displayed off-diagonal estimate no longer tends to zero, and in simple two-dimensional examples the normalized off-diagonal entries diverge.
