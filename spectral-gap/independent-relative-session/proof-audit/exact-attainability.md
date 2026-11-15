# Independent proof audit and exact attainability upgrade

Audit date: 2026-11-15. Scope: `spectral-gap/relative-fractional-response.tex` as read during this session. No root manuscript was edited.

## Verdict on the existing separated-scale proof

The stated spectral-closure theorem, fixed-dimensional count, and the separated-scale rank-one lemma are correct. In particular, the off-diagonal estimate contains the essential factor

\[
 (a_i/a_j)^{(1-\alpha)/2}
 \frac{1-(a_i/a_j)^\alpha}{1-a_i/a_j},\qquad i<j,
\]

which tends to zero precisely in the stated range \(0<\alpha<1\). The diagonal dominated-convergence argument is valid, including cases \(z_i=0\). The leverage telescoping identity is exact, rather than asymptotic. The fixed-dimensional count follows because its equal-positive target is used only as a limit with a strict margin above the threshold.

There is a stronger exact theorem: **the attainable spectra are exactly the admissible lists whose entries strictly above one are pairwise distinct.** Thus every strictly positive collision is excluded at finite condition number, while every admissible simple positive list is attained exactly. The closure theorem follows immediately.

## Exact attainable-spectrum theorem

Fix \(n\geq1\), \(0<\alpha<1\), and \(\tau>0\). A decreasing list \(q_1\geq\cdots\geq q_n\) is the spectrum of

\[
 Q=A^{-\alpha/2}(A+uu^T)^\alpha A^{-\alpha/2},
 \qquad A\succ0,\quad u^TA^{-1}u=\tau,
\]

if and only if, for some \(1\leq m\leq n\),

\[
 q_1>q_2>\cdots>q_m>1,
 \qquad q_{m+1}=\cdots=q_n=1,
 \qquad \prod_iq_i=(1+\tau)^\alpha.
\]

For \(\tau=0\), the unique list is all ones.

### Necessity: strict total positivity of the active correction

Let \(\theta_1<\cdots<\theta_m\) be those distinct eigenvalues of \(A\) for which the spectral projection of \(u\) is nonzero. The cyclic subspace

\[
 \mathcal K=\operatorname{span}\{u,Au,A^2u,\ldots\}
\]

has dimension \(m\). It and its orthogonal complement reduce \(A\), \(B=A+uu^T\), and every function used in \(Q\). On \(\mathcal K^\perp\), the correction \(C=Q-I\) vanishes. In an orthonormal basis of \(\mathcal K\), we can write

\[
 A=\operatorname{diag}(\theta_1,\ldots,\theta_m),
 \qquad u_i>0.
\]

The rank-one resolvent formula gives

\[
 C_{ij}=d_i d_j\int_0^\infty
 \frac{w(t)}{(\theta_i+t)(\theta_j+t)}\,dt,
 \quad d_i=u_i\theta_i^{-\alpha/2}>0,
\]

where

\[
 w(t)=\frac{\sin(\pi\alpha)}{\pi}
 \frac{t^\alpha}{1+\sum_k u_k^2/(\theta_k+t)}>0.
\]

All these integrals converge. For row and column index sets \(I,J\) of the same size \(k\), the continuous Cauchy--Binet identity expresses their minor, after division by its positive diagonal factors, as

\[
 \int_{0<t_1<\cdots<t_k<\infty}
 \det\left[\frac1{\theta_i+t_\ell}\right]_{i\in I,\ell\leq k}
 \det\left[\frac1{\theta_j+t_\ell}\right]_{j\in J,\ell\leq k}
 \prod_{\ell=1}^k w(t_\ell)\,dt_1\cdots dt_k.
\]

Each Cauchy determinant is strictly positive when its row parameters and its \(t\)'s increase, by the Cauchy determinant formula. The integral is strictly positive. Truncating the domain to a compact interval first justifies the identity without any improper-integral issue, and then monotone convergence applies. Consequently every minor of the active \(C\) is strictly positive.

This also proves positive definiteness: it is a Gram matrix of the linearly independent rational functions \(1/(\theta_i+t)\) in a measure with positive density. Let its positive eigenvalues be \(\lambda_1\geq\cdots\geq\lambda_m>0\). Its \(k\)-th compound matrix has every entry strictly positive, so Perron--Frobenius says its largest eigenvalue is simple. Its eigenvalues are the products of \(k\) eigenvalues of \(C\). If \(\lambda_k=\lambda_{k+1}\), its largest eigenvalue \(\lambda_1\cdots\lambda_k\) would be repeated. Hence

\[
 \lambda_1>\cdots>\lambda_m>0.
\]

Thus every eigenvalue of \(Q\) above one is simple. The determinant constraint is the usual determinant lemma.

### Sufficiency: uniform separated-scale convergence and Brouwer

It is enough to realize the positive part in dimension \(m\); append an arbitrary positive block on which \(u=0\) for trailing ones. Put

\[
 S=\log(1+\tau),\qquad
 x_i^*=\alpha^{-1}\log q_i.
\]

Thus \(x_1^*>\cdots>x_m^*>0\) and \(\sum_i x_i^*=S\). In the affine space

\[
 \mathcal H=\{x\in\mathbb R^m:\sum_i x_i=S\},
\]

choose a closed Euclidean ball \(K\) centered at \(x^*\), of radius \(\rho>0\), contained in \(x_1>\cdots>x_m>0\). For \(x\in K\), set

\[
 r_i=e^{x_i},\quad
 z_i(x)=(e^{x_i}-1)e^{\sum_{j>i}x_j},\quad
 A_\delta=\operatorname{diag}(\delta^{m-i}),\quad
 u_i(x)=\sqrt{(A_\delta)_{ii}z_i(x)}.
\]

The leverage is \(\sum_i z_i(x)=e^S-1=\tau\) for every \(x\in K\). Let \(Q_\delta(x)\) be its relative power matrix and define the decreasing logarithmic spectrum

\[
 F_\delta(x)=\alpha^{-1}
 \bigl(\log\lambda_1(Q_\delta(x)),\ldots,
       \log\lambda_m(Q_\delta(x))\bigr).
\]

This is a continuous function of \(x\), and the determinant identity places its values in \(\mathcal H\).

The manuscript's separated-scale convergence is **uniform for \(x\in K\)**. Indeed, all \(z_i(x)\) stay in a fixed compact interval. In the diagonal integral, the convergence of its denominator for each fixed integration variable \(s>0\) is uniform in \(x\), and the bound \(s^\alpha/(1+s)^2\) still dominates the entire family. Apply dominated convergence to the supremum of the absolute integrand error. The off-diagonal estimate is uniform because the prefactors \(\sqrt{z_i(x)z_j(x)}\) are bounded. Hence

\[
 \sup_{x\in K}\|Q_\delta(x)-
       \operatorname{diag}(e^{\alpha x_1},\ldots,e^{\alpha x_m})\|
 \longrightarrow0.
\]

Ordered eigenvalue continuity and the fact that every eigenvalue is at least one give

\[
 \sup_{x\in K}\|F_\delta(x)-x\|_2\longrightarrow0.
\]

For sufficiently small positive \(\delta\), this supremum is less than \(\rho\). Therefore

\[
 T_\delta(x)=x^*+x-F_\delta(x)
\]

is a continuous map from the closed ball \(K\) into itself. Brouwer's fixed-point theorem gives \(x=T_\delta(x)\), equivalently \(F_\delta(x)=x^*\). This is an exact realization at finite positive \(\delta\). For \(m=1\), the affine space is a point and the scalar identity supplies the same conclusion directly.

## Consequences

1. The closure is essential for every target with a repeated entry strictly above one. In particular, a scalar target \(Q=cI\), \(c>1\), cannot be realized in dimension greater than one. This special obstruction also follows directly from \(B^\alpha=cA^\alpha\), which implies \(B=c^{1/\alpha}A\) and contradicts a rank-one update.
2. Every admissible simple spectrum is realized exactly, not merely approximated. The proof is existential and does not provide a useful condition-number bound or a numerical inverse algorithm.
3. A target with entries equal to one but with pairwise distinct entries above one is attained exactly by restricting to its active dimension and padding. Thus the presence of ones alone is not an obstruction to exact attainability.
4. The exact worst-case threshold count can be realized by choosing distinct positive target entries inside the same strict threshold margin. Its proof does not require a collision target.

The total-positivity and topological tools here are classical. This note makes no historical-priority claim for their application to relative fractional spectra.
