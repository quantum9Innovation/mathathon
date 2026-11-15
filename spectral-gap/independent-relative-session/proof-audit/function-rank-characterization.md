# Exact rank and simplicity for complete Bernstein updates

This is a derived functional extension of the total-positivity argument. Its relation to classical finite-rank Loewner kernels should be credited; no novelty is claimed here.

Let \(f:(0,\infty)\to(0,\infty)\) have a complete Bernstein representation

\[
 f(x)=a+bx+\int_{(0,\infty)}\frac{x}{x+t}\,\mu(dt),
 \qquad a,b\geq0,\quad \mu\geq0,
\]

with the usual convergence condition on the positive measure. Let \(B=A+uu^T\), \(A\succ0\), \(u\ne0\), and let \(m\) be the dimension of the cyclic subspace of \((A,u)\). Define

\[
 N=\#\operatorname{supp}(\mu)+\mathbf1_{b>0},
\]

where the support count is the number of distinct positive support points and is infinity when the support is infinite. Then

\[
 \operatorname{rank}(f(B)-f(A))=\min(m,N).
\]

The same rank holds after congruence by \(f(A)^{-1/2}\). Moreover, all its positive eigenvalues after this congruence are pairwise distinct.

## Proof

On the active cyclic subspace, put \(A=\operatorname{diag}(\theta_1<\cdots<\theta_m)\) and choose the signs so \(u_i>0\). The resolvent identity gives

\[
 (f(B)-f(A))_{ij}=u_i u_j\left[
 b+\int_{(0,\infty)}
 \frac{t\,\mu(dt)}{
 (\theta_i+t)(\theta_j+t)
 (1+\sum_\ell u_\ell^2/(\theta_\ell+t))}
 \right].
\]

This is a Gram matrix of the Cauchy columns \((1/(\theta_i+t))_i\), with a positive column scaling at each support point. If \(b>0\), include the additional constant column \((1)_i\). This column is the positive rescaled limit of a Cauchy column as \(t\to\infty\).

Every square Cauchy minor with distinct increasing row and support parameters is strictly positive; the same holds when the final support parameter is infinity and its column is rescaled to one. By continuous/discrete Cauchy--Binet, every minor of order \(k\leq\min(m,N)\) of the Gram matrix is strictly positive. If \(N\) is finite, its rank is at most \(N\) from the displayed column representation; the strictly positive maximal minors give the matching lower bound. Infinite support gives strict positivity of its full determinant. Congruence by the positive diagonal matrix \(f(A)^{-1/2}\) on the cyclic subspace preserves these signs.

Let the nonzero positive eigenvalues be \(\lambda_1\geq\cdots\geq\lambda_r>0\), where \(r=\min(m,N)\). For \(1\leq k<r\), every entry of the \(k\)-th compound is strictly positive. Perron--Frobenius and the compound eigenvalue-product formula imply \(\lambda_k>\lambda_{k+1}\). The correction vanishes on the orthogonal complement of the cyclic subspace, proving the claims.

## Function characterization and graph consequence

A finite-support representing measure gives a dimension-independent exact rank bound for every rank-one update, equal to its number of support points plus the presence of an affine term. Infinite support gives unbounded rank: choose arbitrarily large diagonal \(A\) with distinct diagonal entries and every coordinate of \(u\) nonzero. Thus finite support is necessary and sufficient for a uniform exact rank bound within this function class. Under the standard uniqueness of the complete Bernstein/Stieltjes representation, this is equivalently rationality of \(f\), including affine functions.

For \(f(x)=x^\alpha\), \(0<\alpha<1\), its measure has positive density on all positive \(t\), so the rank equals \(m\) and the positive relative eigenvalues are simple. For a connected graph and a single positive edge-conductance change, this says precisely that the relative fractional correction rank equals the number of distinct positive Laplacian eigenvalues whose spectral projectors do not annihilate the edited edge incidence vector. The result applies after restriction to the common constant-orthogonal support. It places no computational efficiency bound on finding those eigenvalues.

For an endpoint-edge edit on any \(N\)-vertex weighted path, the active dimension is exactly \(N-1\). Indeed, positive path conductances make its Laplacian irreducible symmetric tridiagonal and hence give simple eigenvalues. If a positive-eigenvalue eigenvector satisfies \(v_1-v_2=0\), the endpoint equation \(w_1(v_1-v_2)=\lambda v_1\) gives \(v_1=v_2=0\), and recurrence along the path gives \(v=0\), a contradiction. Consequently **every nonrational complete Bernstein response has rank \(N-1\) and pairwise distinct positive relative correction eigenvalues after every positive endpoint-edge edit**, regardless of the edit size. Rational complete Bernstein responses have instead the exact rank \(\min(N-1,N_f)\), where \(N_f\) is their positive-support count plus the affine term indicator.
