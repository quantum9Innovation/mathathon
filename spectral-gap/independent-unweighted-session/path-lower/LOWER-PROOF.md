# A sharp root-exponential lower law for centered unit paths

Fix `0 < alpha < 1`. All logarithms are natural. Let `C_N` be the
energy-relative fractional correction for the unit path on `2N` vertices
when its central edge is doubled. Let `N(epsilon; T)` denote the number
of eigenvalues of a positive compact operator `T` strictly exceeding
`epsilon`.

**Proved conclusion.** There is a positive compact operator `C_infinity`
such that, after canonical isometric embeddings of the cyclic supports,
`C_N -> C_infinity` in Hilbert--Schmidt norm, and

\[
 N(\varepsilon;C_\infty)
   \sim \frac{1}{2\pi^2}\log^2(1/\varepsilon).
 \tag{1}
\]

Consequently

\[
 \liminf_{\varepsilon\downarrow0}
 \frac{\sup_N N(\varepsilon;C_N)}{\log^2(1/\varepsilon)}
 \ge \frac1{2\pi^2}.
 \tag{2}
\]

In particular a uniform path upper bound `O_alpha(log^2(1/epsilon))`
has the correct order. This note does **not** identify the sharp leading
coefficient for the supremum over all finite path lengths and edge
locations: (1) concerns the centered-path limit, and (2) is a lower
bound for that supremum.

## 1. A relative derivative that sandwiches the exact update

For a positive definite `A` on the common support and update `uu^*`, set

\[
 m(t)=u^*(A+t)^{-1}u,\qquad
 H_\alpha=c_\alpha\int_0^\infty
 t^\alpha A^{-\alpha/2}(A+t)^{-1}uu^*(A+t)^{-1}A^{-\alpha/2}\,dt,
 \quad c_\alpha=\sin(\pi\alpha)/\pi.
\]

This is the relative Fréchet derivative of the power at `A` in the
direction `uu^*`. The rank-one fractional resolvent identity gives

\[
 C_\alpha=c_\alpha\int_0^\infty
 \frac{t^\alpha A^{-\alpha/2}(A+t)^{-1}uu^*(A+t)^{-1}A^{-\alpha/2}}
      {1+m(t)}\,dt.
\]

For a doubled unit bridge, `m(0)=u^* A^{-1}u=1`. Therefore

\[
 \tfrac12 H_\alpha\preceq C_\alpha\preceq H_\alpha.
 \tag{3}
\]

This is a Loewner inequality, not an entrywise estimate. The same
inequality holds in the limiting integral-operator model below.

Let the spectral coordinates of `u` be `u_j`, and put
`z_j=|u_j|^2/lambda_j`. Then the entries of `H_alpha`, after harmless
diagonal sign conjugation, are

\[
 (H_\alpha)_{ij}
 =\sqrt{z_i z_j}\,K_\alpha(\log\lambda_i-\log\lambda_j),\qquad
 K_\alpha(s)=\frac{\sinh(\alpha s/2)}{\sinh(s/2)},\quad K_\alpha(0)=\alpha.
 \tag{4}
\]

Indeed the scalar resolvent integral is the divided difference of
`lambda^alpha`, and multiplication by
`(lambda_i lambda_j)^((1-alpha)/2)` yields precisely `K_alpha`.

## 2. The centered-path spectral measure and its limit

For the unit path on `n` vertices, the positive eigenvalues are

\[
 \lambda_k=4\sin^2(k\pi/(2n)),\qquad 1\le k<n.
\]

For the edge between vertices `p` and `p+1`, direct subtraction of the
cosine eigenvectors gives

\[
 z_k=\frac{2}{n}\sin^2(k\pi p/n).
 \tag{5}
\]

At `n=2N,p=N`, only odd `k=2j-1` contribute, with `z_k=1/N`. Thus
the leverage spectral measure converges to

\[
 d\nu(\lambda)
 =\frac{d\lambda}{\pi\sqrt{\lambda(4-\lambda)}},\qquad 0<\lambda<4.
 \tag{6}
\]

Equivalently it is uniform `dtheta/pi` on `0<theta<pi` under
`lambda(theta)=4 sin^2(theta/2)`. The limiting derivative is the
positive integral operator on `L^2(nu)` with kernel
`K_alpha(log(lambda)-log(eta))`; call it `H_infinity`.

Its trace is `alpha nu((0,4))=alpha`, and compactness follows directly
from the bounded kernel. To avoid invoking any kernel trace theorem,
one can instead obtain trace class from its positive resolvent Gram
factorization and Tonelli, which gives the same diagonal integral.

For an explicit common-space embedding, partition `(0,pi)` into `N`
equal cells, and identify a discrete vector with its normalized
piecewise constant function. The embedded derivative has the step
kernel obtained by evaluating at the cell midpoints
`theta_j=(2j-1)pi/(2N)`. For almost every pair `(theta,phi)` these
kernels converge to the limiting kernel. Since `|K_alpha|<=alpha`,
dominated convergence proves Hilbert--Schmidt convergence.

The exact relative corrections have the same property. In `L^2(nu_N)`
their kernels are

\[
 F_N(\lambda,\eta)=c_\alpha(\lambda\eta)^{(1-\alpha)/2}
 \int_0^\infty\frac{t^\alpha\,dt}
 { (\lambda+t)(\eta+t)(1+m_N(t))},
\]

where

\[
 m_N(t)=\int\frac{\lambda}{\lambda+t}\,d\nu_N(\lambda).
\]

For each `t>0`, midpoint quadrature gives

\[
 m_N(t)\longrightarrow
 m_\infty(t)=1-\sqrt{t/(t+4)}.
 \tag{7}
\]

For fixed positive `lambda,eta`, dominated convergence in the scalar
integral gives kernel convergence. The uniform bound
`0<=F_N(lambda,eta)<=K_alpha(log(lambda/eta))<=alpha` then gives
Hilbert--Schmidt convergence of the step kernels. This constructs
`C_infinity` without applying an unbounded inverse power to an
infinite-graph operator. It also proves (3) for the limit.

## 3. All fractional exponents have the same leading count constant

With Fourier convention `hat f(xi)=integral f(s) exp(-i xi s) ds`,

\[
 \widehat K_\alpha(\xi)
 =\frac{2\pi\sin(\pi\alpha)}
        {\cosh(2\pi\xi)+\cos(\pi\alpha)}.
 \tag{8}
\]

This follows from the elementary beta integral; the formula is also
listed in NIST DLMF, Table 1.14.1, after rescaling its
`sinh(at)/sinh(pi t)` entry. In particular the symbol is positive.
For each fixed `alpha`, its ratio to the symbol at `alpha=1/2` is
bounded above and below by positive constants independent of `xi`.
Consequently, as positive convolution operators on `L^2(R)`,

\[
 c_\alpha K_{1/2}\preceq K_\alpha\preceq C_\alpha K_{1/2}.
 \tag{9}
\]

Compression and multiplication by a real weight preserve (9).

Pass to logarithmic coordinates `x=log(lambda)`. The unitary
transformation from `L^2(nu)` to Lebesgue `L^2` has squared multiplier

\[
 r(x)=\frac{e^{x/2}}{\pi\sqrt{4-e^x}},\qquad x<\log4.
\]

Thus the derivative kernel becomes

\[
 \sqrt{r(x)r(y)} K_\alpha(x-y).
 \tag{10}
\]

On `x<=0`, write `r(x)=e^{x/2} v(x)^2`, with `v` bounded above and
below by positive constants. Equations (9) and (10) show that the
eigenvalues of this low-energy compression are bounded above and
below by fixed constant multiples of those of the model

\[
 S(x,y)=e^{(x+y)/4}K_{1/2}(x-y),\qquad x,y<0.
 \tag{11}
\]

For clarity, the weight comparison is an eigenvalue comparison, not a
pointwise-kernel-to-Loewner inference: if `M_v` is bounded and boundedly
invertible and `S>=0`, then
`inf(v)^2 lambda_j(S)<=lambda_j(M_v S M_v)<=sup(v)^2 lambda_j(S)`
by the min--max principle, or by the singular values of `S^(1/2)M_v`.

At `alpha=1/2`, `K_(1/2)(s)=1/[2 cosh(s/4)]`. Under
`u=exp(x/2)`, the unitary map from `L^2((-infinity,0),dx)` to
`L^2((0,1),du)` turns (11) into the kernel

\[
 2\frac{\sqrt{uv}}{u+v}.
 \tag{12}
\]

Laptev's primary theorem gives, for the operator with kernel
`u^beta v^gamma/(u+v)^a` on `L^2(0,1)`,

\[
 N(\varepsilon;T)
 \sim \frac{\log^2(1/\varepsilon)}{2\pi^2\rho},\qquad
 a>0,\quad\beta,\gamma>-\tfrac12,\quad
 \rho=\beta+\gamma-a+1>0.
 \tag{13}
\]

Apply (13) with `a=1,beta=gamma=1/2,rho=1`. The prefactor 2 in
(12) only shifts the logarithm by a constant. Fixed multiplicative
comparisons of eigenvalues preserve the leading coefficient, so the
low-energy compression of `H_infinity` has count constant `1/(2pi^2)`.

The remaining high-energy compression, `1<=lambda<=4`, has
`N(epsilon)=O_alpha(log(1/epsilon))`. To see this without a separate
spectral theorem, its kernel
`K_alpha(log(lambda)-log(eta))` is analytic in `lambda` on one fixed
complex neighborhood of `[1,4]`, uniformly for real `eta in [1,4]`.
Polynomial approximation in that first variable gives a rank-`q`
kernel with uniform error `O(exp(-c q))`. Since the measure has finite
mass, this is also an operator-norm error of that order.

For a positive block operator, `H<=2 diag(PHP,QHQ)`, while
`lambda_j(PHP)<=lambda_j(H)`. Hence the low-energy constant and
the negligible high-energy count imply

\[
 N(\varepsilon;H_\infty)
 \sim\frac{1}{2\pi^2}\log^2(1/\varepsilon).
\]

The factor-two Loewner comparison (3) proves (1).

## 4. Transfer to finite unit paths, including strict counts

Hilbert--Schmidt convergence implies norm convergence and hence
convergence of each ordered eigenvalue. For any fixed positive
`epsilon`, every eigenvalue of `C_infinity` strictly exceeding
`epsilon` is eventually exceeded by the corresponding eigenvalue of
`C_N`. Since the limit count is finite,

\[
 \sup_N N(\varepsilon;C_N)\ge N(\varepsilon;C_\infty).
\]

Combining this with (1) gives (2), including the strict threshold
convention. The host graphs and both endpoint vertex masses are
ordinary unweighted paths with unit vertex masses; precisely one
existing edge changes its conductance from 1 to 2.

## Primary-source comparison and scope

The sharp asymptotic input is A. A. Laptev, *Spectral asymptotic behavior
of a class of integral operators*, Mathematical Notes 16 (1974),
1038--1043 (English translation), Theorem (3), p. 1039. Author-hosted
full text: <https://www.ma.ic.ac.uk/~alaptev/Papers/MatZam74.pdf>.
DOI: <https://doi.org/10.1007/BF01149794>. The journal's bilingual
MathNet record independently states the same theorem and coefficient:
<https://www.mathnet.ru/php/archive.phtml?jrnid=mzm&option_lang=eng&paperid=7513&wshow=paper>.
The title, theorem, admissibility conditions and constant were checked
in the primary PDF. It specifically treats the weighted Cauchy kernel
needed here, and for `a=1,beta=gamma` points back to Widom's earlier
Hankel-matrix theorem. Thus root-exponential weighted-Cauchy spectral
decay is classical. The contribution here is the exact path spectral
measure, relative derivative sandwich, alpha-independent Fourier
comparison, and finite-path transfer.

For (8), NIST DLMF Table 1.14.1:
<https://dlmf.nist.gov/1.14#T1>. No novelty claim is made for the
transform or for the fractional resolvent identity.

No numerical experiment is used to prove any assertion in this note.
Historical priority of this precise graph-relative specialization has
not been certified.

## Additional consequence: an edge at fixed distance from an endpoint

For comparison, fix an integer `p>=1`, double the edge `(p,p+1)`, and
let the far endpoint of the unit path tend to infinity. Formula (5)
gives the limiting leverage measure

\[
 d\nu_p(\theta)=\frac2\pi\sin^2(p\theta)\,d\theta,
 \quad 0<\theta<\pi,\qquad \lambda=4\sin^2(\theta/2).
\]

Its logarithmic density obeys

\[
 r_p(x)\sim (p^2/\pi)e^{3x/2}\quad(x\to-\infty).
\]

The same derivative sandwich and Fourier comparison apply. Choose a
fixed low-energy cutoff below the first positive zero of
`sin(p theta)`. On this low part, after a translation in `x`, the
derivative eigenvalues are comparable to those of

\[
 e^{3(x+y)/4} K_{1/2}(x-y),\qquad x,y<0.
\]

The substitution `u=exp(x/2)` changes this kernel to
`2 u^(3/2) v^(3/2)/(u+v)`. Laptev's parameters are now
`a=1,beta=gamma=3/2,rho=3`, so the limiting exact relative correction
for this fixed-`p` sequence has

\[
 N(\varepsilon;C_{\infty,p})
 \sim\frac1{6\pi^2}\log^2(1/\varepsilon).
\]

The high-energy part again has only `O(log(1/epsilon))` count. Zeros of
the measure in that high-energy part cause no difficulty, since its
kernel is analytic and its measure is finite. Midpoint/Riemann step
kernel convergence is proved as in Section 2, now incorporating the
bounded factor `sqrt(2) sin(p theta)` into the common `L^2(dtheta/pi)`
embedding. This gives a second explicit order-sharp unit-path family,
including the endpoint-adjacent edge `p=1`.
