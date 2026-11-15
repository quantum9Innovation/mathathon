# A tail bound independent of the number of permutation generators

Status: a complete derivation conditional only on the published first-order support theorem stated below. This is a refinement of an existing method, with a graph consequence obtained by tracking a parameter differently. Historical novelty has not been established. No exact mixed-extremum input is needed.

## Statement

Let r, D be arbitrary finite positive integers. Let S_1,...,S_r be independent uniform permutation matrices of size N, restricted to the orthogonal complement of the constant vector. Take a self-adjoint linear noncommutative polynomial

\[
 P(z)=A_0\otimes I+\sum_{i=1}^r(A_i\otimes z_i+A_i^*\otimes z_i^*),
 \qquad A_0=A_0^*\in M_D(\mathbb C).
\]

Write X_N=P(S), X_F=P(u), where u_i are the left regular generators of the free group, and set

\[
 K=\sup_{U_1,\ldots,U_r}\|P(U)\|,
 \qquad \rho=\|X_F\|.
\]

The supremum includes unitary tuples on all Hilbert spaces, so K is the full free-group C*-norm. There is an absolute constant C, independent of r, D, N, and the coefficients, such that

\[
 \Pr\{\|X_N\|\geq\rho+\varepsilon\}
 \leq C\frac DN\left(\frac K\varepsilon\right)^9
 \tag{T}
\]

for every 0<epsilon<K-rho. The boundary epsilon=K-rho follows by a limit from below. For a threshold strictly above K the probability is zero. If K=0 the assertion is trivial. One may add an unused generator if r=1.

The exponent 9 is deliberately unoptimized. The substantive feature is the absence of r from the bound.

## Published inputs and source fidelity

The inputs are the rational trace formula in Lemma 5.1 and the exact support inclusion in Corollary 9.7 of Chen, Garza-Vargas, Tropp and van Handel, *A new approach to strong convergence*, Annals of Mathematics 203 (2026), pages 555-602. Use [arXiv v3](https://arxiv.org/html/2405.16026v3) for accessible full text. Its Theorem 3.9 has a factor (log r)^8. The proof below replaces that factor with a mild increase in the epsilon exponent.

The first-order support inclusion says that the Taylor coefficients nu_0 and nu_1 of the normalized expected trace, regarded as distributions in the test function, are supported in [-rho,rho]. It is an exact assertion for every finite r and D. Its proof has dimension-dependent intermediate constants, but those constants disappear from the exact support inclusion and do not enter (T).

The locally saved source is `CGVTvH-I-v3-source/strongcv.tex`. Relevant source locations are lines 1865-1930 for rationality, lines 2001-2180 for the original interpolation calculation, lines 2940-2950 for first-order support, and lines 1752-1820 for a smooth cutoff. These are source-file line numbers, not journal page numbers.

## 1. A universal denominator

For integer q>=1 define

\[
 b_j=\left\lfloor\frac q{j+1}\right\rfloor,
 \qquad
 g_q(x)=\prod_{j=1}^{q-1}(1-jx)^{b_j},
 \qquad B_q=q(1+\log q).
\]

For any word w of length at most q, the rational trace formula can use this same denominator, regardless of r. To see this directly from the connected-pattern formula in Lemma 5.1, let e_c be the number of distinct edges of color c in one pattern. Then sum_c e_c<=q. The exponent of (1-jx) in the pattern denominator is the number of colors with e_c>=j+1, which is at most b_j. Thus the pattern denominator divides g_q.

Put G_q=deg(g_q). The elementary harmonic estimate gives

\[
 G_q=\sum_{j=1}^{q-1}b_j\leq q\log q.
\]

After multiplying a pattern term by g_q, its numerator degree is G_q plus the number of colors actually used by that pattern. This number is at most q. The subtraction of the invariant vector contributes -x g_q(x), whose degree is also at most B_q. Therefore all numerator degrees are at most B_q. The constant word has normalized trace 1-x and obeys the same conclusion.

Consequently, for every scalar polynomial h of degree at most q,

\[
 \mathbf E\left[\frac1{DN}\operatorname{Tr}h(X_N)\right]
   =\Psi_h(1/N)=\frac{f_h(1/N)}{g_q(1/N)},
 \qquad N\geq q,
 \tag{1}
\]

where deg f_h,deg g_q<=B_q. Linearity in h defines

\[
 \nu_0(h)=\Psi_h(0),\qquad \nu_1(h)=\Psi_h'(0).
\]

Different choices of q give the same rational function, because they agree at infinitely many reciprocal integers. Hence the coefficient functionals are consistent across q.

## 2. A polynomial remainder with no r dependence

Let H=||h||_infinity on [-K,K], B=B_q, p=ceil(B), and M=ceil(32B^2). The normalization in (1) uses DN, although the actual dimension is D(N-1). Thus

\[
 |\Psi_h(1/L)|\leq H\quad(L\geq q).
\]

For 0<=x<=1/M, all jx<=1/2 and

\[
 -\log g_q(x)\leq 2x\sum_j j b_j
 \leq 2qB/M\leq 1,
\]

so e^{-1}<=g_q(x)<=1. In particular |f_h(1/L)|<=H for integer L>=M.

The mesh of reciprocal integers {1/L:L>=M}, including its limit 0, has maximum gap at most 1/M^2. By the classical Markov inequality,

\[
 \|f_h'\|_{[0,1/M]}\leq2p^2M\|f_h\|_{[0,1/M]}.
\]

Every point in [0,1/M] is within 1/M^2 of this mesh. Since M>=8p^2, comparison at the nearest mesh point gives ||f_h||<=2H. Markov's inequality again yields

\[
 \|f_h'\|\leq CB^4H,
 \qquad \|f_h''\|\leq CB^8H.
\]

On the same interval, writing ell=log(g_q) gives

\[
 |\ell'|\leq2qB\leq2B^2,
 \qquad |\ell''|\leq4q^2B\leq4B^3.
\]

The product rule for f_h/g_q now gives

\[
 \|\Psi_h'\|\leq CB^4H,
 \qquad \|\Psi_h''\|\leq CB^8H.
 \tag{2}
\]

For N>=M, Taylor's theorem and (2) imply

\[
 \left|\mathbf E\frac{\operatorname{Tr}h(X_N)}{DN}
       -\nu_0(h)-\frac{\nu_1(h)}N\right|
 \leq\frac{CB_q^8}{N^2}H.
 \tag{3}
\]

This also holds for N<M. Indeed, |nu_0(h)|<=H by taking N to infinity, and |nu_1(h)|<=CB^4H by (2). The left side is therefore at most 2H+CB^4H/N. Multiplication by N^2 and N<M<=33B^2 bounds this by CB^8H. No formula at reciprocal integers below q is needed.

## 3. Absorb the logarithmic degree factor in smoothness

For a smooth h write

\[
 f(\theta)=h(K\cos\theta)
     =a_0+\sum_{j\geq1}a_j\cos(j\theta).
\]

Applying (3) term by term to T_j(x/K) bounds the expected trace remainder by

\[
 \frac C{N^2}\sum_{j\geq1}j^8(1+\log j)^8|a_j|.
\]

The constant term has zero remainder because

\[
 \nu_0(1)=1,\qquad \nu_1(1)=-1,
 \qquad \frac{\operatorname{Tr}I}{DN}=1-\frac1N.
\]

This normalization detail matters. One should not set nu_1(1)=0.

Cauchy-Schwarz and Parseval give

\[
 \begin{split}
 \sum_{j\geq1}j^8(1+\log j)^8|a_j|
 &\leq
 \left(\sum_{j\geq1}\frac{(1+\log j)^{16}}{j^2}\right)^{1/2}
 \left(\sum_{j\geq1}j^{18}|a_j|^2\right)^{1/2}\\
 &\leq C\|f^{(9)}\|_{L^2[0,2\pi]}.
 \end{split}
\]

The numerical series is finite and absolute. The coefficients of a smooth h decrease faster than any power, so the termwise extension is justified. The resulting nu_0,nu_1 coincide with the published distributions by their polynomial values. We have proved

\[
 \left|\mathbf E\frac{\operatorname{Tr}h(X_N)}{DN}
       -\nu_0(h)-\frac{\nu_1(h)}N\right|
 \leq\frac C{N^2}\|[h(K\cos\theta)]^{(9)}\|_2.
 \tag{4}
\]

## 4. Spectral cutoff

Choose a fixed smooth nondecreasing function eta equal to zero on (-infinity,0] and to one on [1,infinity). Apply it on each of the intervals [rho+epsilon/2,rho+epsilon] and [-rho-epsilon,-rho-epsilon/2] to obtain a smooth chi with 0<=chi<=1, vanishing on a neighborhood of [-rho,rho], and equal to one when |x|>=rho+epsilon.

The transition width is epsilon/2. The chain rule for chi(K cos(theta)) gives

\[
 \|[\chi(K\cos\theta)]^{(9)}\|_2
 \leq C(K/\varepsilon)^9.
\]

All lower derivative terms are absorbed because epsilon<K. Since nu_0 and nu_1 have support in [-rho,rho], they annihilate chi. Equation (4) therefore gives

\[
 \mathbf E\operatorname{Tr}\chi(X_N)
 \leq C\frac DN(K/\varepsilon)^9.
\]

An eigenvalue outside [-rho-epsilon,rho+epsilon] contributes at least one to this nonnegative trace. Markov's inequality proves (T).

## Graph consequence and exact scope

Let G be any finite connected loopless multigraph with m vertices and maximum degree at most Delta. Give every undirected edge its own independent uniform permutation in an N-lift. Its adjacency matrix on the new subspace is a polynomial P as above with D=m. The full norm K equals ||A_G|| and is at most Delta. The upper bound follows from applying the scalar adjacency form to the vector of block norms. Setting every unitary equal to the identity gives the reverse bound.

The free operator P(u) is adjacency on a disjoint union of copies of the universal covering tree of G. To verify this, a reduced closed walk would give a nonempty reduced word in the distinct oriented edge labels and cannot act trivially in the free group. Each component covers G and is therefore its universal cover. Thus rho=||A_{T_G}||.

Consequently,

\[
 \Pr\{\|A_{G_N}|_{\rm new}\|\geq\rho(T_G)+\varepsilon\}
 \leq C\frac mN(\Delta/\varepsilon)^9.
 \tag{G}
\]

For every deterministic sequence of bounded-degree base graphs with m_N=o(N), (G) gives an upper spectral bound rho(T_{G_N})+o_P(1). For d-regular bases the benchmark is 2sqrt(d-1). Choosing epsilon_N=(m_N/N)^{1/10} makes the failure probability at most C Delta^9(m_N/N)^{1/10}. This choice is only an example.

The quantifier is uniform over deterministic bases. It does not assert that a single random collection of permutations works simultaneously for all coefficients or for a base selected after seeing the permutations. It does not assert a new lower Alon-Boppana theorem, a theorem for simple random regular graphs, or a result for arbitrary factor matrix multiplication.

## Remaining obligations

The displayed derivation has no unresolved internal step, but it needs an independent reconstruction of the universal-denominator degree calculation and the smooth remainder. Historical priority for this parameter refinement is unverified. The result is close to the published method and should be described as a generator-independent corollary or refinement, without claiming a new spectral technique. The separate connected-base obstruction must be checked in its own proof. No finite computation is a premise of (T) or (G).
