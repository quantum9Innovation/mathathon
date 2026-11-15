# Noncoincidence and integer tuning of the retuned scalar law

November 15, 2026. Owner: probability workstream. Revision 1, frozen for separate review.

## 1. Inputs and scope

Use the conditional scalar law from collective-self-energy-v1.md, SHA256 a3c6b1b42bed9f7f3c7c5d45c1292df5a207951e709e318db24f6f711c9d9d4d. Put kappa=3/sqrt(8), theta=c^(3/2)>0,

\[
 \lambda_k=\frac{3\theta}{4\sqrt2}2^k,\qquad
 w_k=\kappa 2^{-k},\qquad
 J(w)=\frac{\kappa w}{\kappa+w}.
\]

The P_k are independent Poisson variables with these means, conditioned on P_0=1. The scalar is

\[
 L=\frac{51}{32}
 +\frac1\theta\left[
  \sum_{k\le0}J(w_k)P_k+
  \sum_{k\ge1}\bigl(J(w_k)P_k-w_k\lambda_k\bigr)
 \right].
\tag{1}
\]

This file proves that L has a bounded smooth density and no atoms, and that every finite next detuning beta can be realized by admissible integer graph sizes. These are supporting claims for the separate actual graph root and eigenvector synthesis.

Exposure: the same workstream authored the preceding probability proofs. After the self-energy formula was frozen, the integrator suggested the same one-scale Fourier bound used below. The complete argument and integer construction are recorded here. No live root or structural proof was read.

## 2. A useful representation

Define

\[
 a_k=\frac{J(w_k)}{\theta}
     =\frac{\kappa}{\theta(2^k+1)}.
\tag{2}
\]

Since P_0 is fixed at one, (1) can be written

\[
 L=d_*+\sum_{k\le-1}a_kP_k
          +\sum_{k\ge1}a_k(P_k-\lambda_k),
\tag{3}
\]

where the finite constant is

\[
 d_*=\frac{51}{32}+\frac{\kappa}{2\theta}
       -\frac1\theta\sum_{k\ge1}
          \lambda_k\frac{w_k^2}{\kappa+w_k}.
\tag{4}
\]

The last series converges. The positive-offset centered series in (3) converges in L2, since sum_(k>=1)lambda_k a_k squared is finite. The negative-offset series is a finite-intensity compound Poisson sum with bounded jump sizes, so it has finite moments of all orders. In particular the characteristic function of L is well defined.

## 3. Exponential Fourier decay

Let psi(t)=E exp(itL). Independence and the finite-truncation limit give

\[
 |\psi(t)|
 =\exp\left[
  -\sum_{k\ne0}\lambda_k(1-\cos(t a_k))
 \right].
\tag{5}
\]

The series in this formula converges for each real t. For k<=-1, the sum of intensities is finite. For k>=1, use
1-cos(x)<=x squared/2 and the summable variance series.

Suppose |t|kappa/theta>=2 and choose

\[
 k=\left\lfloor\log_2(|t|\kappa/\theta)\right\rfloor\ge1.
\]

Then

\[
 \frac12\le |t|a_k
 =\frac{|t|\kappa/\theta}{2^k+1}<2.
\]

The interval [1/2,2] lies strictly inside (0,pi). Therefore

\[
 1-\cos(t a_k)\ge \eta_0:=1-\cos(1/2)>0.
\]

Also

\[
 \lambda_k
 \ge \frac{3\theta}{4\sqrt2}
       \frac{|t|\kappa}{2\theta}
 =\frac9{32}|t|.
\]

Keeping only this single nonnegative summand in (5) proves

\[
 |\psi(t)|\le
 \exp\left(-\frac9{32}\eta_0 |t|\right)
 \quad\text{for }|t|\ge2\theta/\kappa.
\tag{6}
\]

In particular psi and every polynomial multiple of psi are integrable. Fourier inversion gives a bounded continuous density

\[
 f_L(x)=\frac1{2\pi}\int_{\mathbb R}e^{-itx}\psi(t)\,dt.
\tag{7}
\]

Differentiation under this absolutely convergent integral proves that the density is smooth. Hence

\[
 \mathbb P(L=d)=0
 \quad\text{for every deterministic real }d.
\tag{8}
\]

Fixing P_0 did not weaken the estimate, since the selected k in the argument is positive. The same proof works after fixing any specified finite collection of P_k values, by taking |t| sufficiently large that the chosen k lies beyond that collection.

Thus, for every finite beta, L differs almost surely from the deterministic pair coefficient 33/16-beta. This is a probability statement for the derived scalar law. The actual graph eigenvector transfer remains a separate use of the exact pencil.

## 4. Both possible orderings have positive probability

The law is unbounded in both directions. This is useful when interpreting the random eigenvalue ordering.

For the negative direction, note that

\[
 \lambda_k a_k
 =\frac{3\kappa}{4\sqrt2}\frac{2^k}{2^k+1}
 \longrightarrow\frac9{16}>0.
\tag{9}
\]

Consequently the sum of lambda_k a_k over 1<=k<=N tends to infinity. The event P_1=...=P_N=0 has strictly positive probability for every finite N. The negative-offset compound Poisson sum is zero with strictly positive probability, independently. The remaining centered tail has variance tending to zero as N tends to infinity, so it has positive probability of lying between -1 and 1 for every sufficiently large N. Combining these independent events shows that L has positive probability of being below any prescribed real bound.

For the positive direction, isolate P_1 in (3). Its coefficient a_1 is positive and its Poisson law has unbounded support. The independent remainder is finite almost surely, and therefore has positive probability of exceeding some finite lower bound. Taking P_1 sufficiently large shows that L has positive probability of exceeding any prescribed real bound.

Hence, for every real d,

\[
 0<\mathbb P(L<d)<1,\qquad
 0<\mathbb P(L>d)<1.
\tag{10}
\]

Together with (8), this gives a nontrivial random choice of ordering against each fixed pair coefficient. It does not produce a nonzero signed mixing matrix entry.

## 5. Integer realization of every finite beta

Fix c>0 and a real beta. For integers j tending to infinity choose m_j to be a nearest integer to

\[
 \sqrt2\,c^{3/2}2^j.
\]

Put

\[
 s_0=\frac1{\sqrt2\,2^j},\qquad
 q_j=1-\frac{\kappa}{2}j s_0+\frac{\beta}{\kappa}s_0,
\tag{11}
\]

and let n_j be a nearest even integer to

\[
 2m_j4^j q_j^2.
\tag{12}
\]

The factor q_j tends to one and is positive for all sufficiently large j. The rounding error in n_j is bounded. Write s_j=sqrt(m_j/n_j), r_j=floor(log_2(1/s_j)), and w_j=(3/4)2^(-r_j)/s_j.

Since n_j has order 2^(3j), the relative rounding error is O(1/n_j). Thus

\[
 s_j=s_0/q_j\,(1+O(1/n_j)).
\tag{13}
\]

It follows that

\[
 \log_2(1/s_j)=j+\tfrac12+\log_2 q_j+O(1/n_j).
\]

The extra terms tend to zero, so r_j=j for all sufficiently large j. Therefore

\[
 w_j=\kappa q_j+O(1/n_j).
\tag{14}
\]

Combining (11)-(14),

\[
 \begin{split}
 \frac{w_j-\kappa+(\kappa^2/2)s_jr_j}{s_j}
 &=\beta q_j+\frac{\kappa^2}{2}j(1-q_j)
       +O(1/(n_js_0))\\
 &\longrightarrow\beta.
 \end{split}
\tag{15}
\]

Indeed, j(1-q_j)=O(j squared s_0) tends to zero, and n_j s_0 tends to infinity.

The critical size relation is

\[
 \frac{m_j}{n_j^{1/3}}
 =\left(\frac{m_j^2}{2\,4^j q_j^2}\right)^{1/3}
       (1+o(1))
 \longrightarrow c.
\tag{16}
\]

The chosen n_j are even, so they are admissible cubic graph sizes for all sufficiently large j. Also m_j<n_j eventually.

These sequences have phase tending to 1/2, satisfy
sqrt(m_j)(w_j-kappa)->0, and satisfy the logarithmic retuning
(w_j-kappa)/(s_jr_j)->-kappa squared/2. Equation (15) shows that none of those preceding conditions fixes beta. Integer rounding imposes no additional restriction on this finite next detuning.

## 6. Scope and review request

The density proof uses the actual jump sizes remaining after the coupled quadratic and complementary corrections are combined. It does not apply a density claim to the raw, differently centered quadratic law. The integer construction uses the exact ratio m_j/n_j, retains even n_j, and accounts for the floor r_j.

The graph consequence requires the separately proved exact Schur reduction and its uniform order-s error. This file alone is not an eigenvalue or eigenvector theorem. It proves noncoincidence of the limiting diagonal coefficients and availability of every finite beta.

Requested review: check the single-scale lower bound in the Fourier exponent, the conditional independence after fixing P_0, the positive-probability arguments for both orderings, and every rounding term in (15).
