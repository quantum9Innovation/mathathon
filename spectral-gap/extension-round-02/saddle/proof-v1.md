# SG-E2: a uniform correction throughout the sublinear range

Date: November 14, 2026 Pacific

Owner: manuscript_referee

Integrator: root

Revision: saddle proof v1

Mathematical status proposed: proved, pending independent review

Base: accepted frozen manuscript v5, manifest SHA-256 `ce8f5240a55ef278b9ab2c6ce53cc25f7688fcd28dafd602937c303a06b8ac78`

Prior exposure: the full manuscript audit and its subsequent delta revisions. No other extension attempt or root exploration file was read before this revision was frozen.

## 1. Statements and exact normalization

Let $N$ be a positive integer and $2\le k\le N$. Retain the manuscript's normalized moment $R_k$. The exact objects needed below are

\[
 F_N(z)=\exp\left(Nf(z)\right),\qquad
 f(z)=\frac{z}{1-z}+\log(1-z)
     =\sum_{j\ge2}\frac{j-1}{j}z^j,
\]

\[
 Q_k=k![z^k]F_N(z),\qquad D_k=\frac{N^k}{(N)_k},
 \qquad R_k=D_k\frac{Q_k}{\mathcal L_k}.
\]

For $m\ge1$, the exact leading polynomials are

\[
 \mathcal L_{2m}=\frac{(2m)!}{2^m m!}N^m,
 \qquad
 \mathcal L_{2m+1}=\frac{4m}{3}\frac{(2m+1)!}{2^m m!}N^m.
\]

Write

\[
 \delta=k\bmod2,\qquad K=k-\delta=2m,\qquad
 x=\sqrt{K/N},\qquad \lambda=\frac23Nx^3.
\]

The manuscript's hyperbolic term is exactly

\[
 H_k=\frac{e^\lambda+(-1)^\delta e^{-\lambda}}{2\lambda^\delta}.
\]

In particular the odd argument uses $K=k-1$, throughout this proof.

Define, for $0\le t<1$,

\[
 G(t)=t+\frac{t^2}{2}+(1-t^2)\log(1-t)-\frac23t^3
     =\sum_{j\ge4}\frac{2t^j}{j(j-2)}.
 \tag{1}
\]

**Theorem SG-E2-S1.** For every sequence $b_N\ge2$ with $b_N=o(N)$,

\[
 \sup_{2\le k\le b_N}
 \left|\frac{R_k}{H_k\exp\{NG(\sqrt{k/N})\}}-1\right|
 \longrightarrow0.
 \tag{2}
\]

The supremum is over integers. This retains both parity normalizations and does not assume that $k$ tends to infinity.

**Corollary SG-E2-S2.** Within the sublinear range $2\le k_N=o(N)$,

\[
 \frac{R_{k_N}}{e^{k_N^2/(4N)}H_{k_N}}\longrightarrow1
 \quad\Longleftrightarrow\quad
 \frac{k_N^5}{N^3}\longrightarrow0.
 \tag{3}
\]

If $k_N/N^{3/5}\to c\in(0,\infty)$, the ratio in (3) tends to

\[
 \exp\left(\frac{2}{15}c^{5/2}\right).
 \tag{4}
\]

If $k_N/N^{3/5}\to\infty$ while $k_N=o(N)$, that ratio tends to infinity. Its boundedness is equivalent to $k_N^5/N^3=O(1)$.

**Corollary SG-E2-S3.** Adding the next exponent gives uniform relative accuracy through every range $k\le b_N=o(N^{2/3})$:

\[
 R_k\sim H_k\exp\left(\frac{k^2}{4N}
                    +\frac{2k^{5/2}}{15N^{3/2}}\right).
 \tag{5}
\]

At $k/N^{2/3}\to c\in(0,\infty)$, the ratio to the right side of (5) tends to $e^{c^3/12}$. More generally, each fixed truncation of (1) has the sharp threshold given in Step 6.

The proof uses the accepted v5 uniform square-root correction only for $k\le\sqrt N$. Steps 2 through 4 establish a separate uniform saddle estimate above that range.

## 2. A positive-saddle coefficient estimate with the other peak controlled

Set

\[
 r=\frac{x}{1+x},\qquad
 b=N\left(r\frac{d}{dr}\right)^2 f(r)=2K(1+x).
\]

The saddle equation is exact:

\[
 Nr f'(r)=\frac{Nr^2}{(1-r)^2}=K.
 \tag{6}
\]

There are absolute constants $C,c>0$ such that, whenever $K\ge2$, $0<x\le1/4$ and $\delta\in\{0,1\}$,

\[
 [z^{K+\delta}]F_N(z)
 =\frac{e^{Nf(r)}r^{-K-\delta}}{\sqrt{2\pi b}}
   (1+\varepsilon_{N,K,\delta}),
 \qquad
 |\varepsilon_{N,K,\delta}|
 \le C\left(\frac1K+e^{-c\lambda}\right).
 \tag{7}
\]

The bound remains a valid, possibly non-small bound when $\lambda$ is bounded. It will be used as a relative approximation only where both $K$ and $\lambda$ diverge.

To prove (7), Cauchy's formula reduces the coefficient, after division by $e^{Nf(r)}r^{-K-\delta}$, to

\[
 \frac1{2\pi}\int_{-\pi}^{\pi}
 \exp\{\Phi(\theta)-i\delta\theta\}\,d\theta,
 \qquad
 \Phi(\theta)=N(f(re^{i\theta})-f(r))-iK\theta.
 \tag{8}
\]

All coefficients of $f$ are nonnegative. Hence

\[
 -\Re\Phi(\theta)
 =N\sum_{j\ge2}\frac{j-1}{j}r^j(1-\cos(j\theta))
 \ge Nr^2\sin^2\theta
       +\frac23Nr^3(1-\cos(3\theta)).
 \tag{9}
\]

Use the fixed angle $\eta=\pi/6$. In the central interval $|\theta|\le\eta$, (9) gives $\Re\Phi\le-c_0K\theta^2$, with an absolute $c_0>0$. Since $r\le1/5$, for each fixed $q\ge2$,

\[
 N\sum_{j\ge2}\frac{j-1}{j}j^q r^j\le C_q K.
 \tag{10}
\]

Taylor's inequalities for sine and cosine, together with (6), therefore give

\[
 \Re\Phi(\theta)=-\frac b2\theta^2+O(K\theta^4),
 \qquad |\Im\Phi(\theta)|\le CK|\theta|^3.
 \tag{11}
\]

These bounds are uniform in $N,K$. By symmetry, the central integral is the integral of

\[
 e^{\Re\Phi(\theta)}
 \cos(\Im\Phi(\theta)-\delta\theta).
\]

The inequalities $|\cos u-1|\le u^2/2$ and
$|e^u-e^v|\le |u-v|e^{\max(u,v)}$ for real $u,v$ show that its difference from $e^{-b\theta^2/2}$, in absolute value, is at most

\[
 C\left(K\theta^4+K^2\theta^6+\theta^2\right)
 e^{-c_1K\theta^2}.
 \tag{12}
\]

The integral of (12) is $O(K^{-3/2})$, while the Gaussian integral is $\sqrt{2\pi/b}$, of order $K^{-1/2}$. Extending that Gaussian integral beyond the central interval costs $O(e^{-c_2K})$.

It remains to control the angular peak near $\pi$, which cannot be discarded merely from the pair term. Write $\theta=\pi+u$, modulo $2\pi$, with $|u|\le\eta$. Then

\[
 1-\cos(3\theta)=1+\cos(3u)\ge1,
 \qquad \frac23Nr^3=\frac{\lambda}{(1+x)^3}\ge c_3\lambda.
\]

Thus (9) bounds the integral over this neighborhood by

\[
 C e^{-c_3\lambda}\int_{-\eta}^{\eta}e^{-c_4Ku^2}\,du
 \le \frac C{\sqrt K}e^{-c_3\lambda}.
 \tag{13}
\]

On the remaining angles, $|\sin\theta|\ge\sin\eta$, so (9) bounds the integral by $Ce^{-c_5K}$. After division by the main Gaussian integral, this is absorbed into $C/K$. Equations (12) and (13) prove (7). This argument explicitly accounts for the almost periodic pair contribution and its suppression by triples.

## 3. Restoring the exact even and odd normalizations

Define

\[
 h(x)=x+(x^2-1)\log(1+x)-\frac{x^2}{2},
 \qquad q(x)=h(x)-\frac23x^3.
\]

The exponent remaining after the Gaussian pair normalization is exactly

\[
 Nf(r)-K\log r+K\log x-\frac K2=Nh(x).
 \tag{14}
\]

Stirling's formula, with its remainder $O(1/K)$, and (7) give

\[
 \frac{Q_k}{\mathcal L_k}
 =\frac{e^{Nh(x)}(1+x)^{\delta-1/2}}{2\lambda^\delta}
 \left(1+O\left(K^{-1}+e^{-c\lambda}\right)\right).
 \tag{15}
\]

For clarity, the additional odd normalization is exactly

\[
 \frac{3}{2Kr}=\frac{1+x}{\lambda}.
 \tag{16}
\]

It converts the even prefactor $(1+x)^{-1/2}/2$ into the odd prefactor $(1+x)^{1/2}/(2\lambda)$. No parity-dependent factor is omitted.

Dividing (15) by the exact $H_k$ introduces the factor
$(1+(-1)^\delta e^{-2\lambda})^{-1}$. Consequently, once $K$ and $\lambda$ exceed fixed sufficiently large constants,

\[
 \log\frac{R_k}{H_k}
 =\log D_k+Nq(x)
  +(\delta-\tfrac12)\log(1+x)
  +O\left(K^{-1}+e^{-c\lambda}\right).
 \tag{17}
\]

The constants and thresholds in (17) are absolute for $x\le1/4$. Taking a logarithm is justified because the relative error in (15) is then at most $1/2$. The small-$\lambda$ regime will instead be handled by the accepted manuscript theorem.

## 4. Combining the saddle and permutation exponents

Put $t=\sqrt{k/N}$, $u=t^2$, and

\[
 I(u)=u+(1-u)\log(1-u).
\]

Because $g(v)=-\log(1-v)$ is increasing, its left Riemann sum satisfies

\[
 0\le NI(k/N)-\log D_k
 \le -\log(1-k/N).
 \tag{18}
\]

In particular, the error is $O(k/N)$ for $k/N\le1/16$. This bounds the full denominator correction, including all of its higher powers.

Direct differentiation gives

\[
 h'(x)=2x\log(1+x),\qquad
 q'(x)=2x(\log(1+x)-x),\qquad |q'(x)|\le x^3.
\]

Since $t^2-x^2=\delta/N$, the mean value theorem yields

\[
 N|q(t)-q(x)|\le Nt^3(t-x)\le k/N.
 \tag{19}
\]

The exact identity

\[
 I(t^2)+q(t)=G(t)
 \tag{20}
\]

now turns (17) into the uniform estimate

\[
 \log\frac{R_k}{H_k}
 =NG(\sqrt{k/N})
  +(\delta-\tfrac12)\log(1+\sqrt{K/N})
  +O\left(\frac{k}{N}+\frac1K+e^{-c\lambda}\right).
 \tag{21}
\]

This holds for $k/N\le1/16$ once $K$ and $\lambda$ exceed the fixed thresholds from (17). In particular it holds uniformly for $\sqrt N\le k\le N/16$ when $N$ is sufficiently large.

The explicit parity prefactor in (21) explains an even correction of order $-\sqrt{k/N}/2$ and an odd correction of order $+\sqrt{k/N}/2$. It tends to one multiplicatively throughout the sublinear range, but should not be mistaken for an error of order $k/N$.

## 5. Uniformity down to fixed orders

Fix any $b_N=o(N)$. On the part of the range with $k>\sqrt N$, eventually $k/N\le1/16$, and uniformly

\[
 K\ge\sqrt N-1,\qquad
 \lambda\ge cN^{1/4},\qquad
 \sqrt{k/N}\le\sqrt{b_N/N}\longrightarrow0.
\]

Equation (21) therefore proves (2) uniformly on that part of the range.

For $2\le k\le\sqrt N$, the accepted v5 square-root theorem gives

\[
 \sup_{2\le k\le\sqrt N}
 \left|\frac{R_k}{e^{k^2/(4N)}H_k}-1\right|\longrightarrow0.
 \tag{22}
\]

The positive series in (1) gives, uniformly on the same range,

\[
 0\le NG(\sqrt{k/N})-\frac{k^2}{4N}
 \le C\frac{k^{5/2}}{N^{3/2}}
 \le CN^{-1/4}.
 \tag{23}
\]

Combining (22) and (23) proves (2) below $\sqrt N$. Both parts together prove Theorem SG-E2-S1, including fixed orders and sequences that change parity.

This patch does not assert that a single positive saddle is relatively accurate when $\lambda$ is small. It uses the parity-sensitive approximation already proved in that range.

## 6. Sharp truncation thresholds and the next coefficients

For a fixed integer $p\ge4$, define

\[
 G_p(t)=\sum_{j=4}^{p}\frac{2t^j}{j(j-2)}.
\]

All remaining coefficients are positive. As $t\to0$,

\[
 G(t)-G_p(t)
 =\frac{2}{(p+1)(p-1)}t^{p+1}(1+O_p(t)).
 \tag{24}
\]

The relative error in (24) is uniform for $0<t\le1/4$. For example, the remaining tail is bounded above by its first coefficient times $t^{p+1}/(1-t)$ and below by its first term.

By (2), for every sequence $2\le k=o(N)$,

\[
 \log\frac{R_k}{H_k e^{NG_p(\sqrt{k/N})}}
 =\frac{2}{(p+1)(p-1)}
   \frac{k^{(p+1)/2}}{N^{(p-1)/2}}
   (1+O_p(\sqrt{k/N}))+o(1).
 \tag{25}
\]

The $o(1)$ is uniform on every specified sublinear upper range. Positivity in (24) proves that relative convergence to one in (25) occurs if and only if

\[
 \frac{k^{p+1}}{N^{p-1}}\longrightarrow0,
 \quad\text{equivalently}\quad
 k=o\left(N^{(p-1)/(p+1)}\right).
 \tag{26}
\]

Boundedness of the ratio is equivalent to boundedness of $k^{p+1}/N^{p-1}$. If $k/N^{(p-1)/(p+1)}\to c\in(0,\infty)$, its limit is

\[
 \exp\left(\frac{2c^{(p+1)/2}}{(p+1)(p-1)}\right).
 \tag{27}
\]

These conclusions apply to arbitrary changing parities. They also imply uniform relative accuracy over $2\le k\le b_N$ when $b_N=o(N^{(p-1)/(p+1)})$, either directly from the uniform form of (2) or by taking the supremum of the positive tail.

The first terms are

\[
 NG(\sqrt{k/N})
 =\frac{k^2}{4N}
  +\frac{2k^{5/2}}{15N^{3/2}}
  +\frac{k^3}{12N^2}
  +\frac{2k^{7/2}}{35N^{5/2}}
  +\cdots.
 \tag{28}
\]

Taking $p=4$ proves SG-E2-S2. Taking $p=5$ proves SG-E2-S3. Thus the quintic block intensity identifies the correct next scale, but its raw coefficient $4/5$ is not the final correction coefficient. Saddle displacement, pair availability and the permutation denominator must be combined. Their combined coefficient is $2/15$.

## 7. Evidence, limitations and handoff

The proof's only inherited asymptotic dependency is the accepted v5 uniform square-root theorem in (22). The exact coefficient representation and the leading polynomials are restated in Step 1. All larger-order estimates are proved in Steps 2 through 4. The numerical script `saddle-check.py` evaluates the exact positive normalized recurrence in floating point. Its output `saddle-check-results.json` corroborates the quintic coefficient and the opposite parity prefactors. It is not an interval certificate or a premise of the proof.

No claim is made here about $k$ comparable to $N$, growing truncation order $p$, a global explicit convergence rate below $\sqrt N$, a new graph eigenvalue bound, or literature-wide novelty. The generating function and saddle method are general identities and techniques. Priority of the particular uniform refinements requires a separate source check.

Proposed canonical update: SG-E2 has a proof candidate for a uniform correction throughout $k=o(N)$, the sharp $N^{3/5}$ obstruction for the former square-root correction, and the coefficient $2/15$ of the next exponent. Review status should remain unreviewed until this exact frozen proof is independently checked.

Requested next action: audit (7), (16), (18) through (21), and the uniform patch (22) through (23), then decide whether to integrate SG-E2-S1 through SG-E2-S3. No canonical or manuscript file was changed.
