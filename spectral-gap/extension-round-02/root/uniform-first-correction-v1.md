# Uniform first correction and the sharp worst-case constant

Revision 1. Written November 14, 2026 Pacific. Owner and integrator: root.

Status: proved candidate, awaiting separate review. This note was written after reading the separately frozen RATE-1, CORR-1 and saddle proofs. It is a synthesis, not an independent discovery of their coefficients. It does not modify those frozen inputs.

## 1. Statement

Use the accepted diagonal normalization, with $K=2\lfloor k/2\rfloor$, $\epsilon=k-K$, $\lambda=(2/3)\sqrt{K^3/N}$ and the exact even or odd factor $H_k$. Put

\[
W_{N,k}=\frac{R_k}{e^{k^2/(4N)}H_k},\qquad
\psi_\epsilon(c)=\frac{2\epsilon-1}{2}\sqrt c+\frac{2}{15}c^{5/2}.
\]

For every fixed real $C>0$,

\[
\sup_{2\le k\le C\sqrt N}
\left|N^{1/4}(W_{N,k}-1)-\psi_{k\bmod2}(k/\sqrt N)\right|
\longrightarrow0.
\tag{U1}
\]

In particular, the exact asymptotic constant in the uniform error is

\[
\boxed{
\lim_{N\to\infty}N^{1/4}
\sup_{2\le k\le C\sqrt N}|W_{N,k}-1|
=\frac{\sqrt C}{2}+\frac{2}{15}C^{5/2}.
}
\tag{U2}
\]

All suprema are over integers. There are eligible integers for all sufficiently large $N$. Thus the order is optimal for every fixed positive range endpoint, not only for $C\ge1$.

## 2. Inputs and their exact scope

The finite inequality (5) and the constant derivation in Section 7 of `../rate/square-root-rate-v1.md`, SHA256 `ed472ce70521c37d59c4e3efc88bf7e883d1a75526023ef2c3a15c57bcd9c581`, give

\[
|W_{N,k}-1|\le A_1(C)N^{-1/4}+A_2(C)N^{-1/2}+A_3(C)N^{-1}
\tag{U3}
\]

whenever $N\ge16C^2$ and $2\le k\le C\sqrt N$. The frozen theorem states $C\ge1$. The same displayed constants and proof also apply for every $C>0$. This extension of scope is justified directly below, rather than silently attributed to the narrower statement.

Section 7 uses the implications $k\le N/4$, $K\le C\sqrt N$, $\eta\le3C^2/4$ and $\delta\le C^2$. They hold for every $C>0$ under these hypotheses. Every subsequent coefficient comparison is monotone in these nonnegative upper bounds. The inequalities $\tau\le\delta$, $\log D_k\le k^2/N$ and $r\le C^2/3$ use only $k\le N/4$ and $k\ge2$. None uses $C\ge1$. This proves (U3) on the asserted enlarged scope. An empty range makes it vacuous.

The explicit leading constant is

\[
\begin{aligned}
a&=3C^2/4,\\
B_1(C)&=\frac43(2+3a)\sqrt C+\frac{2144}{27}C^{5/2},\\
A_1(C)&=e^{7C^2/4}B_1(C)+2e^{11C^2/4}C^{5/2}.
\end{aligned}
\]

In particular,

\[
A_1(C)\longrightarrow0\quad\text{as }C\downarrow0.
\tag{U4}
\]

The second input is equation (21) of `../saddle/proof-v1.md`, SHA256 `c9033ac8ff15bd5265771eaad4d4b7eeeb2b2e19860decfa63e0b2bb8c177da8`. It gives, uniformly when its large-$K$, large-$\lambda$ conditions hold,

\[
\log\frac{R_k}{H_k}
=NG(\sqrt{k/N})+(\epsilon-1/2)\log(1+\sqrt{K/N})
+O\left(k/N+K^{-1}+e^{-c\lambda}\right),
\tag{U5}
\]

where $G(t)=\sum_{j\ge4}2t^j/[j(j-2)]$. That proof has passed a separate frozen review. Its constants are absolute for $k/N\le1/16$.

## 3. Positive limiting square-root scales

Fix $0<d<C$. On $d\sqrt N\le k\le C\sqrt N$, the hypotheses of (U5) hold for all sufficiently large $N$, uniformly. Its remainder is $O_{C,d}(N^{-1/2})$, since $K$ is of order $\sqrt N$ and $\lambda$ is bounded below by a positive multiple of $N^{1/4}$.

The convergent series for $G$ and the elementary logarithm expansion give

\[
NG(\sqrt{k/N})-\frac{k^2}{4N}
=\frac{2k^{5/2}}{15N^{3/2}}+O_C(N^{-1/2}),
\]

\[
(\epsilon-1/2)\log(1+\sqrt{K/N})
=\frac{2\epsilon-1}{2}\sqrt{k/N}+O_{C,d}(N^{-1/2}).
\]

For the second identity, the logarithm remainder is $O(k/N)$. Replacing $\sqrt K$ by $\sqrt k$ costs at most $1/\sqrt K$ before division by $\sqrt N$, which is smaller than the stated error on this range. Therefore

\[
\log W_{N,k}
=N^{-1/4}\psi_\epsilon(k/\sqrt N)+O_{C,d}(N^{-1/2}).
\]

The leading function is bounded on $[d,C]$. Exponentiation changes the error only by another $O_{C,d}(N^{-1/2})$. Hence (U1) holds uniformly on this restricted interval.

## 4. Closing the small-order boundary

Use (U3) with endpoint $d>0$. For each fixed $d$,

\[
\limsup_{N\to\infty}
N^{1/4}\sup_{2\le k\le d\sqrt N}|W_{N,k}-1|
\le A_1(d).
\]

Also, for either parity and $0\le c\le d$,

\[
|\psi_\epsilon(c)|\le\frac{\sqrt d}{2}+\frac{2}{15}d^{5/2}.
\]

Split the full range at $d\sqrt N$. Section 3 makes the upper part's error tend to zero. The lower part's limit superior is bounded by the sum of the last two displayed right sides. Let $d\downarrow0$ and use (U4). This proves (U1), including fixed orders, the critical cubic range, and changing parity.

## 5. The maximum and its attainment

For $0\le c\le C$,

\[
|\psi_0(c)|\le\psi_1(c)
\le\psi_1(C)=\frac{\sqrt C}{2}+\frac{2}{15}C^{5/2}.
\]

The odd function is continuous and strictly increasing. Let $k_N$ be the largest odd integer not exceeding $C\sqrt N$. Then $k_N/\sqrt N\to C$. Equation (U1), applied to these orders, gives the matching lower limit. Its uniform upper bound gives the matching upper limit. This proves (U2).

## 6. Review boundary

The general proof uses only the frozen rate inequality and the frozen saddle estimate. The independent conditioned-Poisson proof CORR-1 gives a second derivation of the coefficient at every fixed positive scale. No numerical calculation is a premise of (U1) or (U2).

The only additional bridge requiring review is the extension of the explicit constant calculation from $C\ge1$ to $C>0$, followed by the two-interval uniformity argument. No optimality is asserted for the conservative finite constants $A_i(C)$. Equation (U2) is the optimal asymptotic constant for the supremum error.
