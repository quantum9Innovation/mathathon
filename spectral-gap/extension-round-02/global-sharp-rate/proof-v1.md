# The sharp global error scale and its parity profile

Revision 1. November 15, 2026 UTC. Mathematical status: proved below, awaiting an independent review. This packet strengthens the rate for the existing GLOBAL-1 approximation and leaves that frozen proof unchanged. No historical firstness claim is made.

## 1. Definitions and statement

For a uniform permutation matrix of size $N$, let

\[
a_k=\mathbb E\prod_{i=1}^k(M_{ii}-1/N),\qquad
Q_k=(N)_kN^ka_k.
\]

The falling factorial is $(N)_k=N(N-1)\cdots(N-k+1)$. For $m\ge1$, put

\[
L_{2m}=\frac{(2m)!}{2^m m!}N^m,\qquad
L_{2m+1}=\frac{4m}{3}\frac{(2m+1)!}{2^m m!}N^m,
\qquad D_k=\frac{N^k}{(N)_k}.
\]

Then the previously defined diagonal normalization is $R_k=D_kQ_k/L_k$. For every integer $2\le k\le N$, define

\[
\epsilon=k\bmod2,\quad K=k-\epsilon,\quad
x=\sqrt{K/N},\quad \lambda=\frac23\sqrt{K^3/N},
\]

\[
H_k=\frac{e^\lambda+(-1)^\epsilon e^{-\lambda}}{2\lambda^\epsilon},
\quad
q(x)=x+(x^2-1)\log(1+x)-\frac{x^2}{2}-\frac23x^3,
\]

\[
\mathcal A_{N,k}=D_kH_ke^{Nq(x)}(1+x)^{\epsilon-1/2},
\qquad E_{N,k}=\frac{R_k}{\mathcal A_{N,k}}-1.
\tag{1}
\]

For $c>0$, set $\ell(c)=(2/3)c^{3/2}$ and

\[
p_0(t)=t\tanh t,\qquad p_1(t)=t\coth t-1,
\]

\[
\boxed{
\Phi_\epsilon(c)=\frac{3(2\epsilon-1)}{4c}
\{p_\epsilon(\ell(c))-\ell(c)\}.
}
\tag{2}
\]

Both profiles extend continuously to zero with value zero.

**Theorem GSR-1.** The following full-range profile holds:

\[
\boxed{
\sup_{2\le k\le N}
\left|N^{1/3}E_{N,k}
-\Phi_{k\bmod2}(k/N^{1/3})\right|\longrightarrow0.
}
\tag{3}
\]

In particular,

\[
\boxed{
\sup_{2\le k\le N}|E_{N,k}|
=\mathfrak C N^{-1/3}+o(N^{-1/3}),
}
\tag{4}
\]

where the positive absolute constant is

\[
\boxed{
\mathfrak C=\max_{c>0}\frac3{4c}
\left(1-\frac{2\ell(c)}{e^{2\ell(c)}-1}\right).
}
\tag{5}
\]

Thus GLOBAL-1 has uniform error $O(N^{-1/3})$, and this exponent is optimal for its stated approximation. Formula (4) is an asymptotic assertion. No numerical finite-$N$ threshold for the limiting constant is claimed.

The maximum in (5) is attained at a unique $c_*>0$. Its approximate values are

\[
c_*=1.16540187318\ldots,\qquad
\mathfrak C=0.395496270091\ldots.
\tag{6}
\]

The exact specification is (5), together with the unique-root characterization in Section 8. The decimals are corroborating evaluations.

## 2. Exact inputs and cancellation of the denominator

The accepted positive representation is

\[
Q_k=k![z^k]\exp\left(N\sum_{j\ge2}\frac{j-1}{j}z^j\right).
\tag{7}
\]

It holds for the permutation moments on $0\le k\le N$. The recurrence and leading coefficients underlying it are known results of Collins and Nagatsu. The Laguerre and real integral reformulations used below are classical identities.

The factor $D_k$ cancels exactly in the error under consideration:

\[
1+E_{N,k}
=\frac{Q_k/(L_kH_k)}{e^{Nq(x)}(1+x)^{\epsilon-1/2}}.
\tag{8}
\]

This cancellation also holds at $k=N$. No approximation of $D_k$ is used in this proof.

Three frozen estimates will be used in their stated ranges.

1. The finite hyperbolic comparison gives

   \[
   \left|\log(R_k/H_k)\right|\le4k^2/N
   \quad\text{if }2\le k\le N/4,\quad4k^2\le N.
   \tag{9}
   \]

2. The accepted global complex coefficient estimate gives, with absolute constants,

   \[
   |E_{N,k}|\le C\{K^{-1}+e^{-\lambda/8}\}
   \quad\text{if }\lambda\ge1,\quad2\le k\le N.
   \tag{10}
   \]

   In particular its right side is $O(N^{-1/2})$ uniformly for $k\ge\sqrt N$.

3. Exact pair availability for blocks of sizes two, three and four is represented in Section 3 below. It follows directly from (7), so the critical expansion does not depend on an earlier asymptotic correction formula.

The input hashes are recorded in the manifest. Sections 4 and 5 give the real saddle comparison in detail, including the second saddle that cannot be discarded at the critical scale.

## 3. Uniform expansion on compact critical intervals

Fix $0<d<C<\infty$ and restrict to $dN^{1/3}\le k\le CN^{1/3}$. All estimates in this section are uniform in this range and in the parity. Then $K\to\infty$, and $\lambda$ stays in a compact subset of $(0,\infty)$.

Let $J$ have a Poisson distribution of mean $\lambda$ conditioned to have parity $\epsilon$. Independently, let $V$ be Poisson with mean

\[
\eta=\frac{3K^2}{4N}=\frac{27\lambda^2}{16K}.
\]

Put $t=J-\epsilon$, $m=K/2$, and $s=3t/2+2V$. Thus $s$ is a nonnegative integer. Let

\[
w_\epsilon(s)=\frac{(m-\epsilon)_s}{m^s}
\quad(0\le s\le m-\epsilon),
\]

with value zero outside this integer range. The normalized contribution to $Q_k/(L_kH_k)$ from these three block sizes is exactly

\[
e^\eta\mathbb Ew_\epsilon(s).
\tag{11}
\]

Differentiating the even and odd exponential series gives

\[
\mathbb Et=p_\epsilon(\lambda),\qquad
\mathbb Et^2=\lambda^2+(1-2\epsilon)p_\epsilon(\lambda).
\tag{12}
\]

All moments of $t$ of a fixed order are uniformly bounded on the present compact interval. The same is true of $s$, since $\eta=O(K^{-1})$.

Set $A=s(s-1+2\epsilon)/(2m)$. The elementary product estimate

\[
0\le e^{-A}-w_\epsilon(s)\le4s^3/m^2
\]

and the inequality $|e^{-A}-1+A|\le A^2/2$ imply

\[
\mathbb Ew_\epsilon(s)=1-\mathbb EA+O(K^{-2}).
\tag{13}
\]

The product estimate includes unavailable values of $s$. It follows by expanding the product logarithm for $s\le m/2$ and bounding both terms by one for larger $s$. Thus no unproved tail truncation enters (13).

Terms containing $V$ contribute $O(K^{-2})$ to $\mathbb EA$, because $\mathbb EV=O(K^{-1})$. Using (12) in the remaining terms gives

\[
\mathbb EA
=\frac1K\left\{\frac94\lambda^2
+\frac34(1-2\epsilon)p_\epsilon(\lambda)\right\}
+O(K^{-2}).
\tag{14}
\]

All block sizes at least five together have weight

\[
\sum_{j\ge5}N\frac{j-1}{j}x^j
\le\frac{Nx^5}{1-x}=O(K^{-2}).
\]

Removing their availability factors gives an upper bound on their additional positive contribution. After parity projection, division by $\cosh\lambda$ or $\sinh\lambda$ is harmless on the present compact interval. Consequently their total contribution to $Q_k/(L_kH_k)$ is $O(K^{-2})$.

Combining (11) to (14), and $e^\eta=1+\eta+O(K^{-2})$, yields

\[
\frac{Q_k}{L_kH_k}
=1+\frac1K\left\{-\frac9{16}\lambda^2
+\frac34(2\epsilon-1)p_\epsilon(\lambda)\right\}
+O(K^{-2}).
\tag{15}
\]

On the other hand, $x=3\lambda/(2K)$ and

\[
q(x)=-x^4/4+O(x^5),\qquad \log(1+x)=x+O(x^2).
\]

Therefore

\[
e^{Nq(x)}(1+x)^{\epsilon-1/2}
=1+\frac1K\left\{-\frac9{16}\lambda^2
+\frac34(2\epsilon-1)\lambda\right\}
+O(K^{-2}).
\tag{16}
\]

Dividing (15) by (16) in (8) proves

\[
\boxed{
E_{N,k}=\frac{3(2\epsilon-1)}{4K}
\{p_\epsilon(\lambda)-\lambda\}+O_{d,C}(K^{-2}).
}
\tag{17}
\]

Since $K=k+O(1)$, this proves (3) uniformly on every compact critical interval $d\le k/N^{1/3}\le C$.

## 4. A uniform real two-saddle estimate

The exact elementary integral is

\[
Q_k=\frac1{(N-k)!}\int_0^\infty e^{-v}v^{N-k}(N-v)^k\,dv.
\tag{18}
\]

Splitting at $v=N$ gives $Q_k=T_++(-1)^kT_-$, where

\[
T_+=\frac{N^{N+1}e^{-N}}{(N-k)!}
\int_0^1e^{Nt}t^k(1-t)^{N-k}\,dt,
\]

\[
T_-=\frac{N^{N+1}e^{-N}}{(N-k)!}
\int_0^\infty e^{-Nt}t^k(1+t)^{N-k}\,dt.
\tag{19}
\]

Both integrals have their unique maximum at $u=\sqrt{k/N}$. For integers $N,k$ with $2\le k\le N/4$ and $k\to\infty$, ordinary real Laplace expansion and Stirling's formula give

\[
T_\pm=B_\pm\{1+O(k^{-1})\},
\tag{20}
\]

The implied constants and a sufficient lower threshold for $k$ are absolute. In particular, the estimate is uniform as $u$ tends to zero.

where

\[
B_+=\frac{(Nu)^k}{\sqrt{2(1+u)}}
\exp\left(N\{u-u^2-(1-u^2)\log(1+u)\}\right),
\]

\[
B_-=\frac{(Nu)^k}{\sqrt{2(1-u)}}
\exp\left(N\{-u-u^2-(1-u^2)\log(1-u)\}\right).
\tag{21}
\]

For completeness, rescale $t=us$ and divide the logarithmic phase difference by $k$. The resulting normalized derivatives are

\[
F_\pm'(s)=\frac{1-s^2}{s(1\mp us)},\qquad
F_\pm''(1)=-\frac2{1\mp u}.
\tag{22}
\]

On a fixed neighborhood of one, derivatives through order six are uniformly bounded for $0\le u\le1/2$, and the second derivative stays negative. Outside that neighborhood the left part has a fixed negative phase gap. On the right, $F_\pm'$ stays below a fixed negative constant. Taylor expansion near one with the odd cubic integral canceled gives an absolute error $O(k^{-3/2})$ against a leading integral of order $k^{-1/2}$. The outer integrals are exponentially small. This proves uniform relative error $O(k^{-1})$. The factor $(N-k)!$ contributes only $O((N-k)^{-1})=O(k^{-1})$ here. These facts also prove (20) when $u$ tends to zero.

Define $h(x)=q(x)+2x^3/3$ and

\[
P_{N,k}=\frac{L_k}{2\lambda^\epsilon}
e^{Nh(x)}(1+x)^{\epsilon-1/2}.
\tag{23}
\]

The unnormalized target in (8) is exactly

\[
L_kH_ke^{Nq(x)}(1+x)^{\epsilon-1/2}
=P_{N,k}\{1+(-1)^\epsilon e^{-2\lambda}\}.
\tag{24}
\]

For integers $N,k$ with $2\le k\le N/4$ and $K\to\infty$, we next verify

\[
B_+/P_{N,k}=1+O(K^{-1}).
\tag{25}
\]

Again the implied constant and a sufficient lower threshold for $K$ are absolute.

For even $k=K$, Stirling gives

\[
L_K=\sqrt2(NK/e)^{K/2}\{1+O(K^{-1})\},
\]

and substitution into (21) and (23) proves (25). For odd $k=K+1$, the exact normalizers give

\[
\frac{P_{N,K+1}}{P_{N,K}}=\frac{(K+1)(1+x)}x.
\]

Regard the logarithm of $B_+$ in (21) as a smooth function $g(v)$ of its degree. Direct differentiation gives

\[
g'(v)=\log(Nu_v(1+u_v))
-\frac1{4Nu_v(1+u_v)},\qquad u_v=\sqrt{v/N}.
\]

Its variation on $K\le v\le K+1$ is $O(K^{-1})$. Integration gives the same adjacent-degree ratio as above up to relative $O(K^{-1})$. This proves (25) for odd orders as well.

## 5. Match the negative saddle instead of discarding it

The exact ratio of the two leading real saddle terms is

\[
\frac{B_-}{B_+}
=\exp\{\operatorname{artanh}u-N\Delta(u)\},
\]

\[
\Delta(u)=2u-(1-u^2)\log\frac{1+u}{1-u}
=\frac43u^3+O(u^5),
\tag{26}
\]

with an absolute remainder bound for $u\le1/2$. Put $\lambda_k=(2/3)k^{3/2}/\sqrt N$. Since $0\le\lambda_k-\lambda\le u$, we have

\[
\frac{B_-}{B_+}=e^{-2\lambda}e^\theta,
\qquad |\theta|\le C(u+Nu^5).
\tag{27}
\]

For $k\le\sqrt N$, the last bound tends to zero uniformly. Hence

\[
\left|\frac{B_-}{B_+}-e^{-2\lambda}\right|
\le C(u+Nu^5)e^{-2\lambda}.
\tag{28}
\]

Combining (20), (24), (25), and (28), and dividing by a denominator bounded away from zero when $\lambda\ge1$, proves

\[
\boxed{
|E_{N,k}|\le C\left\{K^{-1}
+\left(\sqrt{k/N}+\frac{k^{5/2}}{N^{3/2}}\right)e^{-2\lambda}\right\}
}
\tag{29}
\]

There are absolute constants $C,N_0,K_0$ such that (29) holds for all integers $N\ge N_0$ and $2\le k\le\sqrt N$ satisfying $K\ge K_0$ and $\lambda\ge1$. This is the improvement needed below the square-root scale. It preserves the exact odd factor in (24).

If $c_k=k/N^{1/3}$, then $K\ge k/2$ and

\[
\lambda\ge\frac1{3\sqrt2}c_k^{3/2}.
\]

For any fixed $C_0\ge4$, (29) implies

\[
\begin{aligned}
\limsup_{N\to\infty}
N^{1/3}\sup_{C_0N^{1/3}\le k\le\sqrt N}|E_{N,k}|
\le C_1\left\{\frac2{C_0}
+\sup_{t\ge C_0}(\sqrt t+t^{5/2})
e^{-2t^{3/2}/(3\sqrt2)}\right\}.
\end{aligned}
\tag{30}
\]

The right side tends to zero as $C_0\to\infty$. The accepted estimate (10) also gives

\[
N^{1/3}\sup_{\sqrt N\le k\le N}|E_{N,k}|
=O(N^{-1/6})\longrightarrow0.
\tag{31}
\]

Thus the entire upper tail of the critical variable is negligible, including $k=N$.

## 6. Fixed orders and the lower tail

The identities $q(0)=0$ and $q'(x)=2x(\log(1+x)-x)$ imply

\[
-x^4/4\le q(x)\le0\quad(x\ge0).
\]

Also $0\le\log D_k\le k^2/N$ for $k\le N/4$. Consequently

\[
\left|\log(\mathcal A_{N,k}/H_k)\right|
\le\frac54\frac{k^2}N+\frac12\sqrt{k/N}.
\]

With (9), this gives

\[
\left|\log(1+E_{N,k})\right|
\le6k^2/N+\tfrac12\sqrt{k/N}
\tag{32}
\]

when $4k^2\le N$ and $k\le N/4$. For every fixed $d>0$, these conditions hold throughout $2\le k\le dN^{1/3}$ for sufficiently large $N$. Therefore

\[
\boxed{
\limsup_{N\to\infty}N^{1/3}
\sup_{2\le k\le dN^{1/3}}|E_{N,k}|
\le6d^2+\tfrac12\sqrt d.
}
\tag{33}
\]

The right side tends to zero as $d\downarrow0$. This includes every fixed order and requires no division by a small odd hyperbolic parameter.

## 7. Full uniform profile and the sharp constant

Since $0\le p_\epsilon(t)\le t$, equation (2) gives

\[
|\Phi_\epsilon(c)|\le\tfrac12\sqrt c.
\tag{34}
\]

More explicitly,

\[
\Phi_0(c)=\frac3{4c}\frac{2\ell(c)}{e^{2\ell(c)}+1}>0,
\]

\[
\Phi_1(c)=-\frac3{4c}
\left(1-\frac{2\ell(c)}{e^{2\ell(c)}-1}\right)<0.
\tag{35}
\]

Both profiles tend to zero as $c\to\infty$, and $|\Phi_\epsilon(c)|\le3/(4c)$ suffices there. Split the range into $k\le dN^{1/3}$, $dN^{1/3}\le k\le C_0N^{1/3}$, and $k\ge C_0N^{1/3}$. Equations (17), (30), (31), (33), and (34) prove (3) by first taking $N\to\infty$, then $d\downarrow0$ and $C_0\to\infty$.

For every $c>0$ the odd absolute profile strictly exceeds the even profile, because

\[
|\Phi_1(c)|-\Phi_0(c)
=\frac3{4c}\left(1-\frac{2\ell(c)}{\sinh(2\ell(c))}\right)>0.
\tag{36}
\]

The maximum in (5) therefore exists, is positive, and dominates both parities. Equation (3) gives the corresponding uniform upper bound in (4). If $k_N$ is an odd integer nearest $c_*N^{1/3}$, then $k_N/N^{1/3}\to c_*$ and (3) gives the matching lower bound. This proves (4), including optimality of the exponent. Along these maximizing odd orders the error is negative.

## 8. Unique maximizing scale

Set $z=2\ell(c)=(4/3)c^{3/2}$. Apart from the positive factor $(3/4)^{1/3}$, the function maximized in (5) is

\[
g(z)=z^{-2/3}\left(1-\frac z{e^z-1}\right).
\]

Its derivative has the sign of $-H(z)$, where

\[
H(z)=2e^{2z}-(3z^2-z+4)e^z-z+2.
\tag{37}
\]

Direct series expansion gives

\[
H(z)=-\frac{z^3}2-\frac{z^4}6
+\sum_{n\ge5}\frac{2^{n+1}-3n^2+4n-4}{n!}z^n.
\tag{38}
\]

Every displayed coefficient for $n\ge5$ is positive. Indeed, the coefficient numerator is five at $n=5$, and its value at $n+1$ minus twice its value at $n$ is $3n^2-10n+5>0$ for $n\ge5$.

It follows that $H(z)/z^4$ is strictly increasing on $z>0$. Its limit at zero is negative infinity and its limit at infinity is positive infinity. Thus (37) has exactly one positive root $z_*$. The function $g$ increases before that root and decreases afterward, proving uniqueness. The exact maximizing scale is

\[
c_*=(3z_*/4)^{2/3}.
\tag{39}
\]

## 9. Worked example and finite corroboration

Take even and odd integer sequences with $k/N^{1/3}\to1$. Equation (3) gives the distinct limits

\[
N^{1/3}E_{N,k}\longrightarrow
\begin{cases}
\displaystyle\frac1{e^{4/3}+1},&k\text{ even},\\[6pt]
\displaystyle\frac1{e^{4/3}-1}-\frac34,&k\text{ odd}.
\end{cases}
\]

The even error is positive and the odd error is negative. This is a direct boundary example for the sharp global rate.

The saved finite checks use the exact polynomial recurrence at 60 decimal digits. Exhaustive scans over $2\le k\le N$ give the following corroboration:

| $N$ | Maximizing order | $N^{1/3}\sup_k|E_{N,k}|$ |
| --- | --- | --- |
| $512$ | $11$ | $0.3753664734$ |
| $4096$ | $19$ | $0.3847527142$ |
| $32768$ | $39$ | $0.3901488831$ |

All three maximizing orders are odd. Twenty-four additional profile checks include both parities through $N=10^9$. These numerical observations are not used in the proof or in the uniqueness argument.

## 10. Explanation and evidence boundary

The previous $N^{-1/4}$ global bound came from a conservative estimate near the square-root scale. Matching both saddle contributions to the exact hyperbolic factor gives a smaller error bound there. The sharper analysis locates the largest error at $k$ of order $N^{1/3}$, where the two saddle contributions are both visible. The approximation itself is unchanged.

At this scale, the four-block term and the quadratic availability loss appear in both the moment and its approximation and cancel in their ratio. The remaining term records the difference between a parity-conditioned triple count and its unconditioned mean. It has opposite signs in the two parities. The odd error is larger in absolute value and determines the sharp global constant.

The critical coefficient and the candidate maximizing equation were supplied as conjectural calculations before this attempt. They were rederived in Sections 3 and 8. The proof's global step additionally requires the two-tail bounds, which are supplied in Sections 5 and 6. Numerical checks are not premises of any theorem. Exact dependency hashes, checks, prior exposure, and review status are recorded separately.
