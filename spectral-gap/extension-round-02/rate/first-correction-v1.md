# The signed first correction on the square-root scale

Frozen revision: 1. Follow-up to task SG-E1. Written November 14, 2026 Pacific.

Mathematical status: proved below, awaiting independent review. The accepted partition proof and the separately frozen explicit-rate proof were available. No new saddle or integrator attempt was read before this proof was frozen. No historical priority claim is made.

## 1. Statement and consequence for the rate

Let $a_k(N)$ be the centered diagonal moment of a uniform permutation matrix, and retain the known leading coefficients

$$
\widetilde a_{2m}=(2m-1)!!N^{-3m},
\qquad
\widetilde a_{2m+1}=\frac{4m}{3}(2m+1)!!N^{-3m-2}.
$$

Put $R_k=a_k/\widetilde a_k$, and define

$$
\epsilon=k\bmod2,\qquad m=\lfloor k/2\rfloor,\qquad K=2m,
\qquad\lambda=\frac23\sqrt{K^3/N},
$$

$$
H_k=
\begin{cases}
\cosh\lambda,&\epsilon=0,\\
\sinh\lambda/\lambda,&\epsilon=1,
\end{cases}
\qquad
W_{N,k}=\frac{R_k}{\exp(k^2/(4N))H_k}.
$$

**Theorem CORR-1.** For every sequence of integer orders with $k/\sqrt N\to c\in(0,\infty)$,

$$
\boxed{
W_{N,k}-1
=\frac{2\epsilon-1}{2}\sqrt{\frac KN}
+\frac{2K^{5/2}}{15N^{3/2}}
+o(N^{-1/4}).
}
\tag{1}
$$

The displayed formula allows either parity at each $N$. In particular, along a fixed parity,

$$
\boxed{
N^{1/4}(W_{N,k}-1)
\longrightarrow
\frac{2\epsilon-1}{2}\sqrt c+\frac{2}{15}c^{5/2}.
}
\tag{2}
$$

At $c=1$, the even limit is $-11/30$, and the odd limit is $19/30$. Therefore the uniform $O_C(N^{-1/4})$ rate in RATE-1 cannot be replaced by $o(N^{-1/4})$ on any fixed bounded square-root range containing $k\sim\sqrt N$.

More precisely, for every $C\ge1$, choosing the largest odd integer $k\le\sqrt N$ gives

$$
\liminf_{N\to\infty}N^{1/4}
\sup_{2\le j\le C\sqrt N}|W_{N,j}-1|
\ge\frac{19}{30}.
\tag{3}
$$

The odd coefficient in (2) is positive for every $c>0$. The even coefficient vanishes at $c=\sqrt{15}/2$. No improved rate at that exceptional even scale is asserted here.

## 2. Exact representation and asymptotic bookkeeping

Write

$$
\delta=\frac{K^2}{N},\qquad
\eta=\frac{3K^2}{4N},\qquad
\theta=\frac{4K^{5/2}}{5N^{3/2}},\qquad a=\frac32.
$$

The accepted positive partition representation gives

$$
Q_k=(N)_kN^ka_k
=k!\sum_{\sum_{j\ge2}jc_j=k}
\prod_{j\ge2}\frac{(N(j-1)/j)^{c_j}}{c_j!}.
\tag{4}
$$

Define $\mathcal L_k$ as in the rate proof, so that $R_k=D_kQ_k/\mathcal L_k$ with $D_k=N^k/(N)_k$. If $x=\sqrt{K/N}$, the effective weight of a block of size $j\ge3$ is

$$
\lambda_j=N\frac{j-1}{j}x^j.
$$

Thus $\lambda_3=\lambda$, $\lambda_4=\eta$, and $\lambda_5=\theta$.

Under the hypothesis of CORR-1,

$$
\delta\to c^2,\qquad \eta\to3c^2/4,
\qquad \lambda\asymp N^{1/4},\qquad m\asymp\lambda^2.
\tag{5}
$$

In particular, errors $o(\lambda^{-1})$ are the same as errors $o(N^{-1/4})$. All bounds below hold along the selected sequence, with constants depending only on a compact positive range containing $k/\sqrt N$ eventually.

For blocks of sizes two, three and four, let $J$ be Poisson of mean $\lambda$ conditioned on parity $\epsilon$, and let $L$ be independent Poisson of mean $\eta$. Put

$$
h=2L-a\epsilon,\qquad s=aJ+h.
$$

This $s$ is an integer. Set

$$
w_\epsilon(s)=(m-\epsilon)_s/m^s
$$

when $0\le s\le m-\epsilon$, and set it to zero otherwise. The contribution of these block sizes to $(Q_k/\mathcal L_k)/H_k$ is exactly

$$
e^\eta\mathbb E w_\epsilon(s).
\tag{6}
$$

The known recurrence and leading coefficients underlying (4) are attributed in the accepted base proof. The present proof uses that exact identity, not a new special-function asymptotic assumption.

## 3. Conditioned Poisson fluctuations

Let $Z=J-\lambda$. Since $\lambda\to\infty$, either parity conditioning has probability tending to $1/2$. The exact conditional first two moments give

$$
\mathbb EZ=O(\lambda e^{-2\lambda}),\qquad
\mathbb EZ^2=\lambda+O(\lambda^2e^{-2\lambda}).
\tag{7}
$$

Indeed, $\mathbb EJ=\lambda\tanh\lambda$ in the even case and $\lambda\coth\lambda$ in the odd case. In either case, $\mathbb EJ^2=\lambda^2+\mathbb EJ$.

The unconditioned fourth and sixth central Poisson moments are $3\lambda^2+\lambda$ and $15\lambda^3+25\lambda^2+\lambda$. Dividing their nonnegative restricted expectations by a parity probability bounded below proves

$$
\mathbb EZ^4=O(\lambda^2),\qquad
\mathbb EZ^6=O(\lambda^3),\qquad
\mathbb E|Z|^3=O(\lambda^{3/2}).
\tag{8}
$$

These elementary formulas can also be read off from $\exp(\lambda(e^z-1-z))$. Every fixed moment of $h$ is bounded because $\eta$ stays bounded. Every fixed raw moment of $s$ is $O(\lambda^r)$ at order $r$.

## 4. Expand the quadratic depletion exponent

Define

$$
A=\frac{s(s-1+2\epsilon)}{2m},
\qquad
\delta=\frac{a^2\lambda^2}{2m}=\frac{9\lambda^2}{8m}.
$$

Direct expansion, using (7) and $\mathbb Eh=2\eta-a\epsilon$, gives

$$
\begin{aligned}
\mathbb EA-\delta
&=\left(\frac{a^2-a}{2}+(a-a^2)\epsilon+2a\eta\right)\frac\lambda m
+O(m^{-1})+O(\lambda^2e^{-2\lambda}/m)\\
&=\left(3\eta+\frac38(1-2\epsilon)\right)\frac\lambda m
+o(\lambda^{-1}).
\end{aligned}
\tag{9}
$$

For the second moment, isolate the leading fluctuation:

$$
A-\delta=\frac{a^2\lambda}{m}Z+V,
$$

where

$$
V=\frac{a^2Z^2}{2m}
+\frac{aJh}{m}+\frac{h^2}{2m}
+\frac{(2\epsilon-1)(aJ+h)}{2m}.
$$

Equations (7), (8), and bounded moments of $h$ imply

$$
\mathbb EV^2=O(\lambda^2/m^2)=O(\lambda^{-2}).
$$

The leading term has second moment $a^4\lambda^3/m^2+o(\lambda^{-1})$. Its covariance with $V$ is $O(\lambda^{-3/2})$ by Cauchy-Schwarz. Therefore

$$
\mathbb E(A-\delta)^2
=\frac{a^4\lambda^3}{m^2}+o(\lambda^{-1}).
\tag{10}
$$

Likewise, (8) and the displayed expression for $V$ give

$$
\mathbb E|A-\delta|^3=O(\lambda^{-3/2})=o(\lambda^{-1}).
\tag{11}
$$

Both $A$ and $\delta$ are nonnegative. Taylor's theorem for $e^{-u}$, whose third derivative has absolute value at most one for $u\ge0$, now yields

$$
\mathbb Ee^{-A}
=e^{-\delta}\left[
1-\left(3\eta+\frac38(1-2\epsilon)\right)\frac\lambda m
+\frac{a^4\lambda^3}{2m^2}
\right]+o(\lambda^{-1}).
\tag{12}
$$

## 5. Retain the cubic term in the availability product

On the event $s\le m/2$, the logarithm of the exact product satisfies

$$
\log w_\epsilon(s)
=-A-\frac{s^3}{6m^2}
+O\left(\frac{s^2}{m^2}+\frac{s^4}{m^3}\right).
\tag{13}
$$

To verify this, sum the expansion

$$
\log(1-u)=-u-u^2/2+O(u^3),\qquad0\le u\le1/2,
$$

over $u=r/m$ for $r=\epsilon,\ldots,s-1+\epsilon$. The linear sum is exactly $A$, and the quadratic sum is $s^3/(6m^2)+O(s^2/m^2)$.

The complement of this event has probability $O(\lambda^{-4})$, using the fourth raw moment of $s$ and $m\asymp\lambda^2$. Its contribution to expectations of the bounded factors $w_\epsilon(s)$ and $e^{-A}$ is negligible. Its contribution to $s^3/m^2$ is $O(\lambda^{-3})$, by Cauchy-Schwarz and the sixth raw moment.

On the retained event, write the nonnegative nonlinear logarithm remainder as $B=-\log w_\epsilon(s)-A$. It satisfies $B=O(s^3/m^2)$. The inequality

$$
|e^{-B}-1+B|\le B^2/2
$$

and (13) show, after taking expectations,

$$
\mathbb Ew_\epsilon(s)
=\mathbb Ee^{-A}-\frac1{6m^2}\mathbb E(e^{-A}s^3)+O(\lambda^{-2}).
\tag{14}
$$

Here the three remainder expectations have orders

$$
\frac{\mathbb Es^2}{m^2}=O(\lambda^{-2}),\qquad
\frac{\mathbb Es^4}{m^3}=O(\lambda^{-2}),\qquad
\frac{\mathbb Es^6}{m^4}=O(\lambda^{-2}).
$$

Finally, $\mathbb Es^3=a^3\lambda^3+O(\lambda^2)$, and Cauchy-Schwarz gives

$$
\mathbb E\left[|e^{-A}-e^{-\delta}|s^3\right]
\le\sqrt{\mathbb E(A-\delta)^2}\sqrt{\mathbb Es^6}
=O(\lambda^{5/2}).
$$

Consequently,

$$
\frac1{6m^2}\mathbb E(e^{-A}s^3)
=e^{-\delta}\frac{a^3\lambda^3}{6m^2}+o(\lambda^{-1}).
$$

Combining this with (12) and (14), and using $a=3/2$, proves

$$
\boxed{
\mathbb Ew_\epsilon(s)
=e^{-\delta}\left[
1+\left(\frac38(2\epsilon-1)-3\eta\right)\frac\lambda m
+\frac{63\lambda^3}{32m^2}
\right]+o(\lambda^{-1}).
}
\tag{15}
$$

The coefficient $63/32$ is $a^4/2-a^3/6$. Its two terms come respectively from fluctuations of the quadratic depletion and from the cubic logarithm term.

## 6. Isolate exactly one five-element block

The total effective weight of blocks of size at least six satisfies

$$
\sum_{j\ge6}\lambda_j
\le\frac{Nx^6}{1-x}
=O(N^{-1/2})=O(\lambda^{-2}).
\tag{16}
$$

Also $\theta=O(\lambda^{-1})$, so configurations with two or more five-element blocks have aggregate effective weight $O(\lambda^{-2})$. To justify these statements after normalization, remove their availability factors and sum all remaining triple weights without a parity restriction. The normalization ratios $e^\lambda/\cosh\lambda$ and $e^\lambda/\sinh\lambda$ stay bounded. The four-block factor is $e^\eta=O(1)$. Thus the omitted normalized contribution is still $O(\lambda^{-2})$.

For exactly one five-element block and no larger blocks, the triple count has parity $1-\epsilon$. Its availability index is

$$
s_5=aJ+2L+\frac52-a\epsilon.
$$

The exact contribution to $(Q_k/\mathcal L_k)/H_k$ is

$$
\theta e^\eta
\frac{Z_{1-\epsilon}(\lambda)}{Z_\epsilon(\lambda)}
\mathbb E w_\epsilon(s_5),
\tag{17}
$$

where $Z_0=\cosh$, $Z_1=\sinh$, and $J$ in this expectation has the opposite parity. The ratio of the two normalizers tends to one exponentially fast.

Since $s_5=a\lambda+O_{\mathbb P}(\sqrt\lambda)$, its availability logarithm tends in probability to $-\delta$. The same truncation argument as in Section 5, or the first-order logarithm expansion and boundedness of $w_\epsilon$, gives

$$
\mathbb E w_\epsilon(s_5)=e^{-\delta}+o(1).
$$

Therefore (17) is $\theta e^{\eta-\delta}+o(\lambda^{-1})$. Equations (6), (15), and (16) now give

$$
\frac{Q_k/\mathcal L_k}{H_k}
=e^{\eta-\delta}\left[
1+\left(\frac38(2\epsilon-1)-3\eta\right)\frac\lambda m
+\frac{63\lambda^3}{32m^2}+\theta
\right]+o(\lambda^{-1}).
\tag{18}
$$

## 7. Restore the exact normalization and simplify

The denominator calculation from the rate proof gives

$$
D_k\exp\left(-\frac{k^2+K^2}{4N}\right)
=1+O(N^{-1/2}).
\tag{19}
$$

Since $\eta-\delta=-K^2/(4N)$ and $N^{-1/2}=o(\lambda^{-1})$, restoring $D_k$ in (18) does not change its first correction. Hence

$$
W_{N,k}-1
=\left(\frac38(2\epsilon-1)-3\eta\right)\frac\lambda m
+\frac{63\lambda^3}{32m^2}+\theta
+o(N^{-1/4}).
\tag{20}
$$

The exact parameter identities are

$$
\frac\lambda m=\frac43\sqrt{K/N},\qquad
\eta=\frac{3K^2}{4N},\qquad
\frac{\lambda^3}{m^2}=\frac{32K^{5/2}}{27N^{3/2}},\qquad
\theta=\frac{4K^{5/2}}{5N^{3/2}}.
$$

The coefficient of $K^{5/2}/N^{3/2}$ in (20) is

$$
-3+\frac73+\frac45=\frac2{15}.
$$

Its parity term is $(2\epsilon-1)\sqrt{K/N}/2$. This proves (1), and $K/\sqrt N\to c$ proves (2).

For (3), choose the largest odd integer no greater than $\sqrt N$. Its ratio to $\sqrt N$ tends to one, and the positive odd limit in (2) is $19/30$. It is an allowed order for every $C\ge1$ and all sufficiently large $N$.

## 8. Worked boundary and scope

Take $N=(2m)^2$ and $k=2m$. Then $k/\sqrt N=1$, and the corrected approximation has a negative first relative error with scaled limit $-11/30$.

Take $N=(2m+1)^2$ and $k=2m+1$. The same scale has positive first relative error with scaled limit $19/30$. These two sequences give a direct parity explanation and a concrete obstruction to improving the uniform order in RATE-1.

The four contributions before simplification are the finite shift in available pairs, the interaction of triples with four-blocks, fluctuations and the cubic term in pair depletion, and one five-element block. Neglecting the compulsory odd triple loses the parity term.

The proof establishes the signed first correction for positive limiting square-root scale. It does not claim a further expansion at the exceptional even value $c=\sqrt{15}/2$, or an approximation for unbounded $k/\sqrt N$. The underlying moment identities remain attributed to their sources in the accepted manuscript. A separate finite script and results file corroborate the algebra and examples. Independent review is required before promotion.
