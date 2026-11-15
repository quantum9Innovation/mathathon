# Critical-scale limits for centered permutation moments

Frozen revision: 1. Mathematical status: proved by the argument below, awaiting independent review. This is a separate extension of `sharp-scaling-v2.md`. It does not change the already reviewed cubic-threshold theorem. The bounded investigation for this extension ends on November 15, 2026, at 01:30 UTC.

The exact recurrence and leading terms are due to Collins and Nagatsu, *Weingarten calculus for centered random permutation matrices*, Proposition 3.3, published [PDF](https://alco.centre-mersenne.org/item/10.5802/alco.480.pdf). Published PDF SHA256: `c5b124655a495c03017b3866542ebd1f3289921cc4ed053244cc885cb8db017e`. The normalized recurrences are also in their proof. No priority claim for the critical-scale formulas has been established by a comprehensive literature search.

## 1. Statement

For a uniform permutation matrix of size $N$, define

$$a_k(N)=\mathbb E\prod_{i=1}^k(M_{ii}-1/N).$$

Normalize by the known leading terms

$$R_{2m}(N)=\frac{a_{2m}(N)}{(2m-1)!!N^{-3m}},$$

$$R_{2m+1}(N)=\frac{a_{2m+1}(N)}{(4m/3)(2m+1)!!N^{-3m-2}},\qquad m\ge1.$$

For every fixed $T>0$, there is a finite constant $C_T$ such that, whenever $M\ge1$, $N\ge4M+2$, and $M^3/N\le T$,

$$\max_{1\le m\le M}
\left|R_{2m}(N)-\cosh\left(\frac{4\sqrt2}{3}\sqrt{m^3/N}\right)\right|
\le C_T\frac{M^2}{N},\tag{C1}$$

and

$$\max_{1\le m\le M}
\left|R_{2m+1}(N)-
\frac{\sinh\left(\frac{4\sqrt2}{3}\sqrt{m^3/N}\right)}
{\frac{4\sqrt2}{3}\sqrt{m^3/N}}\right|
\le C_T\frac{M^2}{N}.\tag{C2}$$

Consequently, if $k_N^3/N\to c\in[0,\infty)$, then along even orders

$$R_{k_N}(N)\longrightarrow\cosh\left(\frac23\sqrt c\right),\tag{C3}$$

while along odd orders at least 3,

$$R_{k_N}(N)\longrightarrow
\frac{\sinh\left(\frac23\sqrt c\right)}{\frac23\sqrt c}.\tag{C4}$$

The last expression is interpreted as 1 when $c=0$. A sequence with both parities need not have one common limit when $c>0$.

## 2. Exact recurrence for the two parities

Write $e_m=R_{2m}$ and $o_m=R_{2m+1}$. Use the auxiliary seeds $e_0=o_0=1$. The value of $o_0$ is immaterial, since its coefficients in both first-step equations are zero.

The known moment recurrence gives, for $1\le m\le M$,

$$e_m=A_m e_{m-1}+B_m o_{m-1},\tag{C5}$$

$$o_m=C_m e_m+D_m o_{m-1},\tag{C6}$$

where

$$A_m=\frac{N}{N-2m+1},\qquad
B_m=\frac{4(2m-1)(2m-2)}{3(N-2m+1)},$$

$$C_m=\frac{3N}{(N-2m)(2m+1)},\qquad
D_m=\frac{(2m-2)N}{(N-2m)(2m+1)}.$$

At $m=1$, these reproduce $R_2=N/(N-1)$ and $R_3=N^2/((N-1)(N-2))$.

All coefficients are nonnegative. Under $N\ge4M+2$, they satisfy

$$A_m+B_m\le1+12m^2/N,\qquad
C_m+D_m\le1+4m^2/N,\qquad C_m\le2.\tag{C7}$$

For the first bound, the exact excess is

$$A_m+B_m-1=
\frac{(2m-1)(8m-5)}{3(N-2m+1)}
\le\frac{32m^2}{3N}.$$

For the second, $C_m+D_m=N/(N-2m)$ and its excess is at most $4m/N\le4m^2/N$.

## 3. Continuous comparison functions

For real $x\ge0$, put

$$z_N(x)=\frac{4\sqrt2}{3}\sqrt{x^3/N},\qquad
E_N(x)=\cosh z_N(x),\qquad
O_N(x)=\frac{\sinh z_N(x)}{z_N(x)},$$

with $O_N(0)=1$. Direct differentiation gives

$$E_N'(x)=\frac{16x^2}{3N}O_N(x),\qquad
O_N'(x)=\frac{3}{2x}(E_N(x)-O_N(x)),\tag{C8}$$

where the second identity extends continuously to zero.

For $x^3/N\le T$, power series give bounds with a constant depending only on $T$:

$$|E_N(x)|+|O_N(x)|\le K_T,$$

$$|E_N(x)-O_N(x)|\le K_T x^3/N,$$

$$|E_N'(x)|+|O_N'(x)|\le K_T x^2/N,$$

$$|E_N''(x)|+|O_N''(x)|\le K_T x/N.\tag{C9}$$

For completeness, the two power series have terms $(\alpha x^3/N)^\ell/(2\ell)!$ and $(\alpha x^3/N)^\ell/(2\ell+1)!$, where $\alpha=32/9$. After one derivative, factor out $x^2/N$. After two derivatives, factor out $x/N$. The remaining series are uniformly bounded when $x^3/N\le T$. The difference starts at order $x^3/N$. This proves every bound in (C9), including at zero.

## 4. The local residuals are summable

Write $E_m=E_N(m)$ and $O_m=O_N(m)$. Define the residuals of the exact discrete equations by

$$\rho_m^E=E_m-A_mE_{m-1}-B_mO_{m-1},$$

$$\rho_m^O=O_m-C_mE_m-D_mO_{m-1}.$$

We claim that

$$|\rho_m^E|+|\rho_m^O|\le K'_T m/N.\tag{C10}$$

By Taylor's theorem and (C9), each backward difference differs from its derivative at $m$ by at most $K_Tm/N$. Set $b_m=16m^2/(3N)$. The coefficient formulas give

$$A_m-1=O(m/N),\qquad B_m-b_m=O_T(m/N).\tag{C11}$$

To justify the second bound directly, subtract the fractions and use $N-2m+1\ge N/2$. The error is bounded by a constant times $m/N+m^3/N^2$. Since $m^3/N\le T$ and $m\ge1$, the second term is at most $T m/N$.

Now expand the even residual as

$$\begin{aligned}
\rho_m^E={}&(E_m-E_{m-1}-E_N'(m))\\
&+b_m(O_m-O_{m-1})
-(A_m-1)E_{m-1}-(B_m-b_m)O_{m-1}.
\end{aligned}$$

The first, third, and fourth terms are $O_T(m/N)$. The second is $O_T(m^4/N^2)$, which is also $O_T(m/N)$ because $m^3/N\le T$.

For the odd residual, set

$$c_m=\frac3{2m+1},\qquad d_m=\frac{2m-2}{2m+1},\qquad
t_m=\frac{N}{N-2m}.$$

Thus $c_m+d_m=1$, $C_m=t_mc_m$, $D_m=t_md_m$, and $t_m-1=O(m/N)$. Removing this last factor changes the residual by $O_T(m/N)$. The remaining expression is

$$O_m-c_mE_m-d_mO_{m-1}
=d_m(O_m-O_{m-1})-c_m(E_m-O_m).$$

Insert (C8) and the backward-difference estimate. The coefficient of $E_m-O_m$ becomes

$$d_m\frac3{2m}-c_m=-\frac3{m(2m+1)}.$$

Its contribution is $O_T(m/N)$ by (C9). This proves (C10), including $m=1$.

## 5. Stability of the positive recurrence

Let

$$H_m=\max(|e_m-E_m|,|o_m-O_m|),\qquad H_0=0.$$

Subtracting the comparison equations from (C5) and (C6), using nonnegative coefficients and (C7), yields

$$H_m\le(1+12m^2/N)(1+4m^2/N)H_{m-1}+3K'_Tm/N.\tag{C12}$$

Indeed, first bound the even error, then substitute that bound in the odd recurrence. Its coefficient sum is at most the product in (C12), and $C_m\le2$ bounds the local error contribution.

The accumulated multiplicative factor is at most

$$\prod_{m=1}^M(1+12m^2/N)(1+4m^2/N)
\le\exp\left(\frac{16}{N}\sum_{m=1}^Mm^2\right)
\le e^{16T}.$$

Summing the local errors gives

$$\max_{m\le M}H_m
\le3K'_Te^{16T}\frac{M(M+1)}{2N}
\le3K'_Te^{16T}\frac{M^2}{N}.$$

This proves (C1) and (C2). The proof uses the recurrence and explicit derivative bounds. No numerical convergence is needed.

## 6. Limits and a small-error consequence

If $k_N^3/N$ remains bounded, then its corresponding $m$ is $O(N^{1/3})$, so all hypotheses hold eventually and $m^2/N\to0$. For even $k=2m$, the square of the comparison argument is exactly $4k^3/(9N)$. For odd $k=2m+1$, the difference between $k^3/N$ and $(2m)^3/N$ is $O(m^2/N)$ and tends to zero. Continuity proves (C3) and (C4).

If in addition $k_N\to\infty$ and $k_N^3/N\to0$, the uniform error in (C1) and (C2) is smaller than $k_N^3/N$ by a factor of order $1/k_N$. Expanding the comparison functions therefore gives

$$R_{k_N}-1\sim\frac{2k_N^3}{9N}\quad\text{along even orders},$$

$$R_{k_N}-1\sim\frac{2k_N^3}{27N}\quad\text{along odd orders}.\tag{C13}$$

Thus the constant $2/27$ in the uniform lower bound of `sharp-scaling-v2.md` is asymptotically sharp over growing odd orders in the small-error regime. The finite lower bound itself was already proved without this extension.

## 7. Explanation and boundary

At the critical scale, the even recurrence moves by order $m^2/N$ at each step. The odd recurrence repeatedly averages the current even value with the preceding odd value. Their continuous comparison equations are (C8). Solving this pair produces the hyperbolic cosine and normalized hyperbolic sine. The rigorous step is the residual estimate (C10): the discarded terms add up to only $M^2/N$, which vanishes when $M$ is of order $N^{1/3}$.

For $c=9/4$, the argument is 1. The even ratio tends to $\cosh(1)$, while the odd ratio tends to $\sinh(1)$. These are different and both exceed 1. At $c=0$, both ratios tend to 1. The formulas therefore explain both the cubic transition and its parity dependence.

The estimates here are uniform on bounded ranges of $k^3/N$. They make no assertion about an approximation by the same hyperbolic functions when that quantity diverges. The earlier positive lower bound already establishes divergence of the normalized moment in that regime.
