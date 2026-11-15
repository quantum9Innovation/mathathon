# Explicit constants for the critical-scale comparison

Frozen revision: 1. This is an optional strengthening of the residual and stability estimates in `inputs/critical-scale-v1.md`, whose uniform theorem otherwise stands unchanged. It is proposed for independent review. It supplies a numerical formula for the existence constant, rather than a tighter rate.

## 1. Statement

Set $\alpha=32/9$ and, for $T>0$, define

$$K_T=\left(2+6\alpha+\frac32\alpha^2T\right)e^{\sqrt{\alpha T}},$$

$$C_T=81(1+T)K_Te^{16T}.$$

This $C_T$ is valid in both (C1) and (C2) of the frozen critical-scale theorem. The hypotheses remain $M\ge1$, $N\ge4M+2$, and $M^3/N\le T$.

## 2. Derivative bounds without unspecified constants

Define the entire functions

$$f(t)=\cosh\sqrt{\alpha t},\qquad
 g(t)=\frac{\sinh\sqrt{\alpha t}}{\sqrt{\alpha t}},\qquad g(0)=1.$$

Their power series have nonnegative coefficients. For $0\le t\le T$, coefficient comparison gives

$$0\le f(t),g(t)\le e^{\sqrt{\alpha T}},$$

$$0\le f'(t),g'(t)\le\frac\alpha2e^{\sqrt{\alpha T}},$$

$$0\le f''(t),g''(t)\le\frac{\alpha^2}{12}e^{\sqrt{\alpha T}}.$$

For the second derivative, use

$$\frac{\ell(\ell-1)}{(2\ell)!}\le\frac1{12(2\ell-4)!}\qquad(\ell\ge2).$$

For the first derivative, use $\ell/(2\ell)!\le1/[2(2\ell-2)!]$. The series for $g$ has larger factorial denominators, so the same bounds apply. Also $0\le f(t)-g(t)\le f(t)-1\le(\alpha/2)e^{\sqrt{\alpha T}}t$.

Put $E(x)=f(x^3/N)$ and $O(x)=g(x^3/N)$. The chain rule gives

$$|E(x)|+|O(x)|\le K_T,$$

$$|E(x)-O(x)|\le K_Tx^3/N,$$

$$|E'(x)|+|O'(x)|\le K_Tx^2/N,$$

$$|E''(x)|+|O''(x)|\le K_Tx/N,$$

whenever $x^3/N\le T$. Indeed, the final derivative sum is at most

$$\left(6\alpha+\frac32\alpha^2T\right)e^{\sqrt{\alpha T}}\frac xN.$$

All four bounds include $x=0$ by continuity.

## 3. Explicit local residuals

Use the exact coefficients $A_m,B_m,C_m,D_m$ and comparison equations from (C5) through (C8) of the frozen proof. Taylor's theorem gives the backward-difference error at most $K_Tm/(2N)$ for each comparison function. Let $b_m=16m^2/(3N)$. Direct subtraction gives

$$A_m-1\le4m/N,$$

$$|B_m-b_m|\le\left(16+\frac{64}3T\right)m/N.$$

For the second inequality, put $D=N-2m+1\ge N/2$. The numerator of $B_m-b_m$, over denominator $3DN$, is

$$(-24m+8)N+32m^3-16m^2.$$

Its absolute value is at most $24mN+32m^3$, and $m^3/N\le T$. The even residual decomposition in (C10) therefore yields

$$|\rho_m^E|\le K_T\left(\frac{41}2+\frac{80}3T\right)\frac mN.$$

Here the term $b_m(O_m-O_{m-1})$ is at most $(16/3)K_TT m/N$.

For the odd residual, write $C_m=t_mc_m$ and $D_m=t_md_m$, with

$$t_m=\frac N{N-2m},\quad c_m=\frac3{2m+1},\quad d_m=\frac{2m-2}{2m+1}.$$

Removing $t_m$ costs at most $4K_Tm/N$. The backward-difference error costs at most $K_Tm/(2N)$. The remaining coefficient is exactly

$$\frac{3d_m}{2m}-c_m=-\frac3{m(2m+1)},$$

and hence its contribution is at most $(3/2)K_Tm/N$. Thus

$$|\rho_m^O|\le6K_Tm/N.$$

Combining these bounds gives

$$|\rho_m^E|+|\rho_m^O|
\le27(1+T)K_Tm/N.$$

This holds at $m=1$ as well.

## 4. Stability and conclusion

The exact recurrence has nonnegative coefficients and satisfies

$$A_m+B_m\le1+12m^2/N,\qquad C_m+D_m\le1+4m^2/N,\qquad C_m\le2.$$

After substituting the even error into the odd error, one may therefore use

$$H_m\le(1+12m^2/N)(1+4m^2/N)H_{m-1}
+81(1+T)K_Tm/N,$$

where $H_0=0$ and $H_m$ is the maximum of the even and odd errors. Since $\sum_{m=1}^M m^2\le M^3$ and $\sum_{m=1}^M m\le M^2$, iteration gives

$$\max_{m\le M}H_m\le81(1+T)K_Te^{16T}\frac{M^2}{N}.$$

This proves the stated explicit choice of $C_T$. It is deliberately generous. A small constant is unnecessary for the asymptotic transition.
