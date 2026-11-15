# Independent review of the critical-scale limit

Date: 15 November 2026.

Reviewed frozen file: `audit-2026-11-14/critical-scale-v1.md`, SHA-256 `ea79cdd43ae88afcc2ca5008e4c4a95e50e12b37ca87904db25ce7cdad0b5596`.

Verdict: **supported**. The uniform comparison estimates C1 and C2, the parity-dependent limits C3 and C4, and the small-error asymptotics C13 follow from the stated recurrence. No gap was found. The proof was reconstructed without reading another integrator response. The explicit constants below verify uniformity rather than relying on numerical behavior.

## 1. Initialization and recurrence coefficients

Let `e_m=R_(2m)` and `o_m=R_(2m+1)`. Dividing the moment recurrence by the respective leading terms gives exactly C5 and C6. The auxiliary values `e_0=o_0=1` are consistent with the comparison functions at zero. At the first step,

\[
B_1=D_1=0,\quad
A_1=\frac{N}{N-1},\quad
C_1=\frac{N}{N-2}.
\]

Thus

\[
e_1=\frac{N}{N-1},\qquad
o_1=\frac{N^2}{(N-1)(N-2)},
\]

as required. There is no ratio at odd order one in this argument. Its auxiliary placeholder has coefficient zero in both first-step equations.

Under `N>=4M+2`, every denominator used for `m<=M` is at least `N/2`. In particular,

\[
A_m+B_m\ge1,\qquad C_m+D_m\ge1,
\]

\[
A_m+B_m\le1+12m^2/N,
\quad C_m+D_m\le1+4m^2/N,
\quad C_m\le2.
\]

The lower bounds on the coefficient sums are also useful for the stability step. They follow directly from the positive excess formulas in the draft.

## 2. Continuous comparison and the apparent singularity

Set `alpha=32/9` and `u=x^3/N`. The candidate functions are the entire power series

\[
E_N(x)=\sum_{\ell\ge0}\frac{(\alpha u)^\ell}{(2\ell)!},
\qquad
O_N(x)=\sum_{\ell\ge0}\frac{(\alpha u)^\ell}{(2\ell+1)!}.
\]

They give `E_N(0)=O_N(0)=1`. Direct differentiation gives

\[
E_N'(x)=\frac{16x^2}{3N}O_N(x),\qquad
O_N'(x)=\frac{3}{2x}(E_N(x)-O_N(x)).
\]

The second identity has a removable singularity, since the difference on its right is of order `x^3/N`. Both derivatives are of order `x^2/N` at zero. The differential system is therefore not being solved through an uncontrolled singular initial condition. The proof uses these explicitly defined smooth comparison functions.

For a uniform derivative check, write `E_N(x)=f(u)` and `O_N(x)=g(u)`, where the displayed series define entire functions `f,g`. Then

\[
E_N''(x)=\frac{x}{N}\bigl(6f'(u)+9u f''(u)\bigr),
\]

and likewise for `g`. All functions in these expressions, and `(f(u)-g(u))/u` with its value at zero, are bounded on `[0,T]`. Consequently one constant `K_T` supplies all bounds in C9 on the whole interval `[0,M]` when `M^3/N<=T`.

These calculations independently recover the argument `sqrt(32m^3/(9N))`, hence the proposed hyperbolic functions and their constants.

## 3. Uniform residual bounds with explicit constants

Enlarge `K_T` if necessary so that it bounds each expression in C9. On `[m-1,m]`, Taylor's theorem gives, for either comparison function `F`,

\[
|F(m)-F(m-1)-F'(m)|\le\frac{K_Tm}{2N}.
\]

Put `b_m=16m^2/(3N)` and `Q=N-2m+1`. Direct subtraction gives

\[
B_m-b_m
=\frac{(-24m+8)N+16m^2(2m-1)}{3NQ}.
\]

Thus

\[
|A_m-1|\le4m/N,
\]

\[
|B_m-b_m|
\le16m/N+\frac{64m^3}{3N^2}
\le\left(16+\frac{64T}{3}\right)m/N.
\]

Using `E_N'(m)=b_mO_m`, the even residual decomposes exactly as in the draft. Its four terms satisfy

\[
|\rho_m^E|
\le K_T\left(\frac{41}{2}+\frac{80T}{3}\right)\frac mN.
\]

In particular, the term `b_m(O_m-O_(m-1))` is at most `(16K_T/3)m^4/N^2`. It is bounded by `(16T K_T/3)m/N` because `m^3/N<=T`. This is the place where the bounded critical-scale hypothesis controls the accumulated comparison error.

For the odd residual, use

\[
c_m=\frac3{2m+1},\quad
d_m=\frac{2m-2}{2m+1},\quad
t_m=\frac{N}{N-2m}.
\]

Here `c_m+d_m=1`, both coefficients are nonnegative, and `t_m-1<=4m/N`. Removing `t_m` therefore changes the residual by at most `4K_Tm/N`. The remaining expression is

\[
d_m(O_m-O_{m-1})-c_m(E_m-O_m).
\]

After inserting the derivative, the coefficient of `E_m-O_m` is exactly

\[
d_m\frac3{2m}-c_m=-\frac3{m(2m+1)}.
\]

Its absolute contribution is at most `(3K_T/2)m/N`. The Taylor error is at most `K_Tm/(2N)`. Hence

\[
|\rho_m^O|\le6K_Tm/N.
\]

This includes `m=1`, where `d_1=0`. The initial comparison errors do not have to vanish. They are included in these residual bounds, starting from the exact agreement at index zero.

One possible common constant in C10 is therefore

\[
K'_T=27(1+T)K_T.
\]

It depends on `T` alone, not on `m`, `M`, or `N`.

## 4. Stability and accumulation

Let `S_m=A_m+B_m` and `U_m=C_m+D_m`. The even error is bounded by

\[
S_m H_{m-1}+|\rho_m^E|.
\]

Substitution into the odd equation gives the coefficient `C_mS_m+D_m` on `H_(m-1)`. Since `S_m>=1`,

\[
C_mS_m+D_m\le S_m(C_m+D_m)=S_mU_m.
\]

Also `U_m>=1`, so the same product bounds the even coefficient. Finally `C_m<=2` bounds both residual contributions by `3K'_Tm/N`. This proves C12.

The product of all stability factors is bounded by

\[
\exp\left(16N^{-1}\sum_{m=1}^M m^2\right)
\le e^{16T},
\]

because `sum_(m=1)^M m^2<=M^3` for every integer `M>=1`. Summing the local residuals gives

\[
\max_{m\le M}H_m
\le3K'_Te^{16T}\frac{M(M+1)}{2N}
\le3K'_Te^{16T}\frac{M^2}{N}.
\]

For example, `C_T=81(1+T)K_T exp(16T)` is valid. Its size is not optimized. The proof establishes exactly the uniformity claimed in C1 and C2.

## 5. Parity, limiting constants, and sharpness

For `k=2m`, the squared comparison argument is

\[
\frac{32m^3}{9N}=\frac{4k^3}{9N}.
\]

For `k=2m+1`, one instead has `(2m)^3=(k-1)^3`. The difference between `k^3/N` and `(k-1)^3/N` is of order `m^2/N`, which tends to zero when `k^3/N` remains bounded. Thus the limiting arguments in both cases are `(2/3)sqrt(c)`.

Since `m=O(N^(1/3))`, the comparison error `C_Tm^2/N` tends to zero, and `N>=4m+2` holds eventually. This proves C3 and C4, including `c=0` by continuity. For `c>0`, the even and odd limits are different, so a mixed-parity sequence need not converge.

For the stronger claim C13, the additional hypothesis `k_N` tending to infinity is necessary to use the given error estimate. Under this hypothesis and `k_N^3/N` tending to zero,

\[
\frac{m^2/N}{k_N^3/N}=O(1/k_N)\longrightarrow0.
\]

The expansions `cosh(z)-1=z^2/2+O(z^4)` and `sinh(z)/z-1=z^2/6+O(z^4)` therefore imply the stated coefficients `2/9` and `2/27`.

To make optimality of the global lower-bound constant explicit, take `N=m^4` and `k=2m+1`, with `m` tending to infinity. These are admissible odd orders, `k^3/N` tends to zero, and C13 gives

\[
\frac{R_k(N)-1}{k^3/N}\longrightarrow\frac2{27}.
\]

Thus any proposed uniform lower bound with a strictly larger constant fails along this sequence. The draft correctly limits this optimality argument to growing orders. It does not infer it merely from the fixed positive critical-scale limits.

## 6. Independent numerical corroboration

A separate standard-library calculation used 65-digit decimal arithmetic, a 60-second execution limit, and a 256 MiB memory limit. It directly iterated C5 and C6 and evaluated the two comparison functions. It inspected 21 cases with `M` in `{1,2,5,10,50,200,1000}` and target values of `M^3/N` in `{0.01,1,8}`, increasing `N` to `4M+2` whenever required. The first-step values were separately checked against their exact formulas.

The rescaled local residuals and global errors stayed bounded in each tested range. These observations corroborate the symbolic estimates above and do not establish their uniformity by themselves.

Along `N=m^4`, the independently computed ratios `(R_k-1)N/k^3` were:

| m | Even order `2m` | Odd order `2m+1` |
|---:|---:|---:|
| 10 | 0.2254531664 | 0.0828104904 |
| 50 | 0.2227364677 | 0.0757397272 |
| 200 | 0.2223450062 | 0.0744879166 |
| 1000 | 0.2222464749 | 0.0741567177 |

They approach `2/9` and `2/27`, respectively. No existing verification script was read or invoked.

## Scope of acceptance

The mathematical claims in this frozen revision are supported. The proof is uniform for bounded `k^3/N`, handles the initial step, and yields the stated optimal lower-bound constant. It makes no assertion that the same approximation remains valid for unbounded `k^3/N`. Literature priority of the critical-scale formulas is outside this review.
