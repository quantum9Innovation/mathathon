# An explicit rate for the corrected square-root approximation

Frozen revision: 1. Task SG-E1. Written November 14, 2026 Pacific.

Mathematical status: proved below, awaiting independent review. This investigation had prior exposure to its own accepted base proof, `../../manuscript-round-01/extensions/hyperbolic-window-v1.md`, and the accepted manuscript revision 5. No new saddle or integrator attempt was read before freezing this proof.

## 1. Exact statement

Use the accepted notation

$$
a_k(N)=\mathbb E\prod_{i=1}^k(M_{ii}-1/N),
$$

where $M$ is a uniform permutation matrix of size $N$. For $m\ge1$, set

$$
\widetilde a_{2m}=(2m-1)!!N^{-3m},
\qquad
\widetilde a_{2m+1}=\frac{4m}{3}(2m+1)!!N^{-3m-2},
\qquad R_k=\frac{a_k}{\widetilde a_k}.
$$

For an integer $k\ge2$, define

$$
m=\lfloor k/2\rfloor,\qquad K=2m,\qquad
\lambda=\frac23\sqrt{K^3/N},\qquad
\eta=\frac{3K^2}{4N},\qquad \delta=\frac{K^2}{N},
$$

and retain the exact parity normalization

$$
H_k=
\begin{cases}
\cosh\lambda,&k\text{ even},\\
\sinh\lambda/\lambda,&k\text{ odd}.
\end{cases}
$$

In particular, the cube in the odd comparison uses $K=k-1$. Write

$$
W_{N,k}=\frac{R_k}{\exp(k^2/(4N))H_k}.
$$

**Theorem RATE-1.** Fix any real $C\ge1$. For integers $N\ge16C^2$ and $2\le k\le C\sqrt N$,

$$
\boxed{
|W_{N,k}-1|
\le A_1(C)N^{-1/4}+A_2(C)N^{-1/2}+A_3(C)N^{-1}.
}
\tag{1}
$$

The constants are fully explicit. Put $a=3C^2/4$ and define

$$
\begin{aligned}
B_1(C)&=\frac43(2+3a)\sqrt C+\frac{2144}{27}C^{5/2},\\
B_2(C)&=\frac32(2a+3)C
+\frac{16}{9}(245+45a+45a^2)C,\\
B_3(C)&=3(10a^3+188a^2+457a+141).
\end{aligned}
\tag{2}
$$

Then one valid choice is

$$
\begin{aligned}
A_1(C)&=e^{7C^2/4}B_1(C)+2e^{11C^2/4}C^{5/2},\\
A_2(C)&=e^{7C^2/4}B_2(C)+2e^{11C^2/4}C
+e^{C^2/3}\left(\frac C2+\frac{C^3}{3}\right),\\
A_3(C)&=e^{7C^2/4}B_3(C).
\end{aligned}
\tag{3}
$$

These constants are conservative. Equation (1) supplies an explicit $O_C(N^{-1/4})$ rate on the entire bounded square-root range, including fixed orders and the odd small-$\lambda$ case. The accepted base proof supplied convergence without a rate on this range.

The proof also gives a usually more informative finite bound depending on $k$ rather than a common upper endpoint. For any integers $2\le k\le N/4$, put

$$
b=\min(\lambda,\lambda^2),\qquad
D_k=\frac{N^k}{(N)_k},\qquad
r=\frac{k}{2N}+\frac{k^3}{3N^2},
$$

$$
\tau=\frac{2K^{5/2}}{N^{3/2}},\qquad
\zeta=\frac{2K}{N},
$$

and

$$
\begin{aligned}
\mathcal B={}&\frac{(2+3\eta)b+2\eta^2+3\eta}{m}\\
&+\frac{67\lambda^3+(245+45\eta+45\eta^2)\lambda^2
+10\eta^4+188\eta^3+457\eta^2+141\eta}{m^2}.
\end{aligned}
\tag{4}
$$

Here $(N)_k$ is the falling factorial. The finite assertion is

$$
\boxed{
|W_{N,k}-1|
\le e^r-1
+D_k e^{-k^2/(4N)+\eta}
\left[\mathcal B+(1+\zeta)e^\tau-1\right].
}
\tag{5}
$$

Both (1) and (5) are proved inequalities, rather than estimates inferred from numerical convergence.

## 2. Positive partition input and exact parity conditioning

The accepted base proof establishes

$$
Q_k=(N)_kN^ka_k
=k!\sum_{\sum_{j\ge2}jc_j=k}
\prod_{j\ge2}\frac{(N(j-1)/j)^{c_j}}{c_j!},
\tag{6}
$$

and $R_k=D_kQ_k/\mathcal L_k$, where

$$
\mathcal L_{2m}=(2m-1)!!N^m,
\qquad
\mathcal L_{2m+1}=\frac{4m}{3}(2m+1)!!N^m.
$$

The recurrence and the leading terms underlying (6) are known results of Collins and Nagatsu. The generating function in the base proof is a classical Laguerre reformulation. No new historical claim about these identities is made here.

Set $\epsilon=0$ when $k$ is even and $\epsilon=1$ when $k$ is odd. Let $J$ have the Poisson distribution of mean $\lambda$, conditioned to be even when $\epsilon=0$ and odd when $\epsilon=1$. Independently, let $L$ be Poisson of mean $\eta$. Define

$$
t=J-\epsilon,\qquad s=\frac32t+2L.
\tag{7}
$$

Both $t$ and $s$ are nonnegative integers. Define the pair availability factor

$$
w_\epsilon(s)=
\begin{cases}
(m-\epsilon)_s/m^s,&0\le s\le m-\epsilon,\\
0,&s>m-\epsilon.
\end{cases}
\tag{8}
$$

Restrict (6) to blocks of sizes two, three and four. Its contribution to $(Q_k/\mathcal L_k)/H_k$ is exactly

$$
e^\eta\mathbb E w_\epsilon(s).
\tag{9}
$$

This is a finite coefficient identity written as an expectation. For even orders the triple weights are normalized by $\cosh\lambda$. For odd orders the factor $1/\lambda$ in the accepted partition formula cancels the same factor in $H_k$, leaving normalization by $\sinh\lambda$. Therefore (9) does not require $\lambda$ to be bounded away from zero.

## 3. Uniform moment bounds for the conditioned triple count

We will use four elementary bounds that hold for every $\lambda>0$ and either parity:

$$
\mathbb Et\le b,\qquad
|\mathbb Et^2-\lambda^2|\le b,\qquad
\mathbb Et^2\le2\lambda^2,
\tag{10}
$$

$$
\mathbb Et^3\le\lambda^3+4\lambda^2,
\qquad
\mathbb E(t^2-\lambda^2)^2\le4\lambda^3+8\lambda^2.
\tag{11}
$$

For even $J$, differentiation of $\cosh\lambda$ gives

$$
\mathbb EJ=\lambda\tanh\lambda,
\qquad
\mathbb EJ^2=\lambda^2+\lambda\tanh\lambda,
$$

$$
\mathbb EJ^3=\lambda^3\tanh\lambda+3\lambda^2+\lambda\tanh\lambda,
$$

$$
\mathbb E(J^2-\lambda^2)^2
=4\lambda^3\tanh\lambda+7\lambda^2+\lambda\tanh\lambda.
$$

These imply (10) and (11), since $\lambda\tanh\lambda\le\min(\lambda,\lambda^2)$.

For odd $J$, put $q=\lambda\coth\lambda-1$. Direct differentiation of $\sinh\lambda$, followed by $t=J-1$, gives

$$
\mathbb Et=q,\qquad
\mathbb Et^2=\lambda^2-q,
\qquad
\mathbb Et^3=\lambda^2+\lambda^2q+q,
$$

$$
\mathbb E(t^2-\lambda^2)^2
=3\lambda^2+(4\lambda^2-1)q.
$$

Here $0\le q\le\min(\lambda,\lambda^2)$. The first upper bound follows from $\coth\lambda\le1+1/\lambda$. For the second, the function

$$
(1+\lambda^2)\sinh\lambda-\lambda\cosh\lambda
$$

is zero at zero and has nonnegative derivative $\lambda^2\cosh\lambda+\lambda\sinh\lambda$. This proves the claimed bound on $q$ and hence (10) and (11), including the small-$\lambda$ regime.

## 4. Quantitative comparison of pair availability with its exponential

Set

$$
A=\frac{s(s-1+2\epsilon)}{2m}.
\tag{12}
$$

This is nonnegative. For every integer $s\ge0$,

$$
0\le e^{-A}-w_\epsilon(s)\le\frac{4s^3}{m^2}.
\tag{13}
$$

To see this, first suppose $s\le m/2$. Expand the logarithm of the product (8). The sum of its linear terms is $-A$. The remaining absolute contribution is at most $s^3/m^2$, by

$$
0\le-\log(1-u)-u\le\frac{u^2}{2(1-u)}
$$

and $u\le1/2$. The inequality $1-e^{-v}\le v$ proves (13) in this range. If $s>m/2$, the left difference lies in $[0,1]$, including the case where the product is assigned zero. Since $s\ge1$, we have $4s^3/m^2>1$, which proves (13) in the remaining range.

The identity $\delta=9\lambda^2/(8m)$ and (7) give

$$
A-\delta
=\frac{9}{8m}(t^2-\lambda^2)
+\frac3m tL+\frac2mL^2
+(2\epsilon-1)\left(\frac{3}{4m}t+\frac1mL\right).
\tag{14}
$$

Use independence, (10), and the Poisson formulas

$$
\mathbb EL^2=\eta^2+\eta,\quad
\mathbb EL^3=\eta^3+3\eta^2+\eta,\quad
\mathbb EL^4=\eta^4+6\eta^3+7\eta^2+\eta.
$$

Taking the expectation of (14) yields

$$
|\mathbb EA-\delta|
\le\frac{(15/8+3\eta)b+2\eta^2+3\eta}{m}.
\tag{15}
$$

The elementary inequality $(u_1+\cdots+u_5)^2\le5\sum_i u_i^2$, applied to the five terms in (14), together with (10) and (11), gives

$$
\begin{aligned}
\mathbb E(A-\delta)^2\le\frac5{m^2}\bigg[&
\frac{81}{16}\lambda^3
+\left(\frac{45}{4}+18\eta+18\eta^2\right)\lambda^2\\
&+4\eta^4+24\eta^3+29\eta^2+5\eta\bigg].
\end{aligned}
\tag{16}
$$

For completeness, the terms involving $t^2-\lambda^2$, $tL$, $L^2$, $t$, and $L$ contribute before multiplication by $5/m^2$ at most

$$
\frac{81}{64}(4\lambda^3+8\lambda^2),\quad
18\lambda^2(\eta^2+\eta),\quad
4(\eta^4+6\eta^3+7\eta^2+\eta),\quad
\frac98\lambda^2,\quad\eta^2+\eta,
$$

respectively. Their sum is the bracket in (16).

Also, $(u+v)^3\le4(u^3+v^3)$ for nonnegative $u,v$ implies

$$
\mathbb Es^3
\le\frac{27}{2}(\lambda^3+4\lambda^2)
+32(\eta^3+3\eta^2+\eta).
\tag{17}
$$

For nonnegative $A$ and $\delta$, Taylor's theorem and $|(e^{-x})''|\le1$ on $x\ge0$ show

$$
|\mathbb Ee^{-A}-e^{-\delta}|
\le|\mathbb EA-\delta|+\tfrac12\mathbb E(A-\delta)^2.
\tag{18}
$$

Combine (13), (15) through (18). Rounding the resulting positive coefficients upward gives exactly

$$
\boxed{|\mathbb Ew_\epsilon(s)-e^{-\delta}|\le\mathcal B,}
\tag{19}
$$

where $\mathcal B$ is (4). No concentration event or asymptotic approximation has been used in this bound.

## 5. Bound all blocks of size at least five

Assume $k\le N/4$, so $x=\sqrt{K/N}\le1/2$. As in the accepted base proof, put

$$
\lambda_j=N\frac{j-1}{j}x^j.
$$

Let $T_{\rm e}$ and $T_{\rm o}$ be the sums of these weights over even and odd $j\ge5$, respectively. Then

$$
T_{\rm e}+T_{\rm o}
\le\frac{Nx^5}{1-x}
\le\tau,
\qquad
\frac{T_{\rm o}}\lambda
\le\frac{3x^2}{2(1-x^2)}\le\zeta.
\tag{20}
$$

All coefficients in the partition formula are nonnegative. Removing pair availability factors only increases the sum of terms containing at least one block of size at least five. For even orders, this gives the following upper bound on the extra contribution after division by $H_k$:

$$
e^\eta\left[
 e^{T_{\rm e}}\frac{\cosh(\lambda+T_{\rm o})}{\cosh\lambda}-1
\right]
\le e^\eta(e^\tau-1).
$$

For odd orders, the corresponding bound is

$$
e^\eta\left[
 e^{T_{\rm e}}\frac{\sinh(\lambda+T_{\rm o})}{\sinh\lambda}-1
\right]
\le e^\eta\left[(1+\zeta)e^\tau-1\right].
$$

The last inequality follows because the logarithmic derivative of $\sinh y/y$ lies in $[0,1]$. These formulas remain valid for every $\lambda>0$.

Combining both parities with (9) and (19), we obtain

$$
\left|\frac{Q_k/\mathcal L_k}{H_k}-e^{\eta-\delta}\right|
\le e^\eta\left[\mathcal B+(1+\zeta)e^\tau-1\right].
\tag{21}
$$

## 6. Restore the permutation denominator

Since $\eta-\delta=-K^2/(4N)$, the central value in (21), after restoring $D_k$ and the target correction, is

$$
D_k\exp\left(-\frac{k^2+K^2}{4N}\right).
\tag{22}
$$

For $k\le N/4$,

$$
0\le\log D_k-\frac{k(k-1)}{2N}
\le\frac{k^3}{3N^2}.
\tag{23}
$$

Indeed, sum the logarithm remainder bound from Section 4 over $0\le j<k$, now with $u=j/N$. The sum is at most $k^3/[6N(N-k+1)]$, which is at most the right side of (23).

When $K=k$, the difference between $k(k-1)/(2N)$ and $(k^2+K^2)/(4N)$ is $-k/(2N)$. When $K=k-1$, it is $-1/(4N)$. Therefore

$$
\left|\log D_k-\frac{k^2+K^2}{4N}\right|\le r.
\tag{24}
$$

Equation (5) follows by multiplying (21) by $D_ke^{-k^2/(4N)}$ and bounding the difference between (22) and one by $e^r-1$.

## 7. Explicit uniform constants

Now fix $C\ge1$, $N\ge16C^2$, and $2\le k\le C\sqrt N$. These conditions imply $k\le N/4$, $K\le C\sqrt N$, $\eta\le a$, and $\delta\le C^2$.

The following identities make every power of $N$ explicit:

$$
\frac\lambda m=\frac43\sqrt{K/N},\qquad
\frac\eta m=\frac{3K}{2N},\qquad
\frac{\lambda^3}{m^2}=\frac{32K^{5/2}}{27N^{3/2}},
$$

$$
\frac{\lambda^2}{m^2}=\frac{16K}{9N},\qquad
\frac\eta{m^2}=\frac3N.
$$

Using $b\le\lambda$ and bounding extra powers of $\eta$ by powers of $a$, equation (4) therefore gives

$$
\mathcal B\le B_1(C)N^{-1/4}+B_2(C)N^{-1/2}+B_3(C)N^{-1}.
\tag{25}
$$

Moreover, $\tau\le\delta\le C^2$, so

$$
(1+\zeta)e^\tau-1
\le e^{C^2}(\tau+\zeta)
\le2e^{C^2}\left(C^{5/2}N^{-1/4}+CN^{-1/2}\right).
\tag{26}
$$

We also have $\log D_k\le k^2/N\le C^2$. Thus the multiplier of the bracket in (5) is at most $e^{7C^2/4}$. Finally,

$$
r\le\left(\frac C2+\frac{C^3}{3}\right)N^{-1/2},
\qquad r\le C^2/3.
$$

For the second inequality use $k\ge2$ and $k\le N/4$ to write

$$
r=\frac{k^2}{N}\left(\frac1{2k}+\frac{k}{3N}\right)
\le\frac{C^2}{3}.
$$

Hence $e^r-1\le e^{C^2/3}(C/2+C^3/3)N^{-1/2}$. Substitution of (25) and (26) into (5) proves (1) through (3).

## 8. Interpretation, scope and evidence

The rate has two sources at the largest allowed orders. Five-element blocks have total weight of order $k^{5/2}/N^{3/2}$. The third-order remainder in the pair availability product has the same order. At $k\asymp\sqrt N$, both are of order $N^{-1/4}$. The proof bounds them without identifying their signed next-order coefficient, so it does not claim that the rate is optimal for every parity or endpoint.

Exact parity conditioning is essential. For odd orders and very small $\lambda$, the conditioned triple count is near one. The shifted variable $t=J-1$ removes that compulsory triple and makes every error term vanish with $\lambda$ or $\eta$. This is why no artificial lower bound on $k$ or $\lambda$ appears in Theorem RATE-1.

The proof depends on the accepted positive partition representation, its leading coefficients, and elementary finite-moment calculations. It does not rely on any new saddle calculation or another live extension attempt. `check_rate.py` provides finite independent moment and numerical corroboration, recorded in `rate-checks-v1.json`. These checks do not establish the general theorem.

No historical priority or formal-verification claim is made. The accepted unquantified corrected approximation is strengthened here by an explicit rate, with a stated threshold and constants. No result for unbounded $k/\sqrt N$ is inferred from Theorem RATE-1.
