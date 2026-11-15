# Classical Whittaker specialization and its error precision

Revision 1. Audit calculation dated November 15, 2026 UTC.

This calculation assesses derivability and does not identify an earlier publication of the exact manuscript statements. Its inputs are the classical identities linked below and the exact positive generating function already established in the frozen base packet. It does not depend on the manuscript's asymptotic theorems.

## 1. An exact connection with no singular parameter limit

Let integers satisfy $N\ge2$ and $0\le k\le N$. Set

\[
Q_k=k!L_k^{(-N-1)}(-N),\qquad
b=N/2-k,\qquad \mu=(N+1)/2.
\]

The terminating Kummer relation and the definition of Whittaker $W$ give

\[
W_{-b,\mu}(z)=W_{-b,-\mu}(z)
=(-1)^k k!z^{-N/2}e^{-z/2}L_k^{(-N-1)}(z).
\tag{1}
\]

Apply the connection formula [DLMF 13.14.32](https://dlmf.nist.gov/13.14.E32) at positive argument $N$. Its gamma factors here are $\Gamma(N+2)$, $\Gamma(N+1-k)$ and $\Gamma(k+1)$, all finite. The phases in (1) cancel exactly. Consequently

\[
\boxed{
Q_k=k!e^{-N/2}N^{N/2}
\left\{\frac{M_{b,\mu}(N)}{(N+1)!}
+(-1)^k\frac{W_{b,\mu}(N)}{(N-k)!}\right\}.
}
\tag{2}
\]

The symmetry $W_{\kappa,\mu}=W_{\kappa,-\mu}$ is [DLMF 13.14.31](https://dlmf.nist.gov/13.14.E31). This use of positive $\mu$ avoids the singular conventional $M$ function at a negative half-integer parameter.

The classical Kummer integrals [DLMF 13.4.1](https://dlmf.nist.gov/13.4.E1) and [13.4.4](https://dlmf.nist.gov/13.4.E4) turn (2) into

\[
Q_k=A_++(-1)^kA_-,\qquad A_\pm>0,
\tag{3}
\]

\[
A_+=\frac{N^{N+1}e^{-N}}{(N-k)!}
\int_0^1 e^{Nt}t^k(1-t)^{N-k}\,dt,
\tag{4}
\]

\[
A_-=\frac{N^{N+1}e^{-N}}{(N-k)!}
\int_0^\infty e^{-Nt}t^k(1+t)^{N-k}\,dt.
\tag{5}
\]

An elementary independent check is

\[
Q_k=\frac1{(N-k)!}\int_0^\infty e^{-s}s^{N-k}(N-s)^k\,ds.
\tag{6}
\]

Expanding $(N-s)^k$ proves (6) by factorial integration and the finite Laguerre formula. Splitting (6) at $s=N$ and using $s=N(1\mp t)$ proves (3) to (5) directly. Thus the integral representation is classical and elementary, independently of any Whittaker asymptotic theorem.

## 2. What the published Olver approximation covers

Olver's 1980 paper concerns positive real argument and large positive $\mu$, with a bounded ratio of parameters. The exact formulas used here are recorded in [DLMF 13.20(iii), equations 13.20.11 and 13.20.12](https://dlmf.nist.gov/13.20.iii). They approximate $W_{b,\mu}(x)$ and $M_{b,\mu}(x)$ by parabolic cylinder functions with individual relative errors

\[
O(\mu^{-1}\log\mu),
\tag{7}
\]

uniformly for $x>0$ and $-(1-\delta)\mu\le b\le\mu$, with fixed $\delta>0$. The DLMF attributes these formulas and error bounds to [Olver (1980), DOI 10.1017/S0308210500012130](https://doi.org/10.1017/S0308210500012130). The original article body was not accessible in this audit. Its publisher synopsis and the displayed DLMF formulas were inspected.

For every fixed $0<c<1$, all $k\le cN$ satisfy this parameter condition for sufficiently large $N$. For example, $\delta=1-c$ works. Thus this classical parameter range includes all sublinear orders after the exact rotation in (2). It is incorrect to exclude it merely because the unrotated argument is negative or because the unrotated parameters approach the opposite endpoint.

For specificity, the parabolic cylinder parameter is

\[
a=\mu-b=k+\tfrac12.
\]

Write $X=\sqrt{4\mu^2-4bN+N^2}=\sqrt{4N(k+1/2)+1}$ and $\tau=\zeta\sqrt{2\mu}$. The DLMF change of variable is equivalently

\[
\frac{\tau\sqrt{\tau^2+4a}}4
+a\operatorname{arsinh}\frac{\tau}{2\sqrt a}
=\frac X2
-b\log\frac{X+N-2b}{2\sqrt{\mu^2-b^2}}
-\mu\log\frac{\mu X+2\mu^2-bN}{N\sqrt{\mu^2-b^2}}.
\tag{8}
\]

The two leading approximants contain $U(a,\tau)$ and $U(a,-\tau)$ with the explicit, different gamma-scale prefactors in those DLMF formulas. Replacing these prefactors by one common factor before checking their size would lose control of the odd difference.

## 3. Uniform real saddle bounds and the odd condition number

Fix $0<c<1$ and put $u=\sqrt{k/N}\le\sqrt c$. Both integrals (4) and (5) have their unique interior maximum at $t=u$. Their second logarithmic derivatives there are $-2N/(1-u)$ and $-2N/(1+u)$, respectively.

The following standard real Laplace calculation has uniform constants on this range as $k\to\infty$:

\[
\begin{aligned}
A_+&=B_+\{1+O_c(k^{-1})\},\\
A_-&=B_-\{1+O_c(k^{-1})\},
\end{aligned}
\tag{9}
\]

where Stirling's estimate for $(N-k)!$ has been included, and

\[
B_+=\frac{(Nu)^k}{\sqrt{2(1+u)}}
\exp\left(N\{u-u^2-(1-u^2)\log(1+u)\}\right),
\tag{10}
\]

\[
B_-=\frac{(Nu)^k}{\sqrt{2(1-u)}}
\exp\left(N\{-u-u^2-(1-u^2)\log(1-u)\}\right).
\tag{11}
\]

Here is a verification of uniformity sufficient for this audit. Rescale $t=us$ and subtract the logarithm at $s=1$. The normalized phases have derivatives

\[
F_\pm'(s)=\frac{1-s^2}{s(1\mp us)},\qquad
F_\pm''(1)=-\frac2{1\mp u}.
\tag{12}
\]

On a fixed neighborhood of $s=1$, all derivatives through any fixed order are bounded uniformly for $0\le u\le\sqrt c$. The second derivatives are bounded away from zero there. Outside that neighborhood the phase decreases at a rate bounded away from zero on the right and has a uniformly negative gap on the left. Taylor expansion through the quartic term, cancellation of the odd cubic integral, and exponentially small tails give relative error $O_c(k^{-1})$. The same argument without the expansion gives the upper bounds $A_\pm\le C_cB_\pm$ for all $k\ge3$ and sufficiently large $N$. Stirling adds $O((N-k)^{-1})$, which is absorbed in $O_c(k^{-1})$.

The exponent difference is

\[
\Delta(u)=2u-(1-u^2)\log\frac{1+u}{1-u}
=\sum_{j\ge1}\frac{4u^{2j+1}}{(2j-1)(2j+1)}
\ge\frac43u^3.
\tag{13}
\]

Hence $B_-/B_+=\exp(\operatorname{artanh}u-N\Delta(u))$. For $k\ge N^{1/3}$ this ratio is bounded away from one, uniformly for sufficiently large $N$. Equation (9) then shows that the exact ratio $A_-/A_+$ is also bounded away from one.

For odd $3\le k\le N^{1/3}$, set $E_k=(Nk/e)^{k/2}$. Equations (10) and (11) and the upper bounds following (12) give $A_++A_-\le C E_k$, because $Nu^3\le1$. The exact positive generating function

\[
Q_k=k![z^k]\exp\left(N\sum_{j\ge2}\frac{j-1}{j}z^j\right)
\]

has the contribution from one block of size three and $(k-3)/2$ blocks of size two. This gives

\[
Q_k\ge\frac{2(k-1)}3
\frac{k!}{2^{(k-1)/2}((k-1)/2)!}N^{(k-1)/2}
\ge c_0\frac{k^{3/2}}{\sqrt N}E_k,
\tag{14}
\]

where the last constant is absolute by Stirling's inequalities, including the finitely many smallest orders. We therefore obtain the condition-number bound

\[
\boxed{
\frac{A_++A_-}{Q_k}
\le C_c\max\left(1,\frac{\sqrt N}{k^{3/2}}\right)
\quad\text{for odd }3\le k\le cN.
}
\tag{15}
\]

For even $k$, this ratio is exactly one. The exclusion of $k=1$ is essential, since $Q_1=0$.

## 4. Consequence for Olver's error precision

Let $\widehat Q_k$ be obtained by replacing the two Whittaker functions in (2) by their respective leading Olver approximants, with their exact prefactors. Equations (7) and (15) imply

\[
\boxed{
\sup_{2\le k\le cN}
\left|\frac{\widehat Q_k}{Q_k}-1\right|
=O_c\left(\frac{\log N}{\sqrt N}\right)
=o(N^{-1/4}).
}
\tag{16}
\]

Indeed, an error bounded relatively for each positive term is bounded absolutely by that error times $A_++A_-$. The odd subtraction must be performed only after this estimate. For fixed odd $k$, amplification can have order $\sqrt N$, but (7) is still small enough for (16).

This is an audit deduction, not a theorem claimed to appear in Olver's paper. It shows that the classical approximation has sufficient error precision for the manuscript's $N^{-1/4}$ correction. The outstanding conversion is the explicit analysis of the parabolic cylinder functions and their two prefactors, not a mismatch of parameter ranges or a loss of precision that rules out the classical route. The argument does not give uniform control as $c\uparrow1$.

## 5. The positive square-root scales are elementary consequences

Fix $0<d<C<\infty$ and $d\sqrt N\le k\le C\sqrt N$. Then $N\Delta(u)$ grows at least as a positive multiple of $N^{1/4}$. Equations (9) to (13) give

\[
Q_k=B_+\{1+O_{C,d}(N^{-1/2})\}.
\tag{17}
\]

Thus the same action and amplitude arise directly from the classical real integrals, without needing Olver's more general approximation. To spell out the comparison, use the manuscript definitions $R_k$, $H_k$, $K=k-\epsilon$ and

\[
G(u)=u+u^2/2+(1-u^2)\log(1-u)-2u^3/3.
\]

Stirling's formula in the even leading normalizer gives $\sqrt2 E_k\{1+O(k^{-1})\}$. In the odd case it gives $\sqrt2 E_k\lambda_K\{1+O(k^{-1})\}$, where $\lambda_K=(2/3)K^{3/2}/\sqrt N$. Since $H_k=e^{\lambda_K}/(2\lambda_K^\epsilon)$ up to an exponentially small relative error, (17) yields

\[
\log\frac{R_k}{H_k}
=NG(u)+(\epsilon-1/2)u+O_{C,d}(N^{-1/2}).
\tag{18}
\]

For the denominator, the identity

\[
\log D_k
=N\{u^2+(1-u^2)\log(1-u^2)\}
+\tfrac12\log(1-u^2)+O(N^{-1})
\]

follows from Stirling on this range. In the odd case the remaining correction is $\lambda_k-\lambda_{k-1}=u+O((Nk)^{-1/2})$. These give (18) with the exact parity sign.

Finally,

\[
NG(u)=\frac{k^2}{4N}+\frac{2k^{5/2}}{15N^{3/2}}+O_{C,d}(N^{-1/2}).
\]

Consequently, writing $W_{N,k}=R_k/(e^{k^2/(4N)}H_k)$,

\[
N^{1/4}(W_{N,k}-1)
=\frac{2\epsilon-1}{2}\sqrt{k/\sqrt N}
+\frac2{15}(k/\sqrt N)^{5/2}+o(1)
\tag{19}
\]

uniformly on $d\sqrt N\le k\le C\sqrt N$. This verifies classical derivability of the positive-scale correction. It is not evidence that an earlier source states the exact uniform theorem down to fixed orders or its sharp supremum constant.

The same calculation gives the sublinear action when $k=o(N)$ and $k/N^{1/3}\to\infty$. Extending a single relative formula through the central transition and down to fixed orders still requires a parity-sensitive patch. The manuscript supplies that patch explicitly.

## 6. Discriminating finite checks

At 70 decimal digits, (2) agrees with the terminating Laguerre value for $(N,k)=(3,2),(3,3),(8,3),(8,4),(12,11),(12,12)$ with relative discrepancies at most $2\cdot10^{-71}$. These checks include both parities and the endpoint $k=N$. They are corroboration, not premises of the identities or bounds above.

The leading Olver proxy was also evaluated at $(100,3),(1000,3),(100,10),(10000,100),(10000,101)$. Its relative errors were approximately $-0.002776$, $-0.0008147$, $-0.0009546$, $-0.00001021$, and $-0.00001021$, respectively. The fixed odd order visibly amplifies the individual approximation errors. The exact condition-number analysis in Section 3 is what permits the uniform conclusion (16).
