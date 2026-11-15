# Independent review of the sharp global error profile

Review ID: GSR-1-REV. Date: 15 November 2026, UTC.

Verdict: accept the stated uniform profile, sharp global rate, variational constant, and unique limiting maximizing scale in the exact revision reviewed. No required mathematical correction was found. This is a written mathematical audit with independent finite corroboration, not formal verification or historical priority certification.

Reviewed proof: `../global-sharp-rate/proof-v1.md`, SHA256 `c3f5bd362a005688d28a6ac1f5440188aa0b8f4a802de269b17c7d4e08e96fcf`. Its manifest has SHA256 `a67784bed544f88c670b000bda04ec700d257a98c14ffd33d77ea5958314e268`. All four dependency hashes in that manifest were checked against the local files and matched.

Prior exposure included earlier accepted asymptotic and mixed packets, the earlier correction review, and the public-source audit. The task brief announced the proposed sharp rate and profile before this review. The proof's reported numerical table was visible when the proof was read. Its check program and saved check data were not read. The independent full scans below use different values of $N$.

## 1. Exact normalization and integral

Use the notation of the reviewed proof. The ratio being estimated is exactly

\[
1+E_{N,k}
=\frac{Q_k}{L_kH_ke^{Nq(x)}(1+x)^{\epsilon-1/2}}.
\]

The factor $D_k=N^k/(N)_k$ cancels before any approximation. This is valid for every $2\le k\le N$, including $k=N$. No truncated approximation to the permutation denominator is needed or used.

The real integral can also be checked directly from the moment definition. Inclusion and exclusion over the $k$ cells gives

\[
Q_k=\sum_{j=0}^k\binom kj(-1)^{k-j}N^j
\frac{(N-j)!}{(N-k)!}.
\]

Expanding $(N-v)^k$ and integrating each monomial against $e^{-v}v^{N-k}$ gives exactly this sum after changing the summation index. Hence

\[
Q_k=\frac1{(N-k)!}\int_0^\infty e^{-v}v^{N-k}(N-v)^k\,dv.
\]

The split at $v=N$ has the sign $T_++(-1)^kT_-$. The substitutions $v=N(1-t)$ and $v=N(1+t)$ produce the common prefactor $N^{N+1}e^{-N}/(N-k)!$ in the two integrals. Thus the sign, factorial, and powers of $N$ in equations (18) and (19) of the proof are correct.

The normalizer for odd degree is also exact. One triple and $m-1$ pairs contribute

\[
\binom{2m+1}{3}4N\,(2m-3)!!N^{m-1}
=\frac{4m}{3}\frac{(2m+1)!}{2^m m!}N^m=L_{2m+1}.
\]

This compulsory triple accounts for the shifted variable $J-1$ below.

## 2. Compact critical expansion

Fix a closed interval $d\le k/N^{1/3}\le C$ with $d>0$. Then $K\asymp N^{1/3}$, while $\lambda$ stays in a compact subset of $(0,\infty)$. Put $m=K/2$ and $\eta=27\lambda^2/(16K)$.

The exact pair, triple, and four-block contribution is

\[
e^\eta\mathbb E\frac{(m-\epsilon)_s}{m^s},
\qquad s=\frac32(J-\epsilon)+2V,
\]

with unavailable falling factorials set to zero. Here $J$ is Poisson of mean $\lambda$ conditioned to have parity $\epsilon$, and $V$ is independent Poisson of mean $\eta$. For odd degree, the factor $1/\lambda$ in the partition sum cancels that in $H_k$. The conditioning is therefore by $\sinh\lambda$, not by an unconditional Poisson probability. This verifies the exact normalization in equation (11).

Writing $t=J-\epsilon$, differentiation of the two parity series gives

\[
\mathbb Et=p_\epsilon(\lambda),\qquad
\mathbb Et^2=\lambda^2+(1-2\epsilon)p_\epsilon(\lambda).
\]

For $A=s(s-1+2\epsilon)/(2m)$, the availability bound used in the proof is valid even outside the feasible range. When $s\le m/2$, summing the quadratic remainder in $-\log(1-r/m)$ gives

\[
0\le e^{-A}-w_\epsilon(s)\le s^3/m^2.
\]

When $s>m/2$, both $e^{-A}$ and $w_\epsilon(s)$ lie in $[0,1]$, and $4s^3/m^2>1$. Thus the stated bound with constant four holds for every nonnegative integer $s$. All fixed moments of $s$ are uniformly bounded on the current compact interval. Taylor's remainder for $e^{-A}$ consequently gives

\[
\mathbb Ew_\epsilon(s)=1-\mathbb EA+O(K^{-2}).
\]

Terms involving $V$ in $\mathbb EA$ are $O(K^{-2})$. The terms involving only $t$ give

\[
\mathbb EA
=\frac1K\left(\frac94\lambda^2
+\frac34(1-2\epsilon)p_\epsilon(\lambda)\right)
+O(K^{-2}).
\]

The coefficient of $p_\epsilon$ is the sum of $\frac94(1-2\epsilon)$ from $t^2$ and $\frac32(2\epsilon-1)$ from $t$. This checks the sign that distinguishes the two parities.

Blocks of size at least five contribute only $O(K^{-2})$. In fact, $x=3\lambda/(2K)$ and

\[
Nx^5=\frac{27\lambda^3}{8K^2}.
\]

The total positive weight of these blocks is bounded by $Nx^5/(1-x)$. Dropping availability only enlarges their contribution. The even and odd parity projections are smooth functions of the extra even and odd weights, with denominators $\cosh\lambda$ and $\sinh\lambda$ bounded away from zero on the current interval. This proves the required uniform bound without assuming independence from the parity event.

Combining $e^\eta$ with the availability loss gives

\[
\frac{Q_k}{L_kH_k}
=1+\frac1K\left(-\frac9{16}\lambda^2
+\frac34(2\epsilon-1)p_\epsilon(\lambda)\right)
+O(K^{-2}).
\]

The approximation's remaining factor has the expansion

\[
e^{Nq(x)}(1+x)^{\epsilon-1/2}
=1+\frac1K\left(-\frac9{16}\lambda^2
+\frac34(2\epsilon-1)\lambda\right)
+O(K^{-2}).
\]

The common quadratic terms cancel. Division gives equation (17) of the proof, including its sign and its uniform $O_{d,C}(K^{-2})$ remainder. Replacing $K/N^{1/3}$ by $k/N^{1/3}$ costs $O_{d,C}(N^{-1/3})$ in the scaled profile because the profile functions are smooth on a slightly enlarged compact interval. This proves the compact part of the asserted limit.

## 3. Uniform real Laplace estimate

For $k\le N/4$, write $u=\sqrt{k/N}\le1/2$ and rescale $t=us$. The normalized phase derivatives are

\[
F_\pm'(s)=\frac{1-s^2}{s(1\mp us)},\qquad
F_\pm''(1)=-\frac2{1\mp u}.
\]

These follow by differentiation of the exact integrals. They have the required signs. On, for example, $3/4\le s\le5/4$, all derivatives through order six are bounded uniformly for $0\le u\le1/2$. The curvature at one is bounded away from zero in absolute value.

The endpoint motion causes no loss of uniformity. On the left of this neighborhood, monotonicity gives a fixed negative phase gap. On the right, for the plus phase,

\[
-F_+'(s)\ge s-1/s\ge9/20.
\]

For the minus phase,

\[
-F_-'(s)\ge\frac{s-1/s}{1+s/2}\ge\frac{18}{65}
\qquad(s\ge5/4).
\]

The latter function is increasing, as direct differentiation verifies. Hence the right outer integrals have a uniformly exponentially small bound even when their domain becomes unbounded as $u\to0$. The left outer domain has length at most one and a fixed phase gap.

On a smaller symmetric neighborhood of one, Taylor expansion of the phase gives a quadratic Gaussian term, an odd cubic term, and a uniformly controlled remainder. The integral of the isolated cubic term is zero. The remaining error is bounded by integrals of

\[
(k y^4+k^2y^6)e^{-c k y^2},
\]

which are $O(k^{-3/2})$. The leading Gaussian integral is of order $k^{-1/2}$. This proves uniform relative error $O(k^{-1})$. Stirling's formula for $(N-k)!$ adds only $O((N-k)^{-1})$, which is also $O(k^{-1})$ in this range.

Substitution of the Gaussian factor and Stirling's leading term gives exactly the two displayed $B_\pm$ in equation (21). Thus equation (20) remains valid as $u$ tends to zero. The proof does not require $k/N$ to stay bounded away from zero.

## 4. Positive amplitude and the negative saddle

For even degree, Stirling's formula gives

\[
L_K=\sqrt2(NK/e)^{K/2}(1+O(K^{-1})).
\]

Substitution in $P_{N,K}$ matches $B_+$ with relative error $O(K^{-1})$. For adjacent odd degree the exact normalizers give

\[
\frac{P_{N,K+1}}{P_{N,K}}=\frac{(K+1)(1+x)}x.
\]

Direct differentiation of $g(v)=\log B_+(v)$ gives

\[
g'(v)=\log(Nu_v(1+u_v))
-\frac1{4Nu_v(1+u_v)},\qquad u_v=\sqrt{v/N}.
\]

Its variation over $[K,K+1]$ is $O(K^{-1})$. The last displayed correction is itself $O(K^{-1})$. Thus the adjacent ratio of $B_+$ is $Nx(1+x)(1+O(K^{-1}))$. Since $Nx=K/x$, its ratio to the exact adjacent ratio of $P$ is $1+O(K^{-1})$. This verifies equation (25) for odd degree without replacing its normalizer by the even one.

For the other saddle, direct subtraction of the two logarithms gives

\[
\log(B_-/B_+)=\operatorname{artanh}u-N\Delta(u),
\quad
\Delta(u)=\frac43u^3+O(u^5).
\]

The remainder is uniform for $u\le1/2$ by the convergent series for $\operatorname{artanh}u$. Also

\[
0\le\lambda_k-\lambda\le u.
\]

Consequently $B_-/B_+=e^{-2\lambda}e^\theta$ with $|\theta|\le C(u+Nu^5)$. For $k\le\sqrt N$, this bound tends uniformly to zero, so the difference from $e^{-2\lambda}$ is at most $C(u+Nu^5)e^{-2\lambda}$.

The target denominator is exactly $P_{N,k}(1+(-1)^\epsilon e^{-2\lambda})$. When $\lambda\ge1$, it is bounded below by $(1-e^{-2})P_{N,k}$. Combining the two saddle errors with the amplitude comparison proves equation (29). The negative saddle is matched to the hyperbolic factor. It is not discarded at a scale where its contribution may matter.

## 5. Both tails and the full supremum

For $k=cN^{1/3}$ with $c\ge C_0$, the estimate just proved gives a scaled upper bound of the form

\[
C\left(c^{-1}+(\sqrt c+c^{5/2})e^{-2c^{3/2}/(3\sqrt2)}\right)
\]

through $k\le\sqrt N$. Its supremum for $c\ge C_0$ tends to zero with $C_0\to\infty$. The accepted complex coefficient estimate gives $O(N^{-1/2})$ unscaled error for $\sqrt N\le k\le N$. Multiplication by $N^{1/3}$ makes that part tend to zero, including the permutation endpoint.

At the lower boundary, the finite hyperbolic estimate, the elementary bound on $\log D_k$, and

\[
-x^4/4\le q(x)\le0
\]

give $|\log(1+E_{N,k})|\le6k^2/N+\frac12\sqrt{k/N}$. For $k\le dN^{1/3}$ the right side is at most $(6d^2+\frac12\sqrt d)N^{-1/3}$. The inequality $|e^y-1|\le|y|e^{|y|}$ proves the stated lower-tail limsup bound. Fixed orders and small odd $\lambda$ are included without dividing by $\sinh\lambda$.

Both profiles tend to zero at zero and infinity. The compact expansion and these two tail estimates therefore prove the full supremum limit in equation (3), with the order of limits stated in the proof. No range between the compact interval and the two tails is omitted.

## 6. Constant and uniqueness

The explicit parity profiles are

\[
\Phi_0(c)=\frac3{4c}\frac{2\ell}{e^{2\ell}+1},\qquad
\Phi_1(c)=-\frac3{4c}\left(1-\frac{2\ell}{e^{2\ell}-1}\right).
\]

Their absolute difference is $\frac3{4c}(1-2\ell/\sinh(2\ell))>0$. The odd profile therefore determines the global constant. Positivity and vanishing at both endpoints ensure that its supremum is attained at a positive finite scale. Choosing the nearest odd integer to that scale times $N^{1/3}$ supplies the matching lower bound for every sufficiently large integer $N$. This proves exponent optimality for the unchanged approximation, rather than only along a selected sequence of matrix sizes.

Set $z=(4/3)c^{3/2}$. For $g(z)=z^{-2/3}(1-z/(e^z-1))$, direct differentiation shows

\[
3z^{5/3}(e^z-1)^2g'(z)=-H(z),
\]

with $H$ as in equation (37). Its series is

\[
H(z)=-z^3/2-z^4/6+
\sum_{n\ge5}\frac{2^{n+1}-3n^2+4n-4}{n!}z^n.
\]

The coefficient numerator is five at $n=5$. Its next value minus twice its current value is $3n^2-10n+5>0$ for $n\ge5$. Thus all later coefficients are positive. Termwise differentiation shows that $H(z)/z^4$ is strictly increasing. Its limits are negative infinity at zero and positive infinity at infinity. There is exactly one positive zero, with $g$ increasing before it and decreasing afterward.

This verifies the variational constant and the unique limiting maximizing scale. It does not assert uniqueness of the maximizing integer at each finite $N$. In fact, the uniform profile also implies that every sequence of finite maximizers has $k/N^{1/3}\to c_*$ and is eventually odd. To see the latter statement, the even profile attains its own positive maximum, which is strictly smaller than the odd maximum by the strict pointwise inequality above. The uniform convergence preserves this positive gap for sufficiently large $N$. The tail estimates and strict uniqueness then force the scale convergence.

## 7. Independent finite corroboration

The check program uses exact integer arithmetic for

\[
Q_k=2(k-1)Q_{k-1}+(k-1)(N-k+2)Q_{k-2}.
\]

It separately compared that recurrence with 558 exact alternating sums from the moment definition, covering $2\le N\le32$ and all their orders including zero and one. It also compared 38 coefficients at $N=37$ with the independent positive block convolution from the exponential generating function. All comparisons were exact and passed.

The normalized errors were then evaluated at 80 decimal digits. Full scans gave:

| $N$ | Maximizing order | $N^{1/3}\sup_k|E_{N,k}|$ | Largest scaled profile discrepancy |
| --- | --- | --- | --- |
| 257 | 9 | 0.3708392201 | 0.0642679165 |
| 2048 | 17 | 0.3819746664 | 0.0453176570 |
| 15625 | 31 | 0.3886574837 | 0.0320112815 |

All maximizing orders were odd. Thirty-six additional selected checks at $N=10^6$ and $10^9$ covered both parities, fixed orders, the critical scale, larger critical multiples, and adjacent orders near $\sqrt N$.

The independent root calculation gives

\[
z_*=1.67746050737286059472143351424\ldots,
\]

\[
c_*=1.16540187318374991886189563144\ldots,
\qquad
\mathfrak C=0.395496270090507693120291483372\ldots.
\]

These agree with the proof's corroborating decimals. At $N=10^9$, the odd order $k=1165$ gives scaled signed error approximately $-0.3953217324$, compared with profile $-0.3954962512$.

The largest profile discrepancy in each full scan occurred at $k=3$. This is compatible with the theorem's qualitative uniform convergence. Indeed, $Q_3=L_3$, $x=\sqrt{2/N}$, $\log H_3=O(N^{-1})$, and $Nq(x)=O(N^{-1})$. The exact ratio therefore gives $E_{N,3}=-1/\sqrt{2N}+O(N^{-1})$. Expanding the odd profile at zero gives

\[
N^{1/3}E_{N,3}-\Phi_1(3N^{-1/3})
=\left(\frac{\sqrt3}{2}-\frac1{\sqrt2}\right)N^{-1/6}
+O(N^{-2/3}).
\]

Thus the replacement of $K=2$ by the critical coordinate $k=3$ leaves a discrepancy of order $N^{-1/6}$ after scaling. No faster convergence rate for the full profile discrepancy is claimed.

The saved numbers are corroboration only. The all-order conclusion, both tail limits, and uniqueness rest on the written estimates above. No evaluated finite threshold for the limiting constant or claim of historical firstness is accepted or inferred.

## 8. Frozen review disposition

Accepted claims: the full uniform parity profile, the optimal $N^{-1/3}$ relative error for the unchanged GLOBAL-1 formula, the stated exact variational constant, and uniqueness of its limiting scale.

Required changes: none. Open mathematical findings: none. The proof and all previously frozen evidence were left unchanged. This review, its independent check program, the check output, and their hashes are recorded in the separate review manifest.
