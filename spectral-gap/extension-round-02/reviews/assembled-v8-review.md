# Assembled manuscript v8 delta review

Date: November 14, 2026, America/Los_Angeles.

Decision: Accept the mathematical integration of SG-14 and SG-15. The new theorem statements, both global-profile tails, exact one-conflict envelope, figure values and normalizations pass review. Three editorial findings remain present in frozen v8 and are listed below. This is not unqualified approval of v8 as the final reading copy.

The integrator reports that AV8-E1 and AV8-E2 have been corrected in maintained sources. Those later edits are outside the frozen revision reviewed here and require a subsequent delta check. No frozen or maintained source was edited by this review.

## Exact revision and prior exposure

The v8 manifest SHA256 is 4480fd2f51caf7cab2072a830520ffcb8f3c5fddea85e84f79958f0cde6c3d85. All 28 listed file hashes match. The base is accepted frozen v7, manifest ed77594646cbc9c1372aebaa707f209d9395a1c20b40bf6bb8fb6943695b9b80.

| Item | SHA256 |
| --- | --- |
| Main PDF, 40 pages | 951db47dc3b42dd72461e32655b84f3fead884b8a86255f072c715b09f15c1dc |
| Guide PDF, 8 pages | 9c8b76e4873fd731b43293a2b281217f3c3cd7e113a19ab7e4f3ad073e3452de |
| Mixed source | b822c896bf25d0d00b717e34bd48c2b743e0ad282e57a30c8cc27daef0589ab1 |
| Asymptotics source | e530fe5798c257af219ad4b9d6da6d2fb67b3bde7a3847372b6a4b91d63a7930 |
| Global sharp-error appendix | 2c5271d3cae808b679124b276f8bbe5f1b323c49aa1a2a9fd7b484384fb185ab |
| Guide source | 0d44aca811619e69984d12addd9d1665f83b6d838b521150187f4e52c0beec06 |
| New figure data | dfcbffa8f055e78b2d51fdf8f7686b580ca03c8d2554e4861c29b151d6951939 |
| New scientific figure PDF | 4bf820fe9d7ac9ad267a6040d590be5fc9ba4b68c0a034c5ef688d71d658d05d |

Prior exposure includes the base mixed proof, the original sublinear proof, earlier assembled revisions, and the separate one-conflict proof and integration reviews. The new SG-15 author proof was read and its main derivations were reconstructed. The separate SG-15 review was read afterward for comparison. Its agreement is not used as proof.

The SG-15 author proof hash is c3f5bd362a005688d28a6ac1f5440188aa0b8f4a802de269b17c7d4e08e96fcf. The supplied independent review hash is e24147156e4eae856fdea4447756ec88167bce783d43dd27bc76fcc21e93cda3. Both match the task packet.

## Findings requiring a subsequent editorial delta

### AV8-E1. The triple-count explanation omits the odd shift

Location: asymptotics.tex, paragraph immediately after Theorem thm:global, rendered page 24. Also guide reading-guide.tex, “Why another correction helps”, rendered page 7.

The proof uses $T=J-\epsilon$, not the raw parity-conditioned triple count $J$. Its first error contains

$$
\frac{3(2\epsilon-1)}{4K}
\left(\mathbb E[J-\epsilon]-\lambda\right).
$$

For odd parity, $p_1(\lambda)-\lambda\to-1$ as $\lambda\to\infty$. Thus the guide's explanation that the two means become nearly equal does not describe the discrepancy in the displayed error formula. The theorem, appendix and numerical figure use the correct shifted quantity.

Minimal repair: name the triple count after subtracting the compulsory odd triple, and explain that the shifted discrepancy stays bounded while its contribution is divided by $K$. This does not require changing any theorem or proof. The integrator recorded the issue as SG-MAN-I10 and reports a maintained-source repair, not yet checked in a frozen successor.

### AV8-E2. The abstract leaves the second rate's approximation ambiguous

Location: main.tex abstract, rendered page 1.

After stating the full-range $C_*N^{-1/3}+o(N^{-1/3})$ result, the abstract refers to the sharp constant in “its” $N^{-1/4}$ rate on square-root ranges. The pronoun can refer to the same approximation. The two theorems concern different formulas.

Minimal repair: explicitly name the shorter quartically corrected hyperbolic approximation in the second rate sentence. The theorem sections, discussion and guide already distinguish the two formulas. The integrator recorded the issue as SG-MAN-I11 and reports a maintained-source repair, not yet checked in a frozen successor.

### AV8-E3. The contents overflow creates an almost empty page

Location: main PDF page 2.

The final contents entry, Appendix B, is alone at the top of page 2. The rest of that page is blank. The longer abstract and added appendix entry caused a one-line contents overflow.

Minimal repair: keep the last contents entry with the other contents, using a small local layout adjustment. This affects presentation only. It was reported during the all-page inspection. No clipping or formula overflow was found elsewhere.

## SG-14 integration

The separately accepted one-conflict candidate is included byte-for-byte. Its kernel difference, both selected-support cases, affine weights, domain bounds and attaining construction remain intact. The main theorem uses $\mathcal P_h$ consistently with the base section.

The introduction and discussion now identify exact maxima for $b=0$ and $b=1$. They retain the restriction that the general $2^{b-1}$ bound has no asserted sharpness for $b>1$. The guide's additional pattern explains the raw match forcing the distinguished indicator to zero and the resulting factor $-1/N$. The $h=1$ example is now explicitly restricted to $b=0$, preventing confusion with the new case.

## SG-15 reconstruction

### Exact normalization and notation

The manuscript correctly translates the author's polynomial normalizer $L_k$ to $\mathcal L_k$. Its existing $L_k$ in the diagonal-leading-term notation is not substituted for this polynomial. Appendix B consistently uses

$$
1+\mathcal E_{N,k}
=\frac{Q_k/(\mathcal L_kH_k)}
 {e^{Nq(x)}(1+x)^{\epsilon-1/2}}.
$$

This follows from $R_k=D_kQ_k/\mathcal L_k$ and cancels $D_k=N^k/(N)_k$ exactly, including $k=N$. The odd normalizer has the exact compulsory-triple factor $4m/3$. The old sublinear theorem, correction hierarchy and square-root rate statements remain unchanged.

### Compact critical expansion

For every fixed $0<d<C<\infty$, the range $dN^{1/3}\le k\le CN^{1/3}$ gives $K\asymp N^{1/3}$ and a compact positive range of $\lambda$. The exact pair, triple and four-block contribution is

$$
e^\eta\mathbb E w_\epsilon\left(\tfrac32(J-\epsilon)+2V\right).
$$

At odd orders the reciprocal $\lambda$ in the coefficient expression cancels that in $H_k$. The parity normalization is therefore correct.

The moments

$$
\mathbb ET=p_\epsilon(\lambda),
\qquad
\mathbb ET^2=\lambda^2+(1-2\epsilon)p_\epsilon(\lambda)
$$

give the coefficient

$$
\mathbb EA(S)
=\frac1K\left(\frac94\lambda^2
+\frac34(1-2\epsilon)p_\epsilon(\lambda)\right)+O(K^{-2}).
$$

The availability error includes infeasible counts, since the assigned-zero product still satisfies the stated bound. Fixed moments of $S$ stay bounded on the compact interval. The combined weight of all block sizes at least five is $O(K^{-2})$, not merely the weight of one such block. Removing their availability factors and projecting parity preserves that estimate because the relevant normalizing functions are bounded away from zero on the present interval.

Since $\eta=27\lambda^2/(16K)$, multiplication by $e^\eta$ produces the common coefficient $-9\lambda^2/(16K)$. It cancels against the same coefficient in the target approximation. Division gives precisely

$$
\mathcal E_{N,k}
=\frac{3(2\epsilon-1)}{4K}
\bigl(p_\epsilon(\lambda)-\lambda\bigr)+O_{d,C}(K^{-2}).
$$

The replacement of $K$ by $k$ in the critical coordinate costs only a vanishing scaled error uniformly on such compact intervals.

### Uniform two-saddle estimate

The real Gamma integral has the correct factorial and sign. Splitting at $N$ gives $T_++(-1)^kT_-$. With $u=\sqrt{k/N}\le1/2$ and $t=us$, the phases satisfy

$$
F_\pm'(s)=\frac{1-s^2}{s(1\mp us)},
\qquad F_\pm''(1)=-\frac2{1\mp u}.
$$

The local derivatives are uniformly bounded as $u\to0$. On a fixed interval to the left of one, the phase has a uniform gap. On the right, its derivative stays below a negative constant, so the outer integrals remain uniformly integrable even when the domain grows. The central cubic contribution is odd and cancels on a symmetric interval. The remaining Gaussian error is relative $O(k^{-1})$.

Stirling's error for $(N-k)!$ is also $O(k^{-1})$ on $k\le N/4$. It yields the stated $B_+$ and $B_-$, including their different amplitudes. The adjacent odd-degree comparison is valid because

$$
\frac{P_{N,K+1}}{P_{N,K}}=\frac{(K+1)(1+x)}x
$$

and differentiation of $\log B_+$ gives the displayed derivative with variation $O(K^{-1})$. No odd-degree normalization is dropped.

### Upper tail

Direct subtraction of the saddle actions gives

$$
B_-/B_+=\exp\{\operatorname{artanh}u-N\Delta(u)\}.
$$

The expansion $\Delta(u)=4u^3/3+O(u^5)$ and $0\le\lambda_k-\lambda\le u$ yield the matched ratio $e^{-2\lambda}e^\theta$ with $|\theta|\le C(u+Nu^5)$. On $k\le\sqrt N$ this tends uniformly to zero. For $\lambda\ge1$, the parity denominator is bounded below by $1-e^{-2}$, and the manuscript obtains a uniform bound with absolute constants.

After multiplying by $N^{1/3}$, its supremum on $C_0N^{1/3}\le k\le\sqrt N$ tends to zero as $C_0\to\infty$. The unchanged complex coefficient estimate treats $\sqrt N\le k\le N$ with unscaled $O(N^{-1/2})$ error. This proves the full upper tail, including both endpoint parities.

### Lower tail and the full quantifier

The bound $-x^4/4\le q(x)\le0$, the exact-denominator estimate and the earlier finite logarithmic comparison imply

$$
|\log(1+\mathcal E_{N,k})|
\le6k^2/N+\tfrac12\sqrt{k/N}.
$$

For fixed $d>0$, all its hypotheses hold throughout $2\le k\le dN^{1/3}$ once $N$ is sufficiently large. Exponentiation yields the stated scaled limsup at most $6d^2+\sqrt d/2$. This tends to zero with $d$, and includes fixed orders and small odd $\lambda$ without dividing by a vanishing hyperbolic sine.

The compact expansion and the two tails cover the entire range with the correct order of limits. Thus the supremum convergence over all integers $2\le k\le N$ is supported, not just convergence on each fixed critical scale.

### The sharp constant and its unique scale

Both profiles vanish at zero and infinity. Their exact difference in absolute value is positive, so the odd profile determines the supremum. The maximizing function is a positive multiple of

$$
g(z)=z^{-2/3}\left(1-\frac z{e^z-1}\right).
$$

Its derivative has sign opposite to the stated $\mathcal H(z)$. The power series has negative cubic and quartic coefficients followed by strictly positive coefficients. Consequently $\mathcal H(z)/z^4$ is strictly increasing from negative infinity to positive infinity, giving exactly one positive zero. Odd integers nearest the maximizing scale provide the lower bound for every sufficiently large $N$.

The theorem claims uniqueness of the limiting continuous scale, not uniqueness of the maximizing integer for each finite $N$. The guide correctly labels the sharp-constant equality as asymptotic. The stale coarse-global nonoptimality disclaimer is absent.

## Portable numerical and assembly checks

The owned checker uses exact integer $Q_k$ recurrence values and direct $\mathcal L_k$ normalization. It cancels the permutation denominator before 90-digit numerical evaluation. All 60 points in global-error-data.json were independently recomputed. The maximum absolute discrepancy is below $2.31\times10^{-17}$. Bisection of the derivative of the odd absolute profile independently gives

$$
c_*=1.165401873183749918861895631439\ldots,
\qquad
C_*=0.395496270090507693120291483372\ldots.
$$

These agree with all stored digits to the checked tolerance. The figure labels and caption match the actual scaled error, parity and matrix sizes. The profile curves have the correct signs. The circles and squares show finite recurrence values rather than a claim of finite equality with the limiting curve.

Of the 31 formal statement and proof blocks extracted from v7, 29 remain byte-identical. The two changed blocks are exactly the old global theorem and its proof, replaced by the stronger result. Four new formal blocks are the one-conflict lemma, its proof, the theorem and its proof. The appended global-error argument is written as appendix subsections. All 140 labels are distinct and every checked reference resolves.

Both PDFs were rebuilt in three passes from the exact frozen source. Their extracted text matches the supplied PDFs. There are no compilation, unresolved-reference, unresolved-citation, overfull or underfull warnings.

All 40 manuscript pages and all eight guide pages were rendered and inspected in contact sheets. Main pages 23, 24, 36 and 37 and guide pages 3 and 7 were also inspected individually for the new formulas, tails, attainment explanation and figure. AV8-E3 was the only layout issue found. The original theorem proofs and figure-data files identified as unchanged are preserved.

The checker accepts an explicit snapshot path and writes its output to an explicit or adjacent owned path. It does not depend on the author's numerical checker. Its output, source hashes, exact source differences, render evidence and this review are frozen under the assembled-v8 prefix.

## Disposition

No mathematical repair is requested. SG-14 and SG-15 are accepted in the assembled v8 source. AV8-E1, AV8-E2 and AV8-E3 remain open against the frozen reading copy until a successor is checked. Historical priority, the separate two-conflict investigation and any later attribution addendum are outside this decision.
