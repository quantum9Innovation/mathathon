# Special-function priority audit

Revision 1. November 15, 2026 UTC. Scope: the diagonal sublinear action, sharp square-root correction, and full-range approximation.

## 1. Assessment

No historical firstness claim is supported by this bounded audit. Classical Laguerre results overlap the interior proportional range. More substantially, an exact Whittaker connection places all sublinear orders in Olver's positive-argument parameter range. Its error precision is adequate even after the odd subtraction.

The signed correction at every positive square-root scale follows by an elementary uniform Laplace calculation on classical real integrals. The manuscript's explicit normalization, uniform treatment down to fixed orders, sharp supremum constant, and complete proof remain useful mathematical statements. Those features should be described as the statements proved here, without inferring priority from a parameter mismatch or from a different original notation. The mixed extremal result is outside this audit and requires the separate priority assessment.

## 2. Exact Laguerre specialization

The established identity is

\[
Q_k=(N)_kN^ka_k=k!L_k^{(-N-1)}(-N).
\]

For a paper written as $L_n^{(\alpha_n)}(nz)$, substitute

\[
n=k,\qquad \alpha_n=-N-1,\qquad
A_n=-\alpha_n/n=(N+1)/k,\qquad z=-N/k.
\]

If $k/N\to\rho\in(0,1)$, then $A_n\to1/\rho>1$ and $z\to-1/\rho$. This is an overlapping parameter regime for [Kuijlaars and McLaughlin](https://arxiv.org/pdf/math/0204248v1) and the announced scope of [Dai and Wong](https://doi.org/10.1007/s11139-007-9108-7). It must not be presented as an unstudied negative-parameter regime.

Kuijlaars and McLaughlin's exact finite-limit hypothesis is (7.1). Their Theorem 7.1 treats the polynomial in all relevant regions, with the away-from-contour formula (7.3) uniform on compact subsets of its stated domain. Remark 5.4 and the paragraph preceding Section 7 specify uniformity in $A$ on compact subsets of $(1,\infty)$. In the sublinear range $A_n$ and $|z|$ diverge, while at $k=N$ the ratio tends to one. Neither limiting passage is contained in that stated compactness. This observation limits a direct citation of the theorem, but does not prove a new asymptotic regime.

Dai and Wong's full body was unavailable. The primary abstract specifies a finite limit $A>1$ and expansions on the upper and lower half-planes. The audit does not infer any stronger exclusion from the inaccessible theorem body.

## 3. The Olver route is relevant

The detailed calculation is frozen separately in [OLVER_SPECIALIZATION-v1.md](OLVER_SPECIALIZATION-v1.md). With $b=N/2-k$ and $\mu=(N+1)/2$, the classical connection gives

\[
Q_k=k!e^{-N/2}N^{N/2}
\left\{\frac{M_{b,\mu}(N)}{(N+1)!}
+(-1)^k\frac{W_{b,\mu}(N)}{(N-k)!}\right\}.
\]

All gamma factors are finite, including $k=N$. The formula was checked algebraically and against six small exact cases. Substituting classical Kummer integrals gives two positive real integrals. Their sum applies to even $k$ and their difference to odd $k$.

The published approximation in [DLMF 13.20(iii)](https://dlmf.nist.gov/13.20.iii), attributed there to [Olver (1980)](https://doi.org/10.1017/S0308210500012130), covers $-(1-\delta)\mu\le b\le\mu$ at every positive argument. It therefore covers every $k\le cN$ with fixed $c<1$. The separate note proves that the resulting combined proxy has uniform relative error $O_c(N^{-1/2}\log N)$. This is smaller than the $N^{-1/4}$ correction under audit.

The older error estimate is therefore not an obstruction to classical derivability. The conversion to the manuscript's elementary action and hyperbolic normalization still requires explicit analysis, including the two different prefactors and the odd cancellation. No exact earlier theorem asserting the manuscript's full sharp supremum statement was verified.

## 4. Claim-by-claim result

| Claim | What is established by this audit | What remains outside the verified prior statement |
| --- | --- | --- |
| SG-10, uniform sublinear action and polynomial truncation hierarchy | The action for $k=o(N)$ with $k/N^{1/3}\to\infty$ follows by the ordinary real saddle calculation in the specialization note. Olver's parameter domain also covers the transition and lower orders. | The exact uniform relative statement over every $2\le k\le b_N=o(N)$ needs the central transition and fixed-order patch. No source was verified as stating precisely that normalized theorem. |
| SG-12, signed square-root correction and sharp supremum constant | The signed first coefficient on $d\sqrt N\le k\le C\sqrt N$, for fixed $d>0$, is derived explicitly from the classical integrals in the note. Olver's individual approximation errors remain sufficiently small after the odd difference. | The uniform extension as $d\downarrow0$ and the resulting exact supremum constant require an additional uniform argument. Their absence from the inspected statements does not establish priority. |
| GLOBAL-1, all $2\le k\le N$ | The interior proportional range overlaps known Laguerre asymptotics. The classical exact integral remains valid at $k=N$. | Fixed-compact $A$ uniformity and fixed-$\delta$ Olver bounds do not supply uniformity at $k/N\to1$. The particular all-range formula and rate were not identified as an exact prior theorem. |

At $k=N$, the Laguerre polynomial is also a partial sum of the exponential series, already discussed in Section 1.2 of the Kuijlaars and McLaughlin preprint. The endpoint should not be presented as a new special-function identity.

## 5. Suggested framing

The diagonal results are explicit parity-resolved asymptotics for a classical Laguerre specialization. The paper gives a positive combinatorial representation, quantitative uniform bounds, and a self-contained treatment of the transition and fixed orders. Classical Laguerre and Whittaker asymptotics supply substantial overlap and alternative derivations of the positive-scale action and correction.

Historical firstness for the diagonal formulas remains unverified. The bounded searches and access limitations are not a novelty certificate. A manuscript can state and prove these results without using a firstness claim.

## 6. Scope and dependencies

The audit inspected the primary sources in [SOURCE_TABLE-v1.md](SOURCE_TABLE-v1.md). It also used the frozen exact positive representation from the base extension proof. Prior exposure includes the manuscript's accepted rate, correction, saddle, and global proofs, so the independent calculation in the specialization note is a verification of classical derivability rather than an independent discovery of the coefficients.

The Dunster 1989, 2021, and August 2026 sources have narrower parameter hypotheses than Olver's relevant real-argument result. Their scope mismatches do not justify excluding the Olver connection. No attempt was made to cross an access gate or to contact an author.
