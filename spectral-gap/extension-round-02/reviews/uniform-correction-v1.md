# Review of the uniform signed correction

Reviewed 15 November 2026 UTC. Verdict: accept equations (U1) and (U2).

Reviewed synthesis: root/uniform-first-correction-v1.md, SHA256 14ba2a74f0a51bd63bc622a30f0ad4f1bcf0c0c5cc95faa14d3f38e5ae920d5a.

The frozen RATE-1 source hash ed472ce70521c37d59c4e3efc88bf7e883d1a75526023ef2c3a15c57bcd9c581 and saddle source hash c9033ac8ff15bd5265771eaad4d4b7eeeb2b2e19860decfa63e0b2bb8c177da8 both matched. Equation (21) of the latter has the exact form and scope quoted as (U5).

This review checks the synthesis, its use of the frozen inputs, and every new uniformity bridge. It does not repeat the full contour argument behind the saddle estimate. The signed coefficient was independently reconstructed in the CORR-1 review, with its separate transcription addendum.

## 1. The finite rate bound remains valid for every $C>0$

The original RATE-1 theorem states $C\ge1$, but its finite inequality (5) holds for every $2\le k\le N/4$. If $N\ge16C^2$ and $k\le C\sqrt N$, then $k\le N/4$ for any positive $C$. Thus that finite inequality is available.

The substitutions in the constant derivation are valid without a lower bound of one on $C$:

\[
K\le C\sqrt N,\qquad
\eta\le3C^2/4,\qquad
\delta\le C^2.
\]

The terms in the finite polynomial bound have nonnegative coefficients. Extra powers of $\eta$ can therefore be bounded by the same powers of $a=3C^2/4$, including when $a<1$. There is no replacement of a smaller power by a larger power without the appropriate factor.

More explicitly, the terms using $\lambda/m$, $\lambda^3/m^2$, $\lambda^2/m^2$, $\eta/m$, and $\eta/m^2$ are respectively bounded using

\[
\frac43\sqrt C\,N^{-1/4},\quad
\frac{32}{27}C^{5/2}N^{-1/4},\quad
\frac{16}{9}C N^{-1/2},\quad
\frac32 C N^{-1/2},\quad
\frac3N.
\]

These are the identities and comparisons producing the displayed $B_i(C)$.

For the remaining factors, $x=\sqrt{K/N}\le1/2$ gives $\tau=2\delta x\le\delta\le C^2$. Also $\log D_k\le k^2/N\le C^2$. Finally,

\[
r=\frac{k^2}{N}\left(\frac1{2k}+\frac{k}{3N}\right)
\le\frac{C^2}{3},
\]

because $k\ge2$ and $k\le N/4$. All comparisons used for the $A_i(C)$ thus remain valid for $C>0$. An empty finite range causes no problem.

In the formula for $A_1(C)$, every term contains either $\sqrt C$ or $C^{5/2}$ multiplied by a function bounded near zero. Hence $A_1(C)\to0$ as $C\downarrow0$. This vanishing, rather than merely a uniform bound at endpoint one, is what permits the boundary argument.

## 2. Uniform expansion away from zero

Fix $0<d<C$. On $d\sqrt N\le k\le C\sqrt N$, one has, uniformly for large $N$,

\[
K\ge(d/2)\sqrt N,\qquad
\lambda\ge c_d N^{1/4},\qquad
k/N\le1/16.
\]

Here $c_d>0$ follows directly from $\lambda=(2/3)\sqrt{K^3/N}$. Thus the absolute large-$K$ and large-$\lambda$ thresholds in the frozen saddle estimate are met uniformly. Its remainder becomes $O_{C,d}(N^{-1/2})$.

For $t=\sqrt{k/N}$, the first two terms of the positive series for $G$ are $t^4/4$ and $2t^5/15$. Since $2/[j(j-2)]\le1/12$ for $j\ge6$,

\[
0\le N\sum_{j\ge6}\frac{2t^j}{j(j-2)}
\le\frac{Nt^6}{12(1-t)}
=O_C(N^{-1/2}).
\]

Also $\log(1+x)=x+O(x^2)$ uniformly for $x=\sqrt{K/N}\le1/4$. The difference between $\sqrt{K/N}$ and $\sqrt{k/N}$ is zero in the even case and at most $1/(\sqrt N\sqrt K)$ in the odd case. It is therefore $O_d(N^{-3/4})$ on this interval.

Substitution into the frozen saddle estimate gives

\[
\log W_{N,k}
=N^{-1/4}\psi_\epsilon(k/\sqrt N)+O_{C,d}(N^{-1/2}).
\]

The leading function is bounded on $[d,C]$. The inequality $|e^u-1-u|\le u^2e^{|u|}/2$ then yields the asserted uniform signed expansion on this interval. Its error after multiplication by $N^{1/4}$ tends to zero.

The same restricted-interval conclusion also follows from the uniform compact-positive remainder estimates in the independent CORR-1 review. This provides a second check on the coefficient and its parity.

## 3. The lower interval and the order of limits

For each fixed $d>0$, the enlarged finite rate bound implies

\[
\limsup_{N\to\infty}N^{1/4}
\sup_{2\le k\le d\sqrt N}|W_{N,k}-1|
\le A_1(d).
\]

The terms with $A_2(d)$ and $A_3(d)$ vanish after this scaling. At the same time,

\[
\sup_{\epsilon\in\{0,1\},\,0\le c\le d}
|\psi_\epsilon(c)|
\le\frac{\sqrt d}{2}+\frac{2d^{5/2}}{15}.
\]

Let $E_N$ denote the supremum in (U1). Splitting at $d\sqrt N$, applying Section 2 to the upper interval, and using the triangle inequality on the lower interval give

\[
\limsup_{N\to\infty}E_N
\le A_1(d)+\frac{\sqrt d}{2}+\frac{2d^{5/2}}{15}.
\]

This holds for every fixed $0<d<C$. Letting $d\downarrow0$ makes the right side vanish. This proves (U1) without interchanging a limit with an uncontrolled moving endpoint. The argument includes fixed orders and arbitrary changes of parity.

## 4. Exact supremum constant

Write $u=\sqrt c/2$ and $v=2c^{5/2}/15$. They are nonnegative, so $|\psi_0(c)|=|-u+v|\le u+v=\psi_1(c)$. Both summands in $\psi_1(c)$ increase with $c$, so

\[
|\psi_\epsilon(c)|\le\psi_1(C)
\quad\text{for }0\le c\le C.
\]

Equation (U1) therefore gives the upper limit in (U2).

For the lower limit, take the largest odd integer $k_N\le C\sqrt N$. For all sufficiently large $N$ it is an eligible order and

\[
0\le C-k_N/\sqrt N<2/\sqrt N.
\]

Continuity gives $\psi_1(k_N/\sqrt N)\to\psi_1(C)$. Applying the uniform expansion to this sequence gives the matching lower limit. The argument works for every $C>0$ and is unaffected by a zero of the even coefficient.

## 5. Findings and recommendation

- U-REV-01: extending the displayed RATE-1 constants from $C\ge1$ to $C>0$ is justified by their derivation.
- U-REV-02: the frozen saddle estimate is used only where all of its hypotheses hold uniformly.
- U-REV-03: the two-interval argument closes the boundary at zero with the correct order of limits.
- U-REV-04: odd orders attain the exact limiting supremum constant.

No mathematical gap was found in the synthesis. Recommend accepting (U1) and (U2) at the reviewed hash. No numerical evidence is needed for these bridges. No frozen input or canonical file was modified, and no historical-priority conclusion is made.
