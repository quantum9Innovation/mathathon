# Final claim-specific source assessment

Revision 1. Search and inspection date: 15 November 2026 UTC. This additive audit preserves the earlier frozen packets. It compares the exact mixed extrema SG-E3-A and SG-E4-A and the global error profile GSR-1. It does not certify historical firstness. Prior exposure includes the mixed proofs and the independent GSR-1 proof review. The subsequently proved two-conflict extension was not a separate search target in this pass. The contribution language below describes only the compared claims and does not limit the current manuscript's scope.

## 1. Assessment

The principal new attribution is an exact identification of the depleted polynomial with higher-order derangement polynomials. The publisher's equation, the general specialization proof and symbolic checks are preserved in this directory. The polynomial family itself must be credited as known.

The inspected mixed-moment, permanent and matching statements do not state the exact zero-conflict or one-conflict maximum over the present class of cell patterns, powers and independent colors. The inspected asymptotic statements do not state the particular global cubic error profile or its supremum constant. These are conclusions about the statements listed below, not a claim that no equivalent result exists elsewhere.

The previously established classical Laguerre and Whittaker overlap remains substantial. The diagonal result should be presented as an explicit, uniformly proved comparison for a classical specialization. This search supplies no reason to strengthen the manuscript's historical language.

## 2. Exact claims compared

Let $n\ge2$, let $X$ be the mixed product in the frozen mixed proofs, and let $a,h,b$ denote its number of distinct colored cells, consistent centered singletons and inconsistent centered singletons. Write

$$
P_h(n,s)=h![z^h](1-z)^{n-s}\exp\left(\frac{nz}{1-z}\right).
$$

The first target is the exact maximum

$$
\sup |\mathbb EX|=\frac{n^{-h}P_h(n,a-h)}{(n)_a}
\qquad (b=0,\quad 1\le a\le n,\quad 0\le h\le a).
$$

The second is

$$
\sup |\mathbb EX|=\frac{n^{-h-1}P_h(n,a-h-1)}{(n)_{a-1}}
\qquad (b=1,\quad 2\le a\le n,\quad 0\le h\le a-2).
$$

Each supremum includes arbitrary permitted multiplicities and independent permutation colors, with the displayed parameters fixed. The associated bound for $b\ge1$ multiplies the second right side by $2^{b-1}$ and makes no exact-maximum assertion for $b>1$.

For GSR-1, use exactly $R_k$ and $\mathcal A_{N,k}$ in the frozen proof, equation (1). The target is

$$
\sup_{2\le k\le N}\left|N^{1/3}\left(\frac{R_k}{\mathcal A_{N,k}}-1\right)
-\Phi_{k\bmod2}(k/N^{1/3})\right|\longrightarrow0,
$$

where $\ell(c)=2c^{3/2}/3$, $p_0(t)=t\tanh t$, $p_1(t)=t\coth t-1$, and

$$
\Phi_\epsilon(c)=\frac{3(2\epsilon-1)}{4c}\bigl(p_\epsilon(\ell(c))-\ell(c)\bigr).
$$

The resulting optimal relative error constant for that particular approximation is

$$
\mathfrak C=\max_{c>0}\frac3{4c}\left(1-\frac{2\ell(c)}{e^{2\ell(c)}-1}\right)
=0.3954962700905\ldots,
$$

with a unique maximizing scale $c_*=1.1654018731837\ldots$. These constants are not asserted to be optimal over all possible approximations.

The exact target hashes are in `MANIFEST-v1.json`.

## 3. The additional polynomial attribution

Kim, Kim, Jang and Kwon, *A note on some identities of derangement polynomials*, Journal of Inequalities and Applications 2018, article 40, [DOI 10.1186/s13660-018-1636-8](https://link.springer.com/article/10.1186/s13660-018-1636-8), define on page 9, equation (2.22),

$$
(1-t)^{-r}e^{xt}=\sum_{j\ge0}d_j^{(r)}(x)t^j/j!,\qquad r\in\mathbb N.
$$

Consequently

$$
P_h(n,s)=(-1)^h d_h^{(n-s-h+1)}(-n).
$$

The order is positive throughout $h+s\le n$. It depends on $h$, so this is a degree-by-degree identification. The general proof is in the preserved `DERANGEMENT_SPECIALIZATION-v1.md`. The recurrence-versus-coefficient symbolic check gives zero difference identically in $n,s$ for $h=0,\ldots,12$. The downloaded publisher PDF and a visual check of page 9 confirm the definition. Equations (2.23) and (2.24) define a different family called the $r$-derangement polynomials, which should not be substituted for (2.22).

This adds a known-polynomial citation. The definition and the inspected identities following it do not provide the optimization over mixed supports, exponents and colors.

## 4. Mixed-moment and permanent comparisons

| Inspected primary statement | Comparison with the exact extrema |
| --- | --- |
| Collins and Nagatsu, published Proposition 3.3, Theorem 3.6, and Lemma 5.1 | These supply the exact diagonal recurrence, a centered Weingarten reformulation and reduction of powers. They remain attributed ingredients. The inspected statements do not identify either mixed extremum. |
| Bordenave and Zhu, arXiv:2611.07104v1, Lemma 2.1, equations (2.1) and (2.2), PDF page 7 | The mixed estimate has a universal constant, the factor $2^b$, and a power of $3k/\sqrt N$, with $k\le\sqrt N$. It does not retain $P_h(n,s)$ or state attainment. Its separate repeated-edge approximation is a different assertion. |
| Han and Niles-Weed, arXiv:2607.23836v1, Theorem 1.2, and arXiv:2408.09341v3, Lemma 5.5 | Both give bounds for the same zero-depletion diagonal moments after the explicit permanent specializations in the earlier frozen audit. They do not state the present mixed maxima. This conclusion retains that earlier audit's journal-access limits. |
| Coste, Lambert and Zhu, arXiv:2204.00524v3, Proposition 5.7, pages 16 and 17 | The quantity is an uncentered product of entries of a sum of independent permutation matrices, with threshold indicators and a fixed number of entries. Its big-O bound is not the displayed centered extremum. |
| *A strict four-row permanent inequality and permutation moments*, dated 26 September 2026, Theorem 1.1, page 2, and proof, pages 3 and 4 | The theorem concerns four nonnegative functions under a law on $S_4$ near uniform with exact uniform marginals. The stated exponent is existential and not optimized. It does not state either mixed extremum or the diagonal asymptotic profile. |
| Bristiel and Caputo, arXiv:2109.06009v3, Corollary 1.14, page 8 | The sharp constant concerns a permanent of a nonnegative matrix with prescribed row norms. It does not preserve the centered signs or the parameters $h,b$ of the present problem. |
| Sra, *A sharp Brégman-Minc bound for permanents*, author version 1, Theorem 1.1, Corollary 1.2, Theorem 5.1 and Corollary 5.2 | These concern nonnegative permanents and summed matching coefficients with row norms. The rectangular and coefficientwise bounds are genuine nearby results, but the inspected statements do not state the fixed-cell centered extrema. |

The nonnegativity distinction is concrete. For a uniform permutation of four points, $Y=M_{11}-1/4$ has expectation zero, whereas $\mathbb E|Y|=(1/4)(3/4)+(3/4)(1/4)=3/8$. Thus applying a nonnegative permanent bound after taking absolute values loses even the cancellation in the case $a=h=1,b=0$. This limits that direct reduction. It does not rule out a different deduction from those papers.

Gonçalves, arXiv:2609.31979v1, Theorem 1 and Corollaries 2 and 3, compares sorted counts of matching positions of rearranged words under majorization. The inspected statements concern sums of matches and sampling distributions, rather than products of specified centered cells. No broader exclusion is inferred.

## 5. The cubic profile and nearby asymptotics

The earlier special-function audit already establishes overlapping classical machinery. In the original Laguerre variables, $Q_k=k!L_k^{(-N-1)}(-N)$. Kuijlaars and McLaughlin's finite negative-parameter ratio range overlaps $k/N$ in compact subsets of $(0,1)$. The Whittaker connection and the formulas recorded in DLMF 13.20(iii), attributed to Olver, also cover every $k\le cN$ for fixed $c<1$. This pass does not repeat that search or claim that the cubic range is historically new.

Three additional accessible sources were inspected for a direct error-profile statement.

- Ghorbani, Hassani and Moshtagh, *Moments and asymptotic expansion of derangement polynomials in terms of Touchard polynomials*, Theorem 1.1, equation (1.7), page 834, gives an explicit finite remainder for $\widehat D_m(x)=m!\sum_{j=0}^m x^j/j!$. At the endpoint, $Q_N=(-1)^N\widehat D_N(-N)$ by the coefficient identity above with order one. Substituting $m=N,x=-N$ into their remainder and dividing by $N^N$ gives $T_{r+1}(N)/N^{r+1}$ for a fixed truncation index $r$. Since $T_{r+1}(N)=\sum_j S(r+1,j)N^j$ and $S(r+1,r+1)=1$, this tends to one. The inspected remainder therefore does not give a small relative error under that substitution. The endpoint polynomial identity remains classical.
- Nicolaescu, *Derangements and asymptotics of the Laplace transforms of large powers of a polynomial*, Theorems 1.3 and 1.4, page 120, gives inverse-power expansions for a fixed polynomial raised to a growing power at fixed Laplace parameter. The current gamma integral contains $v^{N-k}(N-v)^k$ with a moving root and changing multiplicities. Rescaling $v=Nt$ instead moves the Laplace parameter. The inspected fixed-data theorem does not state uniformity for this joint limit.
- Sun and Xu, *Exploring the Higher-Order Moment Behavior of Certain Probability Distributions by Combinatorial and Asymptotic Analysis*, Section 4, Theorem 2 and equations (27) to (32), treats high central moments of a fixed gamma law using a fixed-shape Darboux expansion. Here the gamma shape is $N-k+1$ and the centering point is $N$, so both the law and the displacement change. The inspected statement does not give the present two-parameter profile.

These comparisons identify scope and exact substitutions. None is an assertion that the full classical literature cannot yield the result. No inspected statement in this additive pass gives the precise $\Phi_\epsilon$, the full-range supremum limit, or the unique maximizing scale. Historical equivalence after further specialization remains unverified.

## 6. Recommended contribution language and limits

The paper determines exact finite mixed-moment extrema when the number of inconsistent centered singletons is zero or one, allowing arbitrary permitted multiplicities and independent permutation colors. The depleted polynomial is a classical Laguerre specialization and is also a higher-order derangement polynomial. On the diagonal, the paper gives an explicit parity-dependent comparison through all orders and determines the optimal error profile and supremum constant for that approximation. These diagonal formulas are developed within classical Laguerre and Whittaker asymptotics.

Dai and Wong's journal body, the related CityU thesis body, the earlier Han and Niles-Weed journal body and the original Olver article body remain uninspected as recorded in the existing packets. No blocked route was retried and no access form was accepted. An additional gamma-transformation article was available only through publisher preview metadata, so it is logged as an unverified lead rather than excluded. The full four-row paper was downloaded, but only its introductory statements, permanent theorem and proof were substantively assessed. The shuffle application was outside this task.

The search ends with a source identification and a bounded statement comparison. It supplies no firstness certificate. The integrator should retain the existing cautious historical framing and add the verified higher-order derangement attribution.
