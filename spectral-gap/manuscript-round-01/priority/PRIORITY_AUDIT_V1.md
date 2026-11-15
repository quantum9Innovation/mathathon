# Priority and citation audit, revision 1

Task SG-M2. Owner: source investigator. Intended recipient: problem 21 integrator. Checked November 14, 2026 Pacific, with source inspection continuing after 03:00 UTC on November 15. This revision audits attribution and scope. It does not independently certify every mathematical step of the manuscript or extension.

## Finding

The exact cubic threshold and the parity-dependent transition factors are defensible contribution candidates. Collins and Nagatsu explicitly posed the scaling question in the published article. Their exact moment formula, leading terms, positive recurrence, both normalized error recurrences and Kummer representation are prior results. The mixed-product estimate already exists in Bordenave and later work. The present contribution there is a direct proof with an explicit prefactor and improved dependence on the number of distinct cells.

No exact duplicate of the threshold equivalence, the hyperbolic transition formulas, the proposed relative extension to $k=o(\sqrt N)$, or its $\exp(d/4)$ boundary correction was located in the inspected sources. This is a bounded search result, not a certificate of historical priority. The source identities and the published question are verified more strongly than that negative search result.

The full pinpoint map and version reconciliation are in [SOURCE_MAP.md](SOURCE_MAP.md). Search terms and the screened literature are in [SEARCH_LOG.md](SEARCH_LOG.md). The minimal manuscript bibliography is [references.bib](references.bib).

## Load-bearing claims

| ID | Claim or proposed wording | Verdict | Primary evidence and required boundary |
| --- | --- | --- | --- |
| P-01 | The published paper asks whether the cubic scale is optimal | Supported | Collins and Nagatsu, Remark 3.4, printed page 473: “It would be interesting to check whether this is the optimal scaling.” The preceding sentence identifies $k^3\le CN$ |
| P-02 | The row-sum recurrence or the normalized parity recurrences are new | Unsupported | Equation (16) and both displayed recurrences for $\varepsilon_{2l}$ and $\varepsilon_{2l+1}$ are already on printed page 472. The frozen input correctly credits them |
| P-03 | The leading terms are relatively accurate exactly for $k^3/N\to0$, and comparable exactly for $k^3/N=O(1)$ | Supported as a precise answer to the cited question, conditional on the separately reviewed proof | Proposition 3.3 already proves sufficiency. The proposed lower bound $R_k-1\ge2k^3/(27N)$ supplies necessity. Do not call cubic scaling itself a newly discovered sufficient regime |
| P-04 | The even and odd ratios have distinct hyperbolic critical factors | No duplicate located in inspected sources | Neither Proposition 3.3 nor Remarks 3.4 and 3.5 states these factors. The nearby sources screened below do not give the same theorem. Historical priority remains provisional |
| P-05 | The mixed centered permutation-product estimate is first established here | Overstated | Bordenave Proposition 28 states the original estimate. Bordenave and Collins Proposition 22 repeats it and credits Bordenave. State a direct quantitative proof and strengthened cell-count dependence |
| P-06 | The direct estimate supplies the probabilistic input of Brito, Dumitriu and Harris Lemma 7 | Supported with a version qualifier | Definition 5 and Lemma 7 are on preprint PDF page 15. Its proof on page 16 identifies a uniform permutation block of size $nd_1=md_2$ and invokes Bordenave Proposition 28. In the final article this is Definition 5.5 and Lemma 5.6, printed pages 244 and 245 |
| P-07 | A displayed conditional assertion in Bordenave is false | Supported for the exact cited preprint assertion | Equation (62), arXiv:1502.04482v4, PDF page 38. The two finite counterexamples in frozen source findings address its stated conditioning. This does not refute Proposition 28 or a spectral theorem |
| P-08 | The positive generating function is a new special-function identity | Unsupported | Collins and Nagatsu Remark 3.5 plus the classical Laguerre relation and generating function imply the identity. Credit those sources and present the positive block expansion as the useful reformulation |
| P-09 | The wider relative window and square-root correction are established prior results | No duplicate located, independent written-proof review accepted | The statements are in extensions/hyperbolic-window-v1.md, hash recorded below. The searched special-function regimes differ from this one. Historical priority remains provisional |
| P-10 | These moment estimates prove a new spectral-gap theorem | Unsupported by this packet | The frozen proofs supply an input used in earlier spectral arguments. No new final spectral statement or complete new application bridge is part of this audit |
| P-11 | The mixed theorem has sharp universal prefactor $\sqrt e$ | Supported by the written proof and recorded independent reconstruction, historical priority separate | proof/permutation-proof-v3.md proves the exact factor $F_N(a-h)$ and takes compatible uncentered cells with $N=a^2$ to attain the limiting prefactor. This does not assert optimality of the singleton factor or the full pointwise inequality |

## Exact source comparison

Write $a_k(N)=\mathbb E\prod_{i=1}^k(M_{ii}-1/N)$ for a uniform permutation matrix, with $0\le k\le N$. Collins and Nagatsu Proposition 3.3 gives

$$
a_k(N)=\sum_{j=0}^k\binom{k}{j}\frac{(-1/N)^{k-j}}{(N)_j}
$$

and the parity-dependent leading terms used in the manuscript. It proves relative error $O(k^3/N)$ when $N\gg k^3$. Its proof gives the positive recurrence and normalized error recurrences before Remark 3.4 asks about optimal scaling. The newly proposed inference is to retain positive terms to obtain a necessary lower bound, then identify the transition and its larger relative range. This distinction is substantive, since relabeling a prior recurrence as new would obscure the actual contribution. [Published source](https://alco.centre-mersenne.org/articles/10.5802/alco.480/)

For the mixed estimate, Bordenave's original singleton factor is $3k/\sqrt N$, where $k$ is the total product length and $a\le k$ is the number of distinct requested cells. The new factor

$$
\beta_{N,a}=\frac{\sqrt{a-1}}{\sqrt N-\sqrt{a-1}}
$$

has order $\sqrt{a/N}$ uniformly when $2\le a\le\sqrt N$. The current proof revision gives the stronger exact-factor inequality

$$
|\mathbb EP|\le 2^bN^{-a}\beta_{N,a}^h F_N(a-h),
\qquad F_N(q)=\frac{N^q}{(N)_q},\qquad 2\le a\le N.
$$

When $a^2\le N$, it gives $|\mathbb EP|\le\sqrt e\,2^bN^{-a}\beta_{N,a}^h$. The universal prefactor $\sqrt e$ cannot be reduced for the stated class of arbitrary mixed products. Compatible uncentered cells with $N=a^2$ have normalized expectation $F_{a^2}(a)\to\sqrt e$. This replaces the valid but weaker prefactor $e$ in the starting input. The proof is independently reconstructed in reviews/mixed-v3-integrator-review.md. No exact duplicate of this sharpened formulation was located in the bounded search.

This recovers an existing type of estimate and improves its quantitative cell-count dependence. In particular, when $k=a$, the singleton factor improves from order $a/\sqrt N$ to order $\sqrt{a/N}$. It does not establish the mixed-product phenomenon for the first time. The consistency and multiplicity definitions must remain aligned with the original statements. Collins and Nagatsu's Lemma 5.1 already gives affine reduction of repeated centered entries, while their Remark 4.3 addresses a cubic-range relative coefficient asymptotic. Neither is the exact-factor mixed bound above. [Bordenave Proposition 28](https://arxiv.org/abs/1502.04482v4), [Bordenave and Collins Proposition 22](https://annals.math.princeton.edu/wp-content/uploads/annals-v190-n3-p03-s.pdf), [Collins and Nagatsu, pages 476 and 477](https://alco.centre-mersenne.org/articles/10.5802/alco.480/)

Brito, Dumitriu and Harris use a bipartite matching matrix. After ordering the two half-edge classes, its off-diagonal block is a uniform permutation matrix on $|E|=nd_1=md_2$ labels. The centered block subtracts the all-ones matrix divided by $|E|$. Reversing the orientation of the other block yields precisely the single-permutation model needed for preprint Lemma 7, which is published Lemma 5.6. Bordenave Proposition 11 concerns unrestricted pairings and is not the cited statement for this reduction. [Brito, Dumitriu and Harris, preprint PDF pages 15 and 16](https://arxiv.org/abs/1804.07808v6), [published pages 244 and 245](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/FF0544B9780460143733B7A5317D6CC1/S0963548321000249a.pdf/spectral-gap-in-random-bipartite-biregular-graphs-and-applications.pdf)

The correction should be confined to the displayed conditional argument in the specified Bordenave preprint. A shared requested row can reveal the target indicator already. Even for two disjoint requested cells, conditioning on both an image and a preimage can expose two arrows, although the printed denominator removes only one. The new compatible-set proof bypasses this issue by conditioning on an explicitly specified partial permutation. Do not imply that the original theorem is false, that this is the first historical observation of the issue, or that the journal version has independently been checked for the identical equation.

## Classical identities and the extension

Collins and Nagatsu Remark 3.5 identifies

$$
a_k(N)=(-1/N)^k\,{}_1F_1(-k,-N,-N).
$$

With falling factorial notation in $(N)_k$, put $Q_k=(N)_kN^ka_k$. The standard Laguerre identity gives

$$
Q_k=k!L_k^{(-N-1)}(-N),\qquad 0\le k\le N.
$$

The classical generating function therefore gives the formal extension

$$
\sum_{k\ge0}\frac{Q_kz^k}{k!}
=\exp\left(N\left[\frac{z}{1-z}+\log(1-z)\right]\right)
=\exp\left(N\sum_{j\ge2}\frac{j-1}{j}z^j\right).
$$

Only the coefficients through $k=N$ represent permutation moments. The extension proof explicitly distinguishes its polynomial continuation from those moments. Positive weights $N(j-1)(j-1)!$ for blocks of size $j$ then follow by coefficient extraction. This is an elementary specialization and interpretation of known formulas. It is useful without a novelty claim about the identity. [DLMF 18.5.12](https://dlmf.nist.gov/18.5.E12), [DLMF 18.12.13](https://dlmf.nist.gov/18.12.E13)

There is also an elementary inverse-gamma interpretation. If $X$ has inverse-gamma density $x^{-N-2}e^{-1/x}/\Gamma(N+1)$ on $x>0$, substitution $u=1/x$ gives $\mathbb E X^j=1/(N)_j$ for $0\le j\le N$. Thus $a_k=\mathbb E(X-1/N)^k$. This calculation is self-contained and should be presented as an interpretation, not as a newly discovered distributional fact.

The extension's normalization uses $K=2\lfloor k/2\rfloor$ and $\lambda=(2/3)\sqrt{K^3/N}$. Its $H_k$ is $\cosh\lambda$ for even $k$ and $\sinh\lambda/\lambda$ for odd $k$. The exact proposed claims are

$$
\left(1-\frac{4k^2}{3N}\right)H_k\le R_k\le e^{4k^2/N}H_k
\quad (2\le k\le N/4)
$$

and $R_k/H_k\to e^{d/4}$ if $k^2/N\to d\in(0,\infty)$. They imply relative accuracy for all $k=o(\sqrt N)$ and the corrected uniform approximation on $k\le C\sqrt N$. The audit searched these exact scalings and factors, together with the Laguerre and inverse-gamma formulations.

Extension input: `extensions/hyperbolic-window-v1.md`, SHA256 `73de96b41b7fba59454795f14bf1fe6160f8eee1391553bf980f3f29f4eba68a`. Its exact revision was accepted in reviews/extension-review-v1.md, SHA256 `85300732089208d4fc745b5e6b6c973aa767a64f0dc0c481a243d19dc9508b91`. That is the independent review record, not an additional proof audit by this source investigator.

## Nearby literature and limits of exclusion

The following comparisons are scope checks, not full audits of those papers.

| Source inspected | Relevant scope | Relation to the proposed theorem |
| --- | --- | --- |
| Lopez and Temme, *Approximations of orthogonal polynomials in terms of Hermite polynomials*, 1999, printed page 132 | Large parameters with degree $n$ fixed | Does not directly establish the growing-degree cubic or square-root windows |
| Kuijlaars and McLaughlin, *Riemann-Hilbert analysis for Laguerre polynomials with large negative parameter*, 2001, introduction and main regime | $-\alpha_n/n\to A>1$ with finite $A$ | Here $\alpha=-N-1$ and degree $k=o(\sqrt N)$ give $-\alpha/k\to\infty$ |
| Dai, Ismail and Wang, *Asymptotics for Laguerre polynomials with large order and parameters*, 2015, publisher-indexed Theorem 1 | Positive parameters $\alpha_n>0$ with $\alpha_n/n\to\infty$ | Sign differs. Full text was not retrieved through the publisher, so exclusion is limited to the inspected theorem |
| Borwein, Borwein and Crandall, *Effective Laguerre Asymptotics*, 2008, abstract and introduction | Degree tends to infinity with the parameter pair fixed | Our parameter pair grows with $N$. The cited fixed-pair asymptotic is not directly applicable |
| Eichelsbacher and Knichel, *Moment estimates of Rosenthal type via cumulants*, arXiv:1901.04865v1, Theorem 1.1 and its proof | General moment bounds from cumulant estimates, with degree-dependent constants and a classical partition formula | Relevant general method. No exact permutation threshold, parity transition, or square-root correction appears in the inspected main result |
| Bordenave and Collins, *Norm of matrix-valued polynomials in random unitaries and permutations*, arXiv:2304.05714v2 | Strong norm estimates, with permutation estimates in Section 6 | No exact diagonal-moment transition theorem identified in the checked passages |
| Collins and Nagatsu, *Smooth Multi-Trace Statistics of Classical Ensembles*, arXiv:2602.04614v1 | Smooth multitraces of classical compact-group and Gaussian ensembles | Not the centered symmetric-group diagonal observable in the inspected statements |
| Liu, Ippoliti and Ho, *Coherence-induced deep thermalization transition in random permutation quantum dynamics*, arXiv:2510.18369v2 | Appendix A.1 invokes the uncentered permutation Weingarten formula | Its transition concerns quantum-state coherence. It does not state these centered diagonal-moment transitions |
| Nagata and Suzuki, *Growing-time trace fluctuations and self-averaging form factors of Grover walks on random lifts*, arXiv:2610.36320v1 | Section 1.6 cites Collins and Nagatsu among permutation moment methods | The inspected main results concern logarithmic-time trace statistics, not the present moment-order scale |

Other searches included inverse-gamma moments, general high central moments, cumulant normal approximation, and forward title or arXiv-ID queries. The Doring, Jansen and Schubert survey was used to locate the primary Eichelsbacher and Knichel paper. Gao and Wormald's high-moment normality criterion concerns noncentral or factorial moment input. Sun and Xu's 2026 high-moment article keeps distribution parameters fixed and compares central with raw moments. These checks reduce obvious nearby ambiguity without excluding every reformulation in the literature.

The audit did not obtain an exhaustive citation database export, inspect every cited special-function monograph, or establish that no general uniform theorem can be specialized to this regime. Search indexing may miss recent or differently phrased work. No author correspondence was sent. A claim such as “the first sharp theorem of this kind” would exceed the evidence.

## Contribution paragraph for integration

We determine the exact range of relative accuracy of the parity-dependent leading terms of Collins and Nagatsu. The ratio tends to one precisely when $k^3/N\to0$, and remains bounded precisely when $k^3/N$ remains bounded, answering the scaling question in their Remark 3.4. At the cubic scale, the even and odd ratios converge to distinct hyperbolic factors. The argument uses their exact formula and positive recurrence, including their normalized parity recurrences. A separate compatible-set argument gives a direct mixed-product estimate with exact factorial correction $F_N(a-h)$ and a factor of order $\sqrt{a/N}$ per isolated centered singleton. In the range $a^2\le N$, its universal prefactor is the optimal constant $\sqrt e$. This recovers Bordenave Proposition 28 and the probabilistic input of Brito, Dumitriu and Harris Lemma 5.6, numbered Lemma 7 in their preprint.

The hyperbolic approximation remains relatively accurate for $k=o(\sqrt N)$, with explicit finite bounds. At $k^2/N\to d$, a common multiplicative correction $e^{d/4}$ appears for both parities. A positive partition expansion, obtained from the classical Laguerre generating function, explains the roles of pairs, triples and four-element blocks.

This paragraph describes mathematical content without asserting exhaustive priority. It should cite the published Collins and Nagatsu paper at its first sentence and the three original estimate papers where the mixed-product comparison is made.

## Handoff

- Base packet: RUN_CONTRACT.md and frozen inputs in inputs/MANIFEST.json.
- Claims affected: SG-01 through SG-05 attribution and source identification. EXT-A, EXT-B and the refined mixed theorem have accepted independent written-proof reviews recorded separately. Their historical priority remains provisional.
- Proposed status: mark the source identities, published question and version mapping verified. Keep historical priority provisional after bounded search.
- No shared ledger or manuscript file was edited by this task.
- Requested next action: integrate the contribution paragraph and bibliography, retain the stated scope boundaries, and preserve the links to the exact accepted proof revisions.
- Stopping reason: primary-source identification and bounded nearby search are complete enough for manuscript integration. Further broad search has diminishing value within this round.
