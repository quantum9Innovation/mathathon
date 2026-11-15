# Pre-submission priority assessment

Checked November 14, 2026 Pacific. This report extends the [frozen first audit](../priority/PRIORITY_AUDIT_V1.md). Earlier search evidence remains preserved at its original hashes.

## Decision

No exact duplicate of the quantitative refinements was located in the inspected sources. The manuscript may state its proved formulas and its answer to Collins and Nagatsu's published scale question. Historical priority remains provisional. The broader claim that these are the first equivalent asymptotics anywhere in the literature is not supported by this search.

The original mixed estimate, exact moment formula, base and normalized recurrences, leading coefficients and special-function identities remain explicitly attributed. This pass also located Bordenave and Zhu's prior raw factorial bound F_N(a)<=sqrt(e). The manuscript now cites it. The contribution is the refined full mixed estimate and its sharpness, not first discovery of that elementary factorial inequality. Another new paragraph distinguishes the closest Laguerre regimes and avoids treating analytic continuation as a transfer theorem for uniform errors.

## What this pass adds

| Source | Inspection and result | Consequence |
| --- | --- | --- |
| Bordenave, published article, DOI 10.24033/asens.2450 | Complete publisher PDF. Proposition 28 is on printed page 1426. The exact conditioning assertion is equation (62) on page 1428 | The two examples concern the published formula too. The prior preprint-only limitation is resolved. No claim that the theorem is false or that the defect was first noticed here |
| Bordenave and Zhu, arXiv:2611.07104v1, November 4, 2026 | Lemma 2.1 and equation (2.3), printed page 7. The mixed estimate keeps the original 3k/sqrt(N) factor and its raw case explicitly bounds F_N(a) by sqrt(e) | Material attribution overlap. Credit the raw factorial estimate. The refined beta singleton factor, exact F_N(a-h) mixed correction and diagonal transition formulas were not found in the inspected statements |
| Dai, Ismail and Wang, Journal of Approximation Theory 193 (2015), 4 to 19 | Full-text extraction of the primary paper, introduction and Theorem 1 on printed page 16, with the following finite-ratio case. The theorem assumes positive alpha and alpha divided by degree tending to infinity | Our alpha=-N-1 has the opposite sign. The inspected theorem does not directly establish the manuscript's approximation |
| Dai and Wong, Ramanujan Journal 16 (2008), 181 to 209 | Publisher abstract and bibliography. Its announced negative-parameter regime has minus alpha divided by degree tending to a finite A>1. The publisher full text remained unavailable without subscription | This announced regime differs from our diverging ratio. Exclusion is limited to the stated regime, not an unread theorem or every possible limiting deduction |
| Cardin, de Guise and Quesada, Haarpy, JOSS 11(124), 11002 (2026) | Complete four-page software paper, permutation-module documentation and its linked source. The module cites Collins and Nagatsu and computes exact centered permutation integrals | Known exact formulas have an active symbolic implementation. No growing-order threshold, hyperbolic approximation or square-root correction was found in these inspected materials |
| Liu, Ippoliti and Ho, Physical Review Letters 136, 100404 (2026) | Current arXiv metadata identifies version 2, revised March 14, 2026, as the same version whose Appendix A.1 was inspected in the first audit | The forward citation was not an uninspected new version. Its coherence transition remains a different observable |

An [independent source review](INDEPENDENT_SOURCE_REVIEW.md) checks Bordenave and Zhu and rechecks the published conditioning examples. It identified the raw-factorial overlap above. The integrator separately read the primary statement before adding the citation.

After that review was frozen, the complete versioned Bordenave and Zhu PDF was retrieved. Its identity and equation (2.3) on page 7 were visually checked in a [separate addendum](reviewer/BZ_PDF_ADDENDUM.md). This closes the earlier local-access limitation for that paper without changing the original review. The source PDF SHA256 is `9fb02688bdd3e3cba1663d101aed5ba9704d5bc3779f6192f81eb8f491113b0d`.

## Parameter comparison

The manuscript uses

$$
(N)_kN^k a_k(N)=k!L_k^{(-N-1)}(-N).
$$

Thus its degree is k, its Laguerre parameter is alpha=-N-1, and its argument is -N. If k grows with k<=C sqrt(N), then -(alpha)/k tends to infinity. A finite negative-parameter ratio, a positive parameter, and fixed-degree expansions are different hypotheses. The existing identities can suggest other derivations, but do not by themselves justify uniform remainders for this growing degree and negative parameter. This is a scope comparison, not a claim that a special-function approach is impossible.

The first audit also inspected the relevant statements of Lopez and Temme, Kuijlaars and McLaughlin, Borwein and coauthors, Eichelsbacher and Knichel, Bordenave and Collins, and recent permutation papers. Those assessments remain bounded by the passages and access levels recorded there.

## Forward-search coverage and access limits

The OpenAlex record for the published Collins and Nagatsu paper is W7159674822. Its cited-by query returned one indexed work, the Liu, Ippoliti and Ho article. Direct title searches additionally located Haarpy and other papers recorded in the first audit. The mismatch demonstrates why the citation count cannot be treated as complete coverage.

The Semantic Scholar citation endpoint returned HTTP 429. Publisher access to Dai and Wong's full paper was unavailable. Dai, Ismail and Wang's theorem was read through a searchable copy of the primary PDF, while direct retrieval of that PDF and a page screenshot failed. Its sign hypothesis and following finite-positive-ratio case were legible in the text. No claim of a visual or local-byte inspection of that PDF is made.

These are limits on the audit. They do not create gaps in the manuscript's self-contained proofs. A final specialist check for equivalent special-function formulations remains a sensible external pre-submission review, especially if asserting historical priority more strongly than the current wording.

## Primary links

- [Bordenave published full text](https://smf.emath.fr/download/pdf/1498332) and [journal comparison record](BORDENAVE_JOURNAL_CHECK.md).
- [Dai, Ismail and Wang DOI](https://doi.org/10.1016/j.jat.2014.03.009) and [inspected primary PDF copy](https://www.researchgate.net/profile/Pinchas-Malits/post/Infinite_order_of_Laguerre/attachment/60244a22fcc1e200015b864c/AS%3A989770188611584%401612991010629/download/Asymptotics%2Bfor%2BLaguerre%2Bpolynomials%2Bwith%2Blarge%2Border%2Band%2Bparameters.pdf).
- [Dai and Wong publisher record](https://link.springer.com/article/10.1007/s11139-007-9108-7).
- [Haarpy paper](https://joss.theoj.org/papers/10.21105/joss.11002.pdf), [permutation documentation](https://haarpy.readthedocs.io/en/latest/code/permutation.html) and [module source](https://haarpy.readthedocs.io/en/latest/_modules/haarpy/permutation.html).
- [Liu, Ippoliti and Ho version record](https://arxiv.org/abs/2510.18369v2).
- [Bordenave and Zhu, exact version](https://arxiv.org/abs/2611.07104v1) and [Lemma 2.1](https://arxiv.org/html/2611.07104v1#S2.SS1).

## Allowed contribution wording

The paper gives a direct proof and quantitative refinement of the mixed estimate requested in problem 21. It proves the exact cubic criterion for the relative accuracy of the known diagonal leading terms, identifies parity-dependent hyperbolic factors, extends their relative accuracy to k=o(sqrt N), and determines the common exp(d/4) correction at k^2/N tending to d. The corrected formula is uniform on bounded square-root ranges. The classical formulas and recurrences remain credited to prior work. No improved graph eigenvalue theorem or exhaustive priority certificate is asserted.
