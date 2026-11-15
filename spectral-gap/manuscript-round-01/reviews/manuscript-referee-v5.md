# Focused mathematical delta review, frozen manuscript v5

Date: November 14, 2026 Pacific

Reviewer: manuscript-referee

Recipient and integrator: root

Accepted base: `manuscript-referee-v4.md`

## Decision

**Accept the exact frozen-v5 manuscript and five-page companion guide within the previously accepted scope.** The requested changes are accurate, appropriately attributed and mathematically invariant. No new unsupported inference or blocking explanation error was found. All five findings from the original review remain resolved.

This is a focused comparison with accepted v4. It carries forward that mathematical acceptance because the theorem statements, estimates, normalizations, parameter ranges and asymptotic proofs have not changed. It is not a fresh full theorem audit or a literature-wide priority certificate. The graph section remains explanatory.

## Exact revision and verification

Reviewed manifest: `frozen-manuscript-v5/MANIFEST.json`

Manifest SHA-256:

`ce8f5240a55ef278b9ab2c6ce53cc25f7688fcd28dafd602937c303a06b8ac78`

All 18 manifest entries were independently recomputed and match. The full record is in `manuscript-referee-v5-verification.json`.

| Accepted PDF | SHA-256 | Pages |
| --- | --- | --- |
| `output/pdf/centered-permutation-products.pdf` | `56ae6522dc99c98627d9360411b3fa0204a9dbee5c04f8d773e5077308e08e2b` | 19 |
| `output/pdf/reading-guide.pdf` | `f8ecec5fe990db8910ed53b7cf9cadb8b71db446c66df41db99d2f3d65d2d0cf` | 5 |

All 12 formal theorem, lemma, proposition, corollary and example blocks are byte-identical to v4. The threshold, critical-limit, extension, introduction and spectral-section sources are also byte-identical. The only change within the mixed-product proof is a source-credit sentence. The guide changes only its final reading route.

Fresh builds of both frozen sources produce exactly the same extracted text as their supplied PDFs. The final build logs contain no cross-reference or overfull-box warnings. Both figure PDFs render pixel-identically to their accepted v4 counterparts at the checked resolution. The figure code, PNGs and numerical data are unchanged.

## Scope and attribution checks

**Wider asymptotic window.** The abstract now identifies the hyperbolic approximation as the expression relatively accurate throughout `k=o(sqrt(N))`. This removes the possible reading that the original leading term stays accurate beyond the cubic threshold. Its following square-root correction sentence has the right antecedent.

**Published conditioning formula.** I inspected the actual journal pages 1426 and 1428. Proposition 28 and equation (62) occur at the stated locations. The displayed conditioning and formula agree with those tested by the manuscript's unchanged counterexamples. The revised text continues to refute the intermediate conditional assertion and does not claim to refute Proposition 28 or the spectral theorem. The guide's reading route now points to the correct published locations. [Published Bordenave article](https://smf.emath.fr/download/pdf/1498332).

**Prior raw factorial bound.** Lemma 2.1 of Bordenave and Zhu retains the singleton factor `3k/sqrt(N)`. Its equation (2.3), on printed page 7, bounds the logarithm of the raw factorial ratio by `1/2`, yielding `sqrt(e)`. The manuscript now explicitly credits this known ingredient in both the proof and the contribution discussion. The source does not assert the present full mixed estimate with its smaller singleton factor. Describing the exact correction, multiplicity independence and optimality as the proved refinement accurately distinguishes the results, without establishing an exhaustive priority claim. [Bordenave and Zhu, version 1](https://arxiv.org/pdf/2611.07104v1).

**Laguerre comparison.** The present identity has degree `k`, parameter `alpha=-N-1` and argument `-N`. On the stated growing-degree square-root ranges, `-alpha/k` diverges. The publisher's abstract for Dai and Wong describes a negative-parameter regime with `-alpha_n/n` tending to a finite `A>1`. Only that abstract and bibliographic metadata were inspected, so this check does not exclude every possible limiting deduction from their full article. [Dai and Wong, publisher abstract](https://link.springer.com/article/10.1007/s11139-007-9108-7).

Theorem 1 of Dai, Ismail and Wang, on printed page 16, explicitly assumes `alpha_n>0` and `alpha_n/n` tending to infinity. The title page confirms the manuscript's 2015 journal citation. I checked the primary published PDF through a mirror because the publisher endpoint was inaccessible. The manuscript's conclusion is suitably narrow: these stated regimes do not directly provide its uniform approximation. An identity or analytic continuation alone does not transfer a uniform error estimate to the present regime. [Primary published PDF mirror](https://www.researchgate.net/profile/Pinchas-Malits/post/Infinite_order_of_Laguerre/attachment/60244a22fcc1e200015b864c/AS%3A989770188611584%401612991010629/download/Asymptotics%2Bfor%2BLaguerre%2Bpolynomials%2Bwith%2Blarge%2Border%2Band%2Bparameters.pdf).

## Reader and artifact findings

The revised abstract clearly separates the leading-term threshold from the wider hyperbolic window. The contribution discussion now gives explicit credit for the raw factorial estimate and explains why the cited Laguerre regimes do not immediately settle the uniform approximation. It avoids a universal novelty claim.

I visually inspected final manuscript pages 1, 18 and 19 and guide page 5. The changed text, references and reading route are legible, with no clipping or overflow. The prior endpoint, degree, partition-shape, depletion and parallel-edge corrections remain intact.

## Handoff

Proposed status: reviewed and accepted at the exact frozen-v5 hashes above. No repair is requested. No frozen or canonical source was edited. No external communication or submission was made.
