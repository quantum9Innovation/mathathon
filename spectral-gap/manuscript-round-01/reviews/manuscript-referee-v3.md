# Mathematical delta review, frozen manuscript v3

Date: November 14, 2026 Pacific

Reviewer: manuscript-referee

Recipient and integrator: root

Base review: `manuscript-referee-v1.md`

## Decision

**Interim decision: accept the main mathematical results in frozen v3. Keep MRF-V1-01 open for the guide until its standalone recurrence paragraph explicitly qualifies the first-moment seed.** The manuscript portion of that finding and the other four findings are resolved.

This status supersedes the provisional full-acceptance wording drafted earlier during the delta review. The guide's displayed square-root estimate implies `r<N`, but the preceding explanation presents the recurrence separately. It should state that boundary directly rather than require the reader to import the later range. Final acceptance is deferred to the next frozen revision.

The accepted mathematical results are the mixed-product bound with optimal universal prefactor `sqrt(e)`, the exact cubic criterion and sharp lower constant, the distinct critical limits for the two parities, the relative hyperbolic approximation through `k=o(sqrt(N))`, and the correction `exp(d/4)` when `k^2/N` tends to positive `d`. The corrected formula is uniformly relatively accurate on each bounded square-root range.

This interim decision preserves the manuscript's limits. It does not assert a new graph eigenvalue theorem, a full audit of either cited graph proof, a rate for the final uniform approximation, or a literature-wide novelty guarantee.

## Exact revision and change audit

The reviewed manifest is `frozen-manuscript-v3/MANIFEST.json`, with SHA-256:

`8c3cdba0e72da72f6265a6aa7c76c2b326113a031412d2e56a8e0c6406374173`

All 18 entries match their recorded hashes. The complete independently verified list is in `manuscript-referee-v3-verification.json`.

I compared every source file with frozen v1. The threshold and critical proofs are byte-identical. The extension proof is unchanged, with only the figure moved. The mixed-product proof changes only its explicit full-depletion seed handling. The graph section adds the degree restriction and the correct edge-based definition of non-backtracking. The guide corrects the leading odd partition description, the depletion explanation, and the statement of the bounded square-root range. Other changes are document metadata, table-of-contents depth, and figure PDF metadata.

No unexamined mathematical change is covered by this acceptance.

## Resolution of findings

| Finding | Resolution in frozen v3 |
| --- | --- |
| MRF-V1-01, full depletion | Resolved in the manuscript, which now uses `mu_1` only when `n-r>=1` and explicitly uses only `mu_0` when `n-r=0`. Still open in the guide's standalone recurrence paragraph, where the seed remains unqualified. Add `r<N` and the empty-product case there. |
| MRF-V1-02, regular-graph degree | The regular-graph illustration explicitly assumes `d>=2`, excluding the false degree-one case. |
| MRF-V1-03, odd partition wording | The guide now says that the leading odd contribution uses one triple and otherwise pairs. This is exactly the coefficient defining its odd leading term. |
| MRF-V1-04, depletion explanation | The guide now distinguishes a vanishing fraction of labels from a nonzero cumulative loss in available pairings. This agrees with `s/m->0` and `s^2/(2m)->d`. |
| MRF-V1-05, parallel edges | Non-backtracking is now defined by forbidding reversal of the same oriented edge. The vertex-only criterion is explicitly limited to a simple graph. The guide's instruction not to reverse an edge is consistent with this definition. |

The square-root proof retains the essential aggregate tail bound. It still proves convergence of the availability error after multiplication by the parity indicator, without imposing independence. The compactness argument still treats both positive limiting square-root parameter and the zero endpoint. None of these steps was weakened during revision.

## Final artifact checks

The frozen manuscript has 19 pages and the guide has five pages. Independent builds from frozen-v3 sources produce exactly the same extracted text as the supplied final PDFs. The final build passes had no reported cross-reference or overfull-box warnings.

I visually inspected the revised guide page 4 and manuscript pages 4, 16, and 17, which contain the endpoint and graph corrections. The inspected pages are legible and have no clipping. Both figure PDFs render identically to their frozen-v1 counterparts despite the metadata changes. The full guide had already been visually inspected in the base review.

| Reviewed artifact | SHA-256 |
| --- | --- |
| `output/pdf/centered-permutation-products.pdf` | `8fefc5b7125e06a7461ad3b2268442a33e71909c467c17b464b60f17b2e712d8` |
| `output/pdf/reading-guide.pdf` | `c774650d484383a4690703ccb6fdf1843774523ff2ec09a515f9184430f8ec30` |
| `manuscript/main.tex` | `08694771364e6185ba02904e6fd0c8f69060673e324b06504fb70fbd682f8f67` |
| `manuscript/sections/mixed.tex` | `6818f564fdaaec4780f0f25a83242e3cb7c7113b8970b9cb45f5520c04b4fe55` |
| `manuscript/sections/extensions.tex` | `cfcc1a97ddfaf96ba50b8dd75f74c689bb482456333bd670e2c67e0f2dd4fe4d` |
| `manuscript/sections/spectral.tex` | `adb5adb7cd75c770ee19b27beae6c1387c1a16ee5dd26bd33534bcc4c4dfe789` |
| `guide/reading-guide.tex` | `444279335171cc084acca94ffb6a5618458528586735619fce08e73c96cfc605` |

## Handoff

Proposed status: main mathematical results reviewed and accepted at frozen v3. Four v1 findings are closed. MRF-V1-01 remains open only for the guide's standalone endpoint wording. Earlier review decisions remain attached to their earlier hashes.

The integrator should add the explicit guide endpoint and freeze a new revision for final delta acceptance. No canonical source was edited by this reviewer.
