# Final mathematical acceptance, frozen manuscript v4

Date: November 14, 2026 Pacific

Reviewer: manuscript-referee

Recipient and integrator: root

Base audit: `manuscript-referee-v1.md`

Interim delta review: `manuscript-referee-v3.md`

## Decision

**Accept the exact frozen-v4 manuscript and five-page companion guide within their stated scope.** All five findings from the independent v1 audit are resolved in this revision. No unsupported inference or blocking explanation error remains in the reviewed proof chain.

This acceptance covers the optimal `sqrt(e)` prefactor for the stated class of mixed products, the exact cubic criterion and sharp lower-bound constant, the two critical parity limits, the relative hyperbolic window through `k=o(sqrt(N))`, and the `exp(d/4)` correction at positive square-root scale. It also covers the compactness argument giving uniform relative accuracy of the corrected expression on each bounded square-root range.

The graph section remains explanatory. This decision does not certify a full graph theorem, all subsequent estimates in the cited sources, a convergence rate for the final uniform approximation, or literature-wide novelty.

## Exact revision

The reviewed manifest is `frozen-manuscript-v4/MANIFEST.json`.

Manifest SHA-256:

`75e0b0233130978fc41d9abb2e622e760a35a2395e0e94e6ba09032b7ad3556e`

I independently recomputed all 18 manifest hashes. Every entry matches. The full list of verified paths and hashes is preserved in `manuscript-referee-v4-verification.json`.

| Accepted artifact | SHA-256 |
| --- | --- |
| `output/pdf/centered-permutation-products.pdf` | `a4ecf5f28faac0a37f2d577f982f9f71424a3f4b2e3b32037fca53c426f42398` |
| `output/pdf/reading-guide.pdf` | `28a6f7c25a03c956bb7229de482e7b3d5d7a3ee5128df8cce0f94f4e2104f27e` |
| `guide/reading-guide.tex` | `81081b7b6249b35d85487aa2c66b9e7a30203189cd10cba31108bcb9f627d529` |

Every manuscript source file is byte-identical to its reviewed v3 counterpart. Compared with v3, the only substantive change is the guide's explicit treatment of the first-moment seed and full depletion. The figure PDFs render identically to the reviewed v3 figures.

## Closure of all findings

| Finding | Verified final resolution |
| --- | --- |
| MRF-V1-01, full depletion | Both manuscript and guide now use the first-moment seed only before full depletion. Guide page 2 explicitly says `mu_1=r/(N-r)` is for `r<N` and that full depletion uses only the empty product `mu_0`. |
| MRF-V1-02, regular-graph degree | The regular-graph circle illustration assumes `d>=2`. |
| MRF-V1-03, odd partitions | The guide identifies a single triple and otherwise pairs as the leading odd contribution. It no longer asserts that every odd partition contains a triple. |
| MRF-V1-04, depletion mechanism | The guide correctly distinguishes a vanishing fraction of labels from a nonzero cumulative effect on the number of available pairings. |
| MRF-V1-05, parallel edges | The non-backtracking definition excludes reversal of the same edge and gives the vertex-only criterion only for simple graphs. |

MRF-V1-01 remained open in the interim v3 report because the guide's standalone recurrence paragraph needed its own explicit boundary. The v4 wording resolves that point directly. The closure does not depend on importing a later parameter restriction.

## Evidence retained from the base audit

The v1 report reconstructs the hard steps independently, including the odd availability factor `1/lambda`, the aggregate tail over every block size at least five, convergence in mean after multiplication by the parity indicator, and the compactness argument at both zero and positive limiting square-root parameter. It found these arguments valid. None of those proofs changed in the final revision.

The base review also checked the primary source recurrence, normalized parity recurrences, cubic-scale question, half-edge dimension, and precise scope of the two conditioning counterexamples. Its exact finite calculations corroborate the moment and partition normalizations. Those finite calculations are supplementary evidence, not substitutes for the general arguments.

## Final presentation checks

The supplied final manuscript has 19 pages. The guide has five pages. The manuscript's extracted text is identical to the independently rebuilt and verified v3 text. A fresh build of the v4 guide produces exactly the same extracted text as the frozen guide PDF, with no reported cross-reference or overfull-box warnings.

I inspected the final guide page 2 visually. The endpoint qualification is legible and does not cause clipping or overflow. The other revised explanation passages were checked in v3, and the full guide was inspected in the base audit. The accepted explanation now separates leading partition shapes from all possible shapes, pair-count depletion from label consumption, and the probability input from a full spectral proof.

## Handoff

Proposed status: reviewed and accepted at frozen v4 for the stated mathematical and explanatory scope. All five findings are closed at the hashes above. The v3 report remains an interim record and must not be used as the final acceptance.

No further repair is requested. The integrator may record this decision and deliver the frozen-v4 PDFs. No canonical source was edited by this reviewer.
