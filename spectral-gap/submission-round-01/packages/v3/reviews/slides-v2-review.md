# Submission slides v2, independent review

Date: November 15, 2026 Pacific.

Decision: Accept the exact slide source, PDF and speaker notes below for mathematical coverage and presentation layout. Author identity remains pending. This is not authorization to submit or acceptance of an uninspected ZIP archive.

## Exact targets

| Artifact | SHA256 |
| --- | --- |
| `slides/problem21-slides.tex` | `34f0692c9584b2bc436bed067ff8bca14140068008b02b4d04345e95c6b292cb` |
| `slides/problem21-slides.pdf`, 16 pages | `97545aed17874c223e54dedc7126cd490c4fb0cd97f7a53443a684d18640643f` |
| `slides/speaker-notes.md` | `91f45a209df0c6eed187fb25d7a116f9005cf5264d53b010f4e417c33145ae45` |
| Covering report `frozen-v1/report.tex` | `5acdbad9d59e8126bf03c4619ce3e43c0e444623d5fdb592178b54b033edc99d` |
| Covering report `frozen-v1/report.pdf` | `d0c9e2d24bcd244463a89e10e3285bebf4600ec80f034d78ee857af2bdd4bcfe` |

The deck has 14 main slides and two optional backups. The notes plan 17 minutes 40 seconds of speaking time. This is a presentation plan, not a measured rehearsal.

## Coverage in the report

All substantive mathematical claims and source attributions in the slides and notes occur in the covering report. The slides consistently rename the mixed section's original matrix size from `n` to `N`.

| Slide | Main content | Report location |
| --- | --- | --- |
| 1 | Problem and proof route | Submission record and Section 1 |
| 2 | Two compatible cells and two same-row cells | Section 1, equation (1) and following sentence |
| 3 | Colors, distinct cells, powers and singleton counts | Section 2, definitions before Theorem 2.1 |
| 4 | Scalar mixed-product estimate | Corollary 2.8 |
| 5 | Compatible conditioning and remaining row sum | Section 2.1 |
| 6 | Depleted recurrence and its derivation | Lemma 2.2 and proof |
| 7 | Positive recurrence and geometric bound | Lemma 2.7 and proof |
| 8 | Affine factors and coefficient weights | Proof of Theorem 2.1, equation (9) |
| 9 | Merging colors and the one global factorial factor | Lemma 2.3, proof of Theorem 2.1 and Corollary 2.8 |
| 10 | Identification with Proposition 28 | Section 3.1 |
| 11 | Biregular half-edge matching and centering | Section 3.2 |
| 12 | Norm moments and adjacency bridge | Sections 3.3 and 3.4 |
| 13 | Exact attained maximum without conflicts | Theorem 2.1 and its attainment proof |
| 14 | Tools, finite checks and verification limits | Submission record |
| 15 | Two exposed arrows in the source conditioning example | Example 9.2 |
| 16 | Known results and source attribution | Bibliography and the cited discussions in Sections 1, 2, 3, 9 and 10 |

The recurrence retains the original centering after depletion. The proof discussion does not treat reverse traversals as independent colors. The biregular application uses the half-edge count, not a vertex count. The norm estimate remains valid without normality. The adjacency relation is restricted to positive singular values, with the rectangular-nullspace limitation explained in the notes.

The exact maximum on slide 13 now states nonempty support. No maximum for more than two conflicting singletons is asserted. The deck does not claim a new graph eigenvalue theorem or end-to-end formal verification. The conditioning example is explicitly a failure of an intermediate assertion, not a counterexample to Proposition 28. Known recurrences and the elementary factorial bound retain attribution.

## Build and visual review

The final source was independently copied into a fresh directory as `slides.tex` and compiled three times. No other source or graphic asset was supplied. The final log contains no warnings, overfull boxes, underfull boxes or unresolved references. The rebuilt 16-page PDF is byte-identical to the exact target.

All pages of the earlier candidate were rendered and inspected. That candidate's footer page numbers touched the right page edge. The author repaired the footer container and added deterministic PDF metadata settings and an empty title-only author location. A source delta check found no mathematical change. The final 16 pages were independently rendered and inspected through four contact sheets. The corrected footer numbers have visible right padding. Main content, diagrams, equations and source footers are legible without clipping or overlap.

The earlier footer finding is resolved by this exact revision. The domain wording on slide 13 and the unsupported promise of a separate interaction record were also corrected before the final target. The speaker notes now point to the historical frozen source accurately and identify the delivered inline report as the portable source of the mathematics.

Evidence is saved in [slides-v2/source-checks.json](slides-v2/source-checks.json), [slides-v2/render-delta.json](slides-v2/render-delta.json), the three build logs and the final rendered contact sheets. No accepted source or target PDF was edited by this reviewer.

## Remaining boundary

No unresolved mathematical, coverage or slide-layout finding remains for these exact targets. Team identity is still pending. Any later title-block change needs a new hash record and a visual delta check. The actual ZIP inventory, extraction and portable verification receipt remain separate delivery checks.
