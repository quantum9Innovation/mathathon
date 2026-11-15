# Submission report v1, independent assembly review

Date: November 15, 2026 Pacific.

Decision: Accept the mathematical and document assembly identified below. Team identity remains pending. This decision does not approve an actual submission and does not yet cover the final slides or ZIP archive.

The prior frozen-v10 acceptance is used only for its stated mathematical scope. This review independently checks the new assembly, its changed front matter, embedded figures, source preservation and build.

## Exact targets

| Artifact | SHA256 |
| --- | --- |
| `frozen-v1/report.tex` | `5acdbad9d59e8126bf03c4619ce3e43c0e444623d5fdb592178b54b033edc99d` |
| `frozen-v1/report.pdf`, 44 pages | `d0c9e2d24bcd244463a89e10e3285bebf4600ec80f034d78ee857af2bdd4bcfe` |
| Frozen-v10 baseline manifest | `70d45e272ec4c32f79b7d630dea55ced37c7f95cb2e89b62c3719ed998737c4d` |

All 28 baseline manifest entries were independently verified before comparison. No baseline or submitted source was edited by this reviewer.

## Preservation and scope

All 37 mathematical blocks are byte-identical to the accepted baseline: 11 theorems, 3 corollaries, 5 lemmas, 14 proofs and 4 examples. All 12 section bodies are byte-identical after excluding their figure environments. The complete inline bibliography is byte-identical. Moving the spectral section directly after the mixed-product section changes numbering through ordinary references, not mathematical content.

The new abstract and reading route accurately describe the written result. Exact mixed maxima are claimed only for zero, one or two inconsistent centered singletons. Bounds at larger conflict counts are distinguished from maxima. The new report does not claim a new graph eigenvalue theorem, a complete solver program, universal historical firstness or full formal verification.

The two-cell illustration, compatible-conditioning argument, row-sum recurrence, scalar consequence and half-edge application remain fully stated in text. The spectral discussion continues to separate the proved fixed-product estimate from cited graph enumeration and tangle estimates. The conditioning counterexamples still target the intermediate assertion in equation (62), not Proposition 28 or its graph conclusion.

## Submission requirements and provenance

The official rules were read at repository commit `4d6098d263275ff1cb0308908a693e776c116f53`, using the [participant rules](https://github.com/SAIRcompetition/mathathon-judge/blob/4d6098d263275ff1cb0308908a693e776c116f53/rules/participant-rules.md), [submission guidelines](https://github.com/SAIRcompetition/mathathon-judge/blob/4d6098d263275ff1cb0308908a693e776c116f53/rules/submission-guidelines.md) and [judge guidelines](https://github.com/SAIRcompetition/mathathon-judge/blob/4d6098d263275ff1cb0308908a693e776c116f53/rules/judge-guidelines.md).

The report is one self-contained TeX file with inline appendices, bibliography and vector figures. No external source, bibliography or graphic file is required. The selected track is Combinatorics. The author block is empty rather than invented, and no submission-repository link is claimed. Exact team names and affiliations remain the only pending report metadata.

The front matter distinguishes written proofs, cited theory and finite computational corroboration. Its finite domains agree with the retained exact-check record and the one-conflict and two-conflict reviews. In particular, the 20,204 independent two-conflict original-product checks are not conflated with the separate integrator's checks.

The chronology explicitly identifies the event interval and treats retained records and PDF build metadata as records, not a forensic authorship certificate. The initial audit's `00:44 UTC` timestamp converts to November 14 at 16:44 Pacific. The baseline PDF records November 14 at 21:41:54 Pacific. The imported archive records its separate earlier graph campaign and is excluded from newly claimed moment results. Published source results remain credited as prior work.

The required tool disclosure states the work performed and how outputs were checked. It distinguishes internal review from independent human peer review, does not invent an underlying model revision, and does not claim that finite checks prove the general theorems. No Lean declaration is relied on by the report.

## Independent build, figures and layout

A fresh directory contained only `report.tex` before compilation. Three standard compilation passes succeeded with zero warnings, overfull boxes, underfull boxes or unresolved references. The rebuilt PDF has the exact target SHA256, not merely matching extracted text. There are 144 distinct labels and no unresolved source references.

All 22 inline plot series were checked independently. Finite plotted coordinates agree with the frozen data. Analytic curves were compared with 60-digit evaluations of the displayed theorem formulas. Across 3,338 scalar coordinate comparisons, the maximum discrepancy normalized by `max(1, absolute expected value)` was approximately `7.305e-12`, below the `3e-10` tolerance.

All 44 pages were rendered and visually inspected. Figure pages 25, 30 and 32 were also enlarged. No clipped content, overlap, unreadable mathematical display or defective figure label was found. The key figures retain textual captions explaining their mathematical content and the limited role of finite evaluations.

Evidence is saved in [report-v1/source-checks.json](report-v1/source-checks.json), [report-v1/figure-checks.json](report-v1/figure-checks.json), the three build logs and the rendered contact sheets.

## Limits and next action

This review checks an assembly delta against previously reviewed proofs. It is not a fresh reconstruction of every proof, an external peer review, a universal priority certificate or a replay of every finite checker. The reported finite-check counts were checked against their retained records. The final delivery checker must separately verify the actual ZIP and its included supplementary files.

No open mathematical or report-layout finding remains for these exact targets. Adding identity information requires a later source and PDF revision, a title-block-only delta check and a new exact hash record. Final slide and archive acceptance must name their own exact targets.
