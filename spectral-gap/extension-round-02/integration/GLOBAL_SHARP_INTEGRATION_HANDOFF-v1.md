# Sharp global approximation integration candidate

Revision 1. November 15, 2026 UTC.

Status: candidate TeX integration of frozen GSR-1. The mathematical packet is under independent review. This handoff does not promote a claim or modify a maintained manuscript file.

## Candidate files and hashes

| File | SHA256 |
| --- | --- |
| `global-sharp-candidate.tex` | `f8c55a8daf6f4705d5678622772b0d0975ccddfedf05896f1cfc2708abfd2f76` |
| `global-sharp-proof-candidate.tex` | `2c5271d3cae808b679124b276f8bbe5f1b323c49aa1a2a9fd7b484384fb185ab` |

The source theorem and proof are frozen in `extension-round-02/global-sharp-rate/proof-v1.md`, SHA256 `c3f5bd362a005688d28a6ac1f5440188aa0b8f4a802de269b17c7d4e08e96fcf`. Its `MANIFEST-v1.json` has SHA256 `a67784bed544f88c670b000bda04ec700d257a98c14ffd33d77ea5958314e268`.

## Proposed integration

1. In `manuscript-round-01/manuscript/sections/asymptotics.tex`, retain all content before `\subsection{Keeping the denominator exact}`. Replace that subsection through the end of the file with `global-sharp-candidate.tex`.
2. Copy `global-sharp-proof-candidate.tex` into a new manuscript section and input it immediately after `\input{sections/rate-proof}`. With the current structure it becomes Appendix B.
3. Preserve `sections/rates.tex` and `sections/rate-proof.tex`. Their quartically corrected approximation and sharp `N^{-1/4}` rate concern a different target.

The main candidate preserves the exact approximation `\mathcal A_{N,k}`, the normalizations `R_k,H_k,D_k`, and the labels `eq:globalformula`, `thm:global`, and `eq:globalerror`. It replaces the conservative global rate by the sharp `C_*N^{-1/3}+o(N^{-1/3})` rate. It retains the upper-range `O(N^{-1/2})` estimate and the endpoint calculation.

New main labels are `eq:globalprofiledef`, `eq:globalsharpconstant`, `eq:globalprofile`, and `eq:globalmaxequation`. The detailed proof is labeled `sec:globalsharpproof`. Its displayed formulas use the `eq:global...` prefix, including `eq:globalcompact`, `eq:globalrealLaplace`, `eq:globalpositivecompare`, `eq:globalmiddlebound`, `eq:globaltailinfty`, and `eq:globaltailzero`.

The appendix retains the compact parity-conditioned expansion, the uniform real two-saddle argument, the exact odd adjacent-degree normalization, the negative-saddle matching estimate, both tails, and the unique-maximizer proof. The absolute-constant hypotheses of frozen equations (20), (25), and (29) remain explicit. It uses `\mathcal L_k` for the leading polynomial normalization throughout. The only notation changes from the frozen proof are manuscript notation and descriptive equation labels.

## Exact manuscript inputs used for layout validation

The isolated build copied the maintained manuscript and figures without changing them. Its relevant source hashes at copy time were:

| Maintained source | SHA256 |
| --- | --- |
| `manuscript/main.tex` | `d8fa4aa517e7111b804ed464cf0ae44aa4ccfd35b0515c96ab21b9f4c86003fe` |
| `manuscript/sections/asymptotics.tex` | `48764f13c723a0caebe4f07545c4e81cd43182e6b46db57d5fd0fa79d977d6b5` |
| `manuscript/sections/rates.tex` | `a36939676c8b4c2aab572ea90c2055ba4cbad428593c52d1a1c496574cce5228` |
| `manuscript/sections/rate-proof.tex` | `ba8e0ccfd926b3036f7b4542c426f203452d445e57a4b905ed9fc8a6f60a64f9` |

These are layout inputs, not a requirement that unrelated maintained sections remain at those revisions.

## Validation

Two consecutive `pdflatex` passes succeeded in `/tmp/spectral-global-sharp-layout/manuscript`. The second log contains no overfull boxes, underfull boxes, undefined references, or duplicate labels. The resulting PDF has 38 pages. The main candidate occupies page 22 and the top of page 23. Appendix B occupies page 33 through the upper part of page 37.

Rendered pages 22, 23, and 33 through 37 were visually inspected. Equations, theorem text, headings, and page breaks are legible with no clipping. A scan found no prohibited punctuation in either candidate. The candidate formulas were checked against the frozen proof.

The temporary review PDF is `/tmp/spectral-global-sharp-layout/manuscript/main.pdf`. Build logs are `compile-1.txt`, `compile-2.txt`, and `main.log` in the same directory. The maintained manuscript, earlier frozen packets, and Section 7 sources were not edited by this integration task.
