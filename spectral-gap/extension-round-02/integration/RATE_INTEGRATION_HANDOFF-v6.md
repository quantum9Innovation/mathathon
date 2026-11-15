# Candidate rate-section integration

Sender: rate investigator. Recipient: problem 21 integrator.

Status: candidate manuscript integration. The uniform first-correction synthesis was still under independent review when these files were drafted. These candidates do not change canonical acceptance, maintained manuscript files, or frozen research packets.

## Candidate files

- `rates-v6.tex`: a concise main section with the uniform rate, its first signed correction, and the sharp supremum constant for every fixed $C>0$.
- `rate-proof-v6.tex`: a detailed appendix with all explicit finite constants and the proof of RATE-1, including the exact odd small-parameter conditioning and the extension of the same constants to every $C>0$.

Use the existing manuscript macros and notation. The polynomial leading term remains `\mathcal L_k`, matching `sections/extensions.tex`. Parity is `\epsilon`. The appendix alone uses `\delta=K^2/N` and explicitly distinguishes it from parity. No internal packet or research-history prose appears in the candidate TeX.

Suggested placement: main rate section after `sections/asymptotics.tex`. Include the proof file after `\appendix`, before the bibliography. The candidates themselves do not issue `\appendix` or force a page break.

## Principal labels

| Label | Purpose |
| --- | --- |
| `sec:rates` | Main rate section |
| `thm:rate` | Uniform explicit rate, required by `thm:global` |
| `eq:rateW` | Corrected ratio $W_{N,k}$ |
| `eq:uniformrate` | Uniform order $N^{-1/4}$ |
| `eq:ratefinite` | Three-term explicit bound |
| `thm:firstcorrection` | Uniform signed correction and sharp supremum constant |
| `eq:uniformfirstcorrection` | Uniform signed first correction |
| `eq:sharprateconstant` | Exact limiting supremum constant |
| `sec:rateproof` | Explicit-rate appendix |
| `eq:rateconstantsB` | Intermediate explicit coefficients |
| `eq:rateconstantsA` | Final explicit rate constants |
| `eq:ratelocal` | Finite bound at the actual order $k$ |

External manuscript references are `eq:hyperdef`, `eq:availabilityeven`, `eq:availabilityodd`, `eq:logsublinear`, and `eq:actionG`. The main proof uses the positive-scale saddle expansion and the vanishing of $A_1(C)$ as $C\downarrow0$. It does not assume uniformity from pointwise limits.

## Exact frozen inputs

- `../rate/square-root-rate-v1.md`, SHA256 `ed472ce70521c37d59c4e3efc88bf7e883d1a75526023ef2c3a15c57bcd9c581`.
- `../root/uniform-first-correction-v1.md`, SHA256 `14ba2a74f0a51bd63bc622a30f0ad4f1bcf0c0c5cc95faa14d3f38e5ae920d5a`.
- `../saddle/proof-v1.md`, SHA256 `c9033ac8ff15bd5265771eaad4d4b7eeeb2b2e19860decfa63e0b2bb8c177da8`.
- Accepted manuscript revision 5 manifest, SHA256 `ce8f5240a55ef278b9ab2c6ce53cc25f7688fcd28dafd602937c303a06b8ac78`, for the existing notation and partition identities.

The mutable `sections/asymptotics.tex` was read only to align its established labels and notation. The mathematical input remains the frozen proofs above.

## Verification

The candidate files were compiled in a temporary copy of the full manuscript. After reference stabilization, there were no undefined references or duplicate labels. The rate section occupied about one and a half pages and the appendix occupied four pages. The six pages touched by those sections were rendered and inspected. Their formulas, table, margins and page endings were legible, with no clipping or overflow in either candidate.

The temporary full build retained one overfull paragraph from the separately maintained `asymptotics.tex`, around its second-peak estimate at lines 103 to 105. That finding was reported to the integrator. No maintained file was edited here.

The first temporary harness accidentally duplicated an already-present appendix input copied from the live main file. The duplicate was removed in the temporary harness before the clean reference build and visual check. The candidate TeX files were unaffected.

Requested next action: finish the independent review of the uniform synthesis, copy the accepted candidates into the maintained manuscript, and perform the final assembled manuscript review and render. The existing PDF operation marker was not repeated.
