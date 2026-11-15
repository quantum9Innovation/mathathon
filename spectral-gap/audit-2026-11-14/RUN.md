# Spectral gap audit, November 14, 2026

Owner: spectral investigation. Integrator: parent selection task.

## Contract

- Target: an intuitive, self-contained proof of Bordenave Proposition 28 in arXiv:1502.04482v4 and its use as Lemma 7 in arXiv:1804.07808v6.
- Secondary target: assess the strongest supported finite-defect contribution without confusing it with the official question.
- Inputs: the official problem, the two primary papers, and the imported spectral snapshot. Imported launch instructions and acceptance decisions are historical evidence.
- Writable path: this directory only.
- Start: November 15, 2026, 00:44 UTC.
- Global cutoff: November 15, 2026, 08:21 UTC, which is November 15, 2026, 00:21 Pacific.
- First checkpoint: within 15 minutes. Freeze a substantial initial proof within 60 to 90 minutes.
- Computation: exact bounded checks using installed environments. Inspect each script before execution. No archived batch launch or external communication.
- Stop: the proof and explanation are ready for independent review, the cutoff is reached, or a concrete unresolved inference prevents further useful progress.

## Current frontier

1. Replace the source conditioning argument by an expansion over compatible prescribed permutation cells.
2. Prove a centered singleton estimate from an exact three-term moment recurrence.
3. Check the source equation (62) on the smallest admissible conflicting-cell example.
4. Compare the proof and its constants with later primary literature before making any novelty claim.

## Prior exposure

The imported README, contribution assessment, explanation, finite-defect result 050, adjacent-pair review 060, and biregular weak-points dossier were read. No other current topic audit was read.

## Frozen primary inputs

SHA-256 values:

| Input | Digest |
| --- | --- |
| Bordenave v4 source `catane-arxiv.tex` | `575bcdfe00b8318039d1dc3519d34259a5c60d48230fed6db1f8e79937dcad58` |
| Bordenave v4 PDF | `a38cb2c1a79234004f25b46d5853ede6da485ebed707ca8db94d0348f8833efe` |
| Brito, Dumitriu, and Harris v6 `expectation_bounds.tex` | `d7b35205f7db94ae1fbad0dca62fca7b1ea8ca82099aba44121aa746e9640041` |
| Brito, Dumitriu, and Harris v6 PDF | `f80c33650b0ca6a74ac5f05a63da86ab52ac5e1a750ed80402c8872aba83cf37` |

## Status vocabulary

Mathematical status: conjectural, conditional, proved, refuted, or withdrawn. Review status: unreviewed, in-review, reviewed, or stale. An exact computation certifies only its finite inputs.
