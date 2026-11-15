# Status

## Current state

Phase 1 is complete. The full paper and every substantive visual have been read and analyzed.

- [x] Source metadata verified against the arXiv abstract page
- [x] Version 6 TeX source archived with hashes
- [x] All 40 PDF pages read
- [x] All six numbered figures inspected in place
- [x] All eight figure components inspected as original assets
- [x] Appendix symbol table reconciled with the paper
- [x] Main spectral transfer derived independently from the paper's equations
- [x] Main moment-method architecture reconstructed
- [x] Three applications mapped
- [x] Assumptions, local misstatements, and unresolved audit questions recorded

No visual remains uninspected.

## Reading coverage

| Paper part | Pages | State |
| --- | --- | --- |
| Introduction, model, lift discussion | 1 to 5 | Complete |
| Non-backtracking matrix and Ihara-Bass bridge | 6 to 7 | Complete |
| Main results | 8 to 9 | Complete, including statement audit |
| Configuration model and tangle-free paths | 10 to 11 | Complete |
| Proof outline and matrix decomposition | 12 to 15 | Complete, with formula issues flagged |
| Expectation and path-counting lemmas | 15 to 20 | Complete, with Corollary 12 audit |
| Norm bounds and proof of Theorem 3 | 20 to 26 | Complete at architecture and central-estimate level |
| Community detection | 26 to 31 | Complete |
| Tanner and LDPC codes | 31 to 32 | Complete, with asymptotic qualification flagged |
| Matrix completion | 32 to 36 | Complete |
| Symbols and bibliography | 36 to 40 | Complete |

## What is currently confusing or delicate

1. Lemma 2's printed imaginary-eigenvalue multiplicities conflict with the nullspace calculation immediately before it and with the dimension count. The derived correction is in `05-main-results.md`.
2. Equation 16 has an index mismatch relative to Equation 14. The surrounding prose also confuses kernels, ranges, and leading-eigenvector spans. The intended decomposition is reconstructible, but the printed text should not be quoted uncritically.
3. Corollary 12 is not a general algebraic weakening of Lemma 11 as printed. A path example shows the problem. Its consequences for the final anisotropic estimate need closer checking.
4. Corollary 22 replaces a graph-size-dependent spectral error by an unscaled vanishing error inside the coding bound. That does not follow directly from Theorem 4, and the finite-size code example is illustrative rather than a finite-$n$ guarantee.
5. Figure 5's repeated-loop indexing is internally inconsistent in three places. Its encoding idea still makes sense, but its sample numbers do not agree.

These are audit findings, not claims that the headline theorem is false.

## What the user already knows

Unknown. The dossier assumes comfort with eigenvalues, matrix multiplication, expectations, and asymptotic notation. It teaches non-backtracking operators and local weak tree-likeness from the paper.

## Next recommended action

Teach the Ihara-Bass spectral bridge first. Start with the real function

$$y=x+\frac{ab}{x}+a+b,$$

then explain why the adjacency bulk becomes the circle $|x|=\sqrt{ab}$ and why an outer non-backtracking eigenvalue implies an adjacency outlier. This is the shortest route to understanding every main conclusion, including full row rank.

The most demanding reading task is a repair-oriented audit of Corollary 12 through Equation 26. It is more technical than the core intuition and remains an open item for verification, not a completed independent proof certification.
