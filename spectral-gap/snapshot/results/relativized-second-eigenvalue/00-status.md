# Status

## Phase

**Paper:** All 144 rendered PDF pages have been text-read. Every page has also been visually scanned in contact sheets, and ten representative or notation-sensitive pages have been inspected at full resolution. All Phase 1 dossier files are present, including analysis of every substantive visual found.

**Derived:** Phase 1 is complete. Phase 2 teaching, oral examination, talk preparation, and research-direction files have not been requested and have not been created.

## What has been read

- Front matter, Contents, Abstract, and List of Symbols
- Chapter 0, Introduction, including both main theorems and the general Hashimoto formulation
- Chapter 1, Precise Terminology and Overview of the Proof
- Chapter 2, The $d$-Regular Case Without Half-Loops, including the full proof architecture
- Chapter 3, Generalizations and Further Directions, including spreading, fundamental order, algebraic models, mod-$S$ functions, and future work
- Glossary and Bibliography
- Complete PDF ranges 1 to 144 in blocks of at most 20 pages
- Targeted exact TeX source for every central equation used in the derivations

## Visual status

There are no numbered figures, plots, or mathematical drawings to leave unexamined. All 144 pages were inspected visually. The meaningful layouts are the List of Symbols, display equations, Glossary, and Bibliography. Red boxes and colored cross-reference highlights are rendering artifacts, not content-bearing mathematical diagrams. Representative rendered pages are retained in `visuals/`.

## What is currently confusing or delicate

1. **Paper-source consistency:** Section 2.7 contains dropped trace operators, inconsistent $\tau$ powers, and a displayed coefficient formula that needs separate treatment at $i=0$. The intended argument can be reconstructed, but the display text cannot be followed mechanically without repairs.
2. **Full versus new spectrum:** Theorem 3.3.2 is false as written if $\rho(H_G)$ means the full Hashimoto radius. The proof context requires $\rho_B^{\mathrm{new}}(H_G)$.
3. **Fundamental-order bound:** Theorem 3.3.4's asserted strict lower bound conflicts with $B=W_2$ at $d=4$, for which the definitions and the paper's own later formula give $\eta_{\mathrm{fund}}(W_2)=1<\sqrt{3}$.
4. **Small algebraic inconsistencies:** The two printed odd-$k$ formulas for the $(1,2)$ weighted convolution differ and are both inconsistent with the defining sum. The derived correct formula is recorded.
5. **Proof audit boundary:** The central proof chain and the above defects were checked carefully, but this dossier is not a complete validation of every technical estimate in the manuscript.

These are source-reading cautions, not unresolved gaps in PDF coverage.

## What the user already knows

No background was supplied. The dossier assumes comfort with finite-dimensional linear algebra, basic graph theory, elementary probability, and asymptotic notation. Specialized material is introduced in `02-prerequisites.md` and `03-notation.md`.

## What remains

- Continue the dossier only if a particular technical passage needs a deeper independent audit or a formal proof.
- Phase 2 files remain on demand: talk outline, oral exam, meeting brief, research directions, and learning record.
- No numeric checks were run. Several identities are marked numerically checkable in `06-derivations.md`, but symbolic derivation was completed first as required.

## Next recommended action

Teach the certified trace as one central idea: why the strict tangle-free condition makes certificate vectors form an upper set, how finite cone decomposition follows, and why that controls the expansion coefficients. Then ask the learner to reconstruct the $n^{-\operatorname{ord}(\psi)}$ occurrence exponent from the factorial formula without looking at the notes.
