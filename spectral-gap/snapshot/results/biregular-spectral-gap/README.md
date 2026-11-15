# Digest: Spectral gap in random bipartite biregular graphs and applications

Gerandy Brito, Ioana Dumitriu, Kameron Decker Harris. arXiv:1804.07808v6, 2021 revision, journal publication 2022.

## Outcome

This is a complete Phase 1 comprehension dossier of the 40-page paper. It includes full notation and result maps, central derivation notes, reusable techniques, intuition, assumptions, and a visual-by-visual reading of every numbered figure and every panel.

The central claim is the asymptotic almost-Ramanujan bound

$$\eta\leq\sqrt{d_1-1}+\sqrt{d_2-1}+\epsilon_n',\qquad\epsilon_n'\to0,$$

for fixed-degree uniform simple bipartite biregular graphs with high probability. The paper also derives the lower positive spectral edge and full row rank of rectangular biadjacency matrices when $d_1>d_2$.

The main mechanism is the Ihara-Bass dictionary between adjacency and non-backtracking spectra, followed by centered non-backtracking moment bounds based on tangle-free circuit encodings.

## Start here

1. [Executive map](01-executive-map.md): problem, main claims, applications, and learning goals.
2. [Full visual and section inventory](04-paper-structure.md): all figures, how to read them, and the claims they support.
3. [Derivations](06-derivations.md): block spectra, the complete quadratic case analysis, rank, matrix decomposition, circuit bookkeeping, asymptotics, and applications.
4. [Intuition](08-intuition.md): the paper at several altitudes and naive approaches that fail.
5. [Audit and weak points](09-assumptions-and-weak-points.md): exact corrections, proof-repair questions, and application limits.

## Dossier files

| File | Contents |
| --- | --- |
| [SOURCE.md](SOURCE.md) | Bibliography, source links, archive paths, hashes, reading coverage |
| [00-status.md](00-status.md) | Completion record, unresolved questions, next learning step |
| [01-executive-map.md](01-executive-map.md) | Main contribution and proof architecture |
| [02-prerequisites.md](02-prerequisites.md) | Minimum background and reading order |
| [03-notation.md](03-notation.md) | Strict notation table and symbol collisions |
| [04-paper-structure.md](04-paper-structure.md) | Section map plus complete visual and appendix-table analysis |
| [05-main-results.md](05-main-results.md) | Theorems, lemmas, assumptions, dependencies, Mermaid dependency graph |
| [06-derivations.md](06-derivations.md) | Nine detailed derivation notes |
| [07-techniques.md](07-techniques.md) | Reusable machinery and alternatives |
| [08-intuition.md](08-intuition.md) | Whiteboard explanation, geometry, small cases, naive baselines |
| [09-assumptions-and-weak-points.md](09-assumptions-and-weak-points.md) | Model scope, source inconsistencies, unresolved audit items |

## Visual coverage

All visuals were inspected on the paper pages and as original source assets.

| Visual | Core reading |
| --- | --- |
| Figure 1, page 2 | Two vertex classes, side-specific degrees, and half-edge interpretation |
| Figure 2, page 4 | A $(3,2)$ biregular graph whose crossed wiring obstructs the required lift representation |
| Figure 3A, page 7 | Signed adjacency bulk, zero atom, Perron level, and asymptotic upper threshold |
| Figure 3B, page 7 | Complex non-backtracking roots, bulk circle, zero-adjacency-induced imaginary roots, eight finite-sample outliers |
| Figure 4, page 13 | Four alternating matrix and transpose legs, purple shared edges, and twelve traversals on eight distinct graph edges |
| Figure 5, page 17 | Compressed discovery-tree encoding of repeated single-cycle traversal, including a documented indexing inconsistency |
| Figure 6A, page 28 | Directed class proportions and reciprocal degrees satisfying detailed balance |
| Figure 6B, page 28 | Seventy-two-node multigraph realization with 54 blue, 9 green, and 9 red nodes |
| Appendix A, page 36 | Symbol table, including its incorrect printed sign for tree excess |

## Important audit status

The spectral transfer and rank argument are derived in the notes. Several definite local statement and figure errors are also corrected.

The most substantial unresolved item is Corollary 12's compatibility with Lemma 11 in the biregular circuit computation. Its discarded factor is $(a/b)^{2\psi}$ in the notation of the dossier, and the subsequent one-sided imbalance bound needs more analysis. The dossier therefore reports the main theorem as the paper's claim, not as an independently certified result.

Corollary 22's unscaled error and the finite-size coding example also require asymptotic qualifications. Imported matching, frame, Ihara-Bass, and Grothendieck ingredients were not independently re-proved.

No optional numerical experiments were run. No experiment was needed to inspect or understand the visuals.

## Primary source

- arXiv abstract: https://arxiv.org/abs/1804.07808
- Versioned paper PDF: https://arxiv.org/pdf/1804.07808v6

The full archived TeX and PDF are retained at `/workspace/nucleus/work/home/research/reading/biregular-spectral-gap/` on this VM. See [SOURCE.md](SOURCE.md) for SHA256 hashes and ingestion details.

## Recommended next action

Teach the Ihara-Bass spectral bridge interactively, starting from

$$y=x+\frac{ab}{x}+a+b,$$

and derive why bulk points map to $|x|=\sqrt{ab}$ while rank loss forces $\pm i\sqrt a$. Then use retrieval questions on Theorem 4 rather than starting with the longest circuit-counting estimates.
