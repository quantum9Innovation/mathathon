# Digest: Bordenave on Friedman's theorem and random lifts

**Status:** Phase 1 complete, with every figure inspected.

**Paper:** Charles Bordenave, *A new proof of Friedman's second eigenvalue Theorem and its extension to random lifts*, [arXiv:1502.04482v4](https://arxiv.org/abs/1502.04482v4), 49 pages.

## Central reading

Bordenave bounds the non-backtracking spectrum before returning to adjacency eigenvalues through Ihara-Bass. The key operation is to delete paths supported on tangles before centering the random matching weights. Conditional moment cancellation and cycle-rank path enumeration then control two trace circuits: one for the centered operator and one for the remainder caused by joining tangle-free pieces. On the final logarithmic scale, this yields the $\sqrt{d-1}$ non-backtracking threshold and the $2\sqrt{d-1}$ adjacency threshold. For random lifts, inherited base eigenvalues are removed on $H^\perp$, and regular branching is replaced by base-path growth $\rho>\rho_1$.

## Start here

1. [Executive map](.paper-mastery/friedman-second-eigenvalue-lifts/01-executive-map.md)
2. [Expanded central derivations](.paper-mastery/friedman-second-eigenvalue-lifts/06-derivations.md)
3. [Section map and complete visual analysis](.paper-mastery/friedman-second-eigenvalue-lifts/04-paper-structure.md)
4. [Intuition at several altitudes](.paper-mastery/friedman-second-eigenvalue-lifts/08-intuition.md)
5. [Assumptions, limitations, and local source defects](.paper-mastery/friedman-second-eigenvalue-lifts/09-assumptions-and-weak-points.md)

## Complete dossier

- [Source and provenance](.paper-mastery/friedman-second-eigenvalue-lifts/SOURCE.md)
- [Reading status](.paper-mastery/friedman-second-eigenvalue-lifts/00-status.md)
- [Prerequisites](.paper-mastery/friedman-second-eigenvalue-lifts/02-prerequisites.md)
- [Notation](.paper-mastery/friedman-second-eigenvalue-lifts/03-notation.md)
- [Main results and dependency graphs](.paper-mastery/friedman-second-eigenvalue-lifts/05-main-results.md)
- [Reusable techniques](.paper-mastery/friedman-second-eigenvalue-lifts/07-techniques.md)

## Visuals inspected and integrated

- [Figure 1, page 8](.paper-mastery/friedman-second-eigenvalue-lifts/visuals/page-8.png): non-backtracking path support, tangles, and inconsistent half-edges
- [Figure 2, page 10](.paper-mastery/friedman-second-eigenvalue-lifts/visuals/page-10.png): why tangle-free pieces create the remainder matrices when joined
- [Figure 3, page 20](.paper-mastery/friedman-second-eigenvalue-lifts/visuals/page-20.png): the alternating trace circuit in $W_{\ell,m}$
- [Figure 4, page 22](.paper-mastery/friedman-second-eigenvalue-lifts/visuals/page-22.png): first visits, excess edges, short cycles, superfluous returns, and the spanning tree
- [Figure 5, page 30](.paper-mastery/friedman-second-eigenvalue-lifts/visuals/page-30.png): a base graph and its explicit 3-lift under two fiber permutations

There are no experimental plots or data tables in this paper. All five substantive vector diagrams were inspected directly from the rendered PDF.

## Verification and boundaries

The full LaTeX source and all 49 PDF pages were read. Source hashes, local file links, PNG readability, and required dossier files were checked. This is a detailed mathematical reading, not formal proof verification or an exhaustive errata list. No numerical checks were run.

## Next recommended action

Use teaching mode on **delete tangles before centering**, with Figures 2 and 4, then explain why centering before restricting paths would invalidate the main decomposition.
