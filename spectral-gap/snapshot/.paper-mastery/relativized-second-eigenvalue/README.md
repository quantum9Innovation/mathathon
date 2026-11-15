# Reading guide: The Relativized Second Eigenvalue Conjecture of Alon

This is the complete Phase 1 mastery dossier for Joel Friedman and David-Emmanuel Kohler's arXiv paper [1403.3462](https://arxiv.org/abs/1403.3462).

## Start here

1. [Executive map](01-executive-map.md): problem, theorems, assumptions, and proof strategy
2. [Notation](03-notation.md): symbol types, dimensions, and common confusions
3. [Main results](05-main-results.md): claims and dependency graph
4. [Derivations](06-derivations.md): expanded central arguments and source repairs
5. [Intuition](08-intuition.md): one-sentence, whiteboard, geometric, and algorithmic explanations
6. [Assumptions and weak points](09-assumptions-and-weak-points.md): scope limits and exact counterexamples to defective printed statements

For the complete section map and visual inventory, read [paper structure](04-paper-structure.md). For background, use [prerequisites](02-prerequisites.md), and for reusable methods use [techniques](07-techniques.md).

## Provenance and status

- [Source record](SOURCE.md): archived source paths, hashes, reading ranges, and visual inspection coverage
- [Current status](00-status.md): what is complete, remaining uncertainties, and next lesson
- [Visuals](visuals/): ten representative or notation-sensitive rendered pages inspected at full resolution

## Important reading caution

The paper has no numbered figures, mathematical drawings, experimental plots, or data tables. All 144 pages were visually reviewed. Its List of Symbols, equation displays, Glossary, and Bibliography are incorporated into the dossier. Colored boxes and highlights are cross-reference styling, not mathematical diagrams.

The manuscript also has genuine notation and statement defects. In particular, Theorem 3.3.2 requires the new Hashimoto radius, Section 2.7 has inconsistent trace and parameter displays, and Theorem 3.3.4 conflicts with the $W_2$ bouquet example. Read the weak-points note before quoting ancillary formulas.

## Verification boundary

The complete rendered PDF was read, targeted exact TeX source was checked, all pages were visually scanned, and central derivations were expanded independently. This dossier is not a formal verification of every estimate and is not a complete errata list. No numerical tests or Lean checks were run.

## Recommended next action

Teach the certified trace, then ask for a from-memory derivation of the $n^{-\operatorname{ord}(\psi)}$ occurrence exponent from the factorial formula. After that, use the side-stepping derivation as a technical oral-exam topic.
