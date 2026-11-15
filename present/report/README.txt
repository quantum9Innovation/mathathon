Revised spectral-gap report
===========================

Editable source: ../../spectral-gap-report.tex
Compiled candidate: spectral-gap-report.pdf (76 pages)
Title: Centered permutation estimates and exact recovery in sparse graphs.

The root TeX file is self-contained: all text, proofs, bibliography, and
vector plot data are embedded. It has no external manuscript-source inputs.

Current structure, following the user's revised emphasis:
  Abstract and Introduction: prior work and the Proposition 28 proof
    first, followed prominently by the main new recovery contribution.
  Sections 2--3 (pages 4--13): complete mixed-product/Proposition 28
    argument and its established spectral role.
  Section 4 (pages 14--16): main recovery Theorem 4.1, proof route,
    regular-template corollary, examples, algorithm, and significance.
  Sections 5--8 (pages 17--40): complete MAIN-TEXT recovery proofs:
    rigidity, raw channel moments, full kernels, and algorithm composition.
  Appendices A--J (from page 41): supplementary quantitative moment
    refinements, their proofs, and detailed prior-work comparisons.
  Appendix K: the historical submission/checking record, explicitly
    distinguished from the scope of the current expanded report.

The mathematical proof content is preserved. The abstract, introduction,
title, reading route, and organization were rewritten to make recovery
the main new contribution rather than a late appended extension. The
recovery theorem remains separate from the Proposition 28 row-sum input.
No additional spectral-disjointness or Bayes-constant claim is imported.
All new claims retain fixed-parameter, exact-count, independent-factor,
expected-cost, and internal-review qualifications.

Build from the workspace root with standard LaTeX packages installed,
or with the locally supplied TeX tree:
  TEXINPUTS="$PWD/present/texmf/tex//:" pdflatex -interaction=nonstopmode -halt-on-error -output-directory=present/report spectral-gap-report.tex
Run three times to resolve references and the table of contents.

source-provenance.json records the original source and four proof modules.
final-checks.json records current hashes and reference/build checks.
The root agent publishes the checked candidate at the root PDF path.
