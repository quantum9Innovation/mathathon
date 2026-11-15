Revised mathematical Beamer presentation
========================================

Editable source: ../../spectral-gap-slides.tex
Compiled PDF: ../../spectral-gap-slides.pdf
Style: standard Madrid Beamer theme, serif mathematics/text, blue title
bars, normal definition/theorem blocks and author/title/page footer.

60 slides: 50 main frames and 10 optional technical backup frames.
  6--8: matching versus nonmatching, perfect matching, and bipartite graphs.
  22--24: a pairing becomes a permutation matrix, uniform random
    pairings, and the single-edge lift picture.
  27--32: average/centering, prior work and Proposition 28, compatible
    pairing, its spectral role, and half-edge connectors.
  33--47: a visual six-vertex recovery walkthrough. The fixed (2,1)
    rule has nine modular answers, two valid colorings, and one unordered
    partition. This is a finite illustration, not an unknown-table
    uniqueness claim for that particular small graph.
  48--50: contribution/predecessors and references.
  51--60: optional precise hypotheses, recurrence/product estimates,
    complete-kernel/raw-moment details and supplementary results.

Build from the workspace root:
  bash present/build.sh slides

All required vector PDFs are supplied in assets/. Optional regeneration:
  make_figures.py             Original elementary/spectral illustrations.
  make_teaching_figures.py    Matching/permutation/lift/half-edge figures.
  make_recovery_figures.py    Recovery story and exact candidate checks.
These scripts require Python, Matplotlib and NumPy. Building the supplied
TeX does not require Python or regeneration of the figures.

The source is expanded and editable, with no external input dependency
on another manuscript. recovery-simple.tex also preserves the teaching
sequence as an editable fragment. All underlying proofs are in the report
or, for explicitly labeled supplementary results, the full reference paper.

The final independent content review is revision-content-audit.txt.
The source-bundle manifest binds final sources, figures, and PDFs.
