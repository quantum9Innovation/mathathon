Revised spectral-graph report and slides
======================================

Entry points:
  ../spectral-gap-report.tex     Formal report: prior work and Proposition
                                28 first, then the main new recovery
                                result and its complete main-text proofs.
  ../spectral-gap-slides.tex     Elementary spectral-graph introduction,
                                original matching-product mechanism,
                                and accessible recovery-result slides.

Final documents: 60 slides (50 main, 10 optional backup) and a 76-page
report. Recovery is prominent in the abstract and introduction. The main
theorem is Theorem 4.1 (page 14), followed by complete MAIN-TEXT proofs
in Sections 5--8 (pages 17--40). Quantitative moment refinements appear
later in appendices. The Proposition 28 proof and all mathematical proof
content are retained; the introduction and organization were revised.

Build both documents from the workspace root with:
  bash present/build.sh

For only one document, use bash present/build.sh slides or report.

The script uses pdfLaTeX and builds the two PDFs in the workspace root.
The report is a self-contained TeX file, including its vector plots and
all added proof text. The slides use the supplied vector PDFs in
slides/assets/. Optional figure generators are slides/make_figures.py,
slides/make_teaching_figures.py, and slides/make_recovery_figures.py.
They use Python, NumPy, and Matplotlib; rebuilding the PDFs does not
require running these generators. The six-vertex example is checked by
exact enumeration, recorded in slides/assets/recovery-exact-check.json.
texmf/ supplies locally vendored missing LaTeX packages; the build does
not need network access. texlive-archives/manifest.json records their
official TeX Live CTAN mirror URLs and SHA256 checksums. A basic LaTeX
installation with AMS packages, geometry, graphicx, and hyperref is still
required. Standard package notices and licenses remain in the source.

Original PDFs are retained under originals/. The original source matched
spectral-gap/submission-round-01/packages/v3/report.tex and its slides.
Copies of those original TeX files are also retained under originals/.
The report's earlier submission record is explicitly historical and
retained in its last appendix. Recovery is the main new result of the
current report, following the established prior work and Proposition 28.

reference/unknown-frame-recovery.pdf is the full source research paper.
It supplies the proofs of the additional ambiguity and information-limit
results attributed to that manuscript in optional backup slides 59--60.
Those additional theorems are separate from the report's core recovery theorem.

The supplied MIT PRIMES Circle exposition by Brian Pan, Nathan Nie, and
Daniel Wang (2025), An Introduction to Spectral Graph Theory, informed
the choice of elementary background topics. Its prose and figures were
not copied. The revised slides provide their own worked examples and
vector figures. Source:
https://math.mit.edu/research/highschool/primes/circle/documents/2025/Brian-Nathan-Daniel-Final.pdf

The new results concern exact neighbor counts, fixed parameter bounds,
and specified independent random graph factors. Expected work, correct
listing, and successful identification of the hidden partition are
different guarantees. No noise stability, growing-parameter uniformity,
historical-firstness certificate, or external peer-review verdict is
implied. See the precise theorems and their proofs in the report.
