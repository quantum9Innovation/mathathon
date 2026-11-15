# Problem 21 submission preparation packet

**Status: verified draft, identity metadata pending.** This packet has not been submitted, uploaded or published. Exact team name, author names and affiliations must be supplied before the title blocks can be finalized. The current report and presentation intentionally contain no invented author identity.

Problem: Gaps in spectral gap literature. Primary track: Combinatorics.

## Read first

- [Report](report.pdf), 44 pages. This is the mathematical record. Its [single TeX source](report.tex) contains every section, appendix, reference and vector figure.
- [Presentation](slides.pdf), 14 main slides and 2 backups. The planned main talk is 17 minutes 40 seconds, followed by discussion.
- [Speaker notes](presentation/speaker-notes.md), with a timing plan and report references.
- [Finite-check supplement](supplement/README.md), with exact tested domains, seeds, counts and preserved source provenance.

The report gives the centered permutation-product proof requested by Problem 21, explains its role in the non-backtracking spectral argument, and develops the stated sharp envelopes and diagonal asymptotics. Its claimed exact mixed maxima cover zero, one and two conflicting centered singletons. The general bounds at larger conflict counts are not presented as maxima.

The report explicitly credits prior methods and identities. It distinguishes its proved probabilistic input from cited graph path and tangle estimates. It does not assert a new graph eigenvalue theorem or universal historical priority. The later growing-defect and collective-pair research is outside this packet.

The required event-work account and tool-use disclosure are on the opening pages of the report. They identify the tools, their purposes and the checks applied. The internal reviews in this archive are not external human peer review. No optional Lean project or full-formalization claim is included.

## Reproduce and verify

The checkers require Python 3 and its standard library on a Unix-like system. Full artifact verification also requires `pdflatex`, `pdfinfo`, `pdftotext` and `pdftoppm`. The TeX installation needs the ordinary packages named in each source, including PGFPlots and Beamer. No project-specific TeX assets, bibliography file, network access or credentials are needed.

From this directory, run:

```bash
python3 verify.py --receipt /tmp/problem21-verification.json
```

The receipt must be outside the extracted package. The verifier checks every manifest entry, rejects unexpected files and symlinks, checks the 37 preserved mathematical blocks, rebuilds both PDFs from source in fresh directories, compares all extracted text and every rendered page, and replays all three finite checkers. It writes temporary build products outside the package. Full verification also checks the expected page counts and the final compilation logs.

For a faster integrity and finite-computation check that omits PDF builds and rendering, Python 3 and `pdfinfo` are sufficient:

```bash
python3 verify.py --quick --receipt /tmp/problem21-quick-verification.json
```

`MANIFEST.json` records the path, byte count and SHA-256 of every included file other than the manifest itself. The separately delivered ZIP verification receipt binds the archive hash, its manifest hash and the fresh-extraction verification. A successful run verifies artifact integrity and reproducibility within the stated checks. It does not prove the unrestricted mathematical theorems or complete the missing identity metadata.

The original plot data are included under `data/` for inspection. Their plotted coordinates are already embedded in `report.tex`, so the report build does not read those files. The editable presentation is `presentation/slides.tex`.

## Review scope

The [report assembly review](reviews/report-v1-review.md) independently checks all 37 mathematical blocks against the previously accepted revision, every section outside figure environments, the complete bibliography, all 22 inline plot series, source-only compilation and all 44 rendered pages. Its `frozen-v1/report.tex` and `frozen-v1/report.pdf` targets correspond byte-for-byte to this archive's `report.tex` and `report.pdf`.

The final slide review is included under `reviews/`. Its exact PDF and source hashes identify the corresponding `slides.pdf` and `presentation/slides.tex` in this archive. All presentation claims must be supported by the report.

The four linked source, figure and slide-delta evidence records are included. Build logs and rendered contact sheets mentioned in the reviews remain in the working record. The portable verifier reproduces the builds and all page comparisons from the files in this archive.

The supplement preserves earlier finite-check programs and their review records without editing them. These records retain historical workspace-relative target names. They are evidence excerpts, not a copy of the complete historical research workspace. The portable replay entry point and all of its dependencies are included.

## Submission rules consulted

The [participant rules](https://github.com/SAIRcompetition/mathathon-judge/blob/4d6098d263275ff1cb0308908a693e776c116f53/rules/participant-rules.md), [submission guidelines](https://github.com/SAIRcompetition/mathathon-judge/blob/4d6098d263275ff1cb0308908a693e776c116f53/rules/submission-guidelines.md), [judge guidelines](https://github.com/SAIRcompetition/mathathon-judge/blob/4d6098d263275ff1cb0308908a693e776c116f53/rules/judge-guidelines.md) and [Problem 21 statement](https://github.com/SAIRcompetition/mathathon-judge/blob/4d6098d263275ff1cb0308908a693e776c116f53/problems_original/021-gaps-in-spectral-gap-literature.md) were checked at commit `4d6098d263275ff1cb0308908a693e776c116f53`.

The deadline stated there is November 15, 2026 at noon Pacific. The report is the official written record. The slide deck is designed for the permitted 20-minute talk. This preparation packet performs no submission action.
