# Digest installation and validation

## Outcome

The attached skill is adapted, installed locally as `digest`, and resolvable by
`skills_load`. It is available in this project and bundled in
[digest-open-math.zip](digest-open-math.zip).

Portable archive SHA256: `99e162658727c9e35d928c101b2e76566aa1a674d30d26a17ba77f54d28061ac`.

## Open Math adaptations

- Project `AGENTS.md` supplies the local writing and execution contract.
- `pdf_extract` reads page-labeled text from project PDFs. `pdftotext` handles
  complete page ranges and PDF paths in the shared library.
- `pdftoppm` renders substantive visuals for actual inspection with
  `view_image`. Extracted captions alone do not satisfy this requirement.
- The bundled `archive_source.py` accepts PDFs, ordinary source archives and
  single gzipped TeX files. It rejects unsafe paths, links and special files,
  applies size and member limits, verifies downloaded file kinds, writes hashes,
  and cleans up failed library entries. It never executes downloaded content.
- Fetched sources use `$HOME/research/reading/<slug>/`, persistent shared-home
  storage available to other project chats on this VM. Optional cross-project
  wiki references use `$HOME/research/wiki/<slug>.md`.
- Dossiers remain in `.paper-mastery/<slug>/` in the project where the paper is
  being studied. `SOURCE.md` records stable source locations.
- Downloaded archives and TeX are never treated as operating instructions.
  Fetched TeX is not automatically compiled.

The file `INSTALL.md` in the skill folder repeats the installation and scope
limits. The adapted skill does not launch a research run or swarm on its own.

## Optional cross-project references

The installed skill requires no other skill. When requested after Phase 1, it
offers a directly written Markdown note at `$HOME/research/wiki/<slug>.md`,
containing the one-line identity, dossier path and library source path. No
additional integration is required.

Reading, visual and numerical operations use ordinary Open Math tools. If more
personal skills exist in other projects, this project's listing cannot prove
their contents. Supply those skill folders or URLs for similar adaptation.

## Account and project scope

The local skill directory is `.skill/digest/`. The canonical reusable copy is
`$HOME/research/skills/digest/`. Local and canonical file hashes were compared.
The portable zip was reopened and its members and CRC values were checked.

The agent's available skill operations expose project-local folders and a
published catalog. No account-global install operation is exposed in this
conversation. Therefore automatic account-wide discovery in every project chat
could not be established and is not claimed. The canonical shared-home copy is
not itself a loader registry entry. To register it in another project, copy it
to that project's `.skill/digest/` directory.

## Verification performed

- **5 archive-helper tests passed** in 0.005 seconds. Coverage: PDF storage and
  SHA256, safe archive extraction, single gzip TeX ingestion, traversal cleanup,
  and symlink rejection. See [digest-tests.log](digest-tests.log).
- **PDF text workflow passed** on a locally generated one-page sample with a
  real TikZ figure. `pdf_extract` recovered the title, caption and axis labels.
- **Visual workflow passed.** The page was rendered at 1224 by 1584 pixels and
  inspected. The quadratic curve, axes, title and caption were visible.
- **Research controller regression passed**, 125 tests in 2.125 seconds after
  the local workspace-style cleanup. See
  [research-lab-regression-after-style.log](research-lab-regression-after-style.log).
- The new workspace scan of current text files found no em dashes, en dashes or
  semicolons. Source files supplied by the user were not rewritten.
- Canonical and local skill files match, and the portable archive validates.

No real paper was downloaded or digested as part of this installation test.
Consequently an actual arXiv retrieval, a substantial multi-page visual review,
and a complete research dossier are not claimed as verified. These paths have
been adapted and locally smoke-tested instead.

## AGENTS.md and Git

The supplied local workspace rules were added verbatim to the root `AGENTS.md`.
Generated first-party files with violations were cleaned without changing
controller behavior. `AGENTS.md` is not listed in `.gitignore`, and this project
still has no commits. No commit was created, so the instruction not to commit
`AGENTS.md` was respected. The writing rules apply regardless of Git use.

A synthetic PDF smoke-test directory in `.scratch/` was removed after this
check. The validated package and logs above are the retained evidence.
