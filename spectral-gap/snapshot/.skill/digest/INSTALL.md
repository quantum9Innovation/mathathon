# Digest installation notes

## This project

The active project skill is `.skill/digest/SKILL.md`. The bundled helper is
`.skill/digest/scripts/archive_source.py`. A matching `.skill/<name>/` folder
is how this Open Math agent discovers a project-local skill.

## Reuse on this VM

A canonical copy is kept at `$HOME/research/skills/digest/`. Its reading library
uses `$HOME/research/reading/<slug>/`, and optional cross-project wiki notes use
`$HOME/research/wiki/<slug>.md`. Those directories use the shared home available
across project chats on this VM.

Copy the canonical folder into a destination project's `.skill/digest/` folder
to register it with that project's skill loader. The canonical shared-home
folder alone does not register it with the loader.

## Account scope

The agent exposes project-local and published-catalog skill operations. No
account-global install operation is exposed in the available tools. Therefore
this package does not claim automatic account-wide discovery. Use the project
copy, the shared-home canonical copy, or the portable zip for reuse. A public
catalog publication or an account-level user interface may use a different
registration process that this agent cannot verify from here.

## Visual and source requirements

`pdf_extract` supplies page-labeled text. `pdftotext` supports page ranges and
central-library paths. `pdftoppm` renders substantive visuals for `view_image`.
The archive helper accepts PDFs, safe tar archives and single gzip TeX sources,
and rejects unsafe paths, links and special files. It does not execute source
contents.
