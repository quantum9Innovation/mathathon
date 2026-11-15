# Critical-law issues

The mathematical proofs and full law passed separate exact-revision reviews. The implementation and evidence findings below are resolved, with their original circumstances preserved.

## CRIT-I1: Plot title emitted an escape-sequence warning

Found during the first figure render. A plain string contained mathematical backslashes. The figure was produced, but the source emitted a Python syntax warning. Status: raw-string repair completed. The first blanket-warning replay stopped in the installed plotting parser, so its premature success note is corrected here. A fresh replay with syntax warnings treated as errors passed and produced no standard error output. Mathematical formulas and frozen proofs are unaffected.

## CRIT-I2: Blanket warning escalation stopped an installed plotting dependency

The all-warning replay raised an existing warning inside the installed plotting parser. No mathematical or figure-formula failure was found. The correct check for CRIT-I1 is to treat syntax warnings as errors and also require an empty standard error stream. Status: resolved. The targeted syntax-warning replay passed and produced no standard error output.

## CRIT-I3: Two review workstreams selected the same output path

Found when the second final synthesis review reported a different hash at the first review path. The second review replaced the first file because unique review filenames had not been assigned. The current second review is preserved at reviews/critical-law-by-probability-v1.md with its original hash. Status: resolved. The first review was recovered byte for byte at reviews/critical-law-independent-v1.md, matching its original SHA256 395b8713ececc5329f9e1baf6bcd951b9b9bd8370276a9b26dca60fd9c5f636e. Both reviews are now preserved under unique paths. No mathematical proof or formal source changed. Future review assignments must name disjoint output files explicitly.
