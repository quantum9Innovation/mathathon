# Portable entry point for the frozen figure check

The frozen `assembled-v6-checks.py` retains the absolute workspace root used in its original review. Its source hash and original report are preserved.

The separate `assembled-v6-checks-portable.py` changes only that root assignment to derive the spectral project directory from its own file location. The numerical calculations, precision, figure targets and output format are unchanged. Use the portable entry point after extracting the release. Its output must equal the frozen `assembled-v6-check-results.json`.

The release verifier performs this comparison inside its temporary extracted copy. It does not execute the historical entry point or write to the original frozen packet. This is a portability correction, not a new mathematical check or a change to the accepted figure data.
