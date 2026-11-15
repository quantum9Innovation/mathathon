# Formalization issues

| ID | Status | Issue |
| --- | --- | --- |
| SG-FORM-01 | fixed | Importing all of Mathlib exceeded the bounded 4096 MB compiler limit. Focused imports now compile within the same limit. The failed broad import is not part of the frozen source. |
| SG-FORM-02 | fixed | The validation wrapper initially required compiled libraries for every package, including an unused command-line dependency. It now verifies every pinned source revision and requires the main cache, while including only compiled library directories that exist. |
| SG-FORM-03 | fixed | The validator's forbidden-character list originally contained a literal prohibited punctuation character. It now uses the equivalent character code, preserving the check while complying with the local writing rule. |
