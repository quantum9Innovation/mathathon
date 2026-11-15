# Growing defect issues and scope boundaries

November 15, 2026, America/Los_Angeles.

No mathematical or integration finding remains open in the reviewed paper proofs.

| ID | Status | Finding and resolution |
| --- | --- | --- |
| GD-F1 | fixed | The first formalization had a valid identity for an arbitrary matrix satisfying projected inverse equations, but did not construct its centered solution. Source-v2 constructs the inverse from the shifted matrix and proves both centering identities. Invertibility from the graph spectral gap remains an explicit application bridge. |
| GD-F2 | fixed | A broad formal import exceeded the compiler's 4096 MB limit. Focused imports pass under the same bound. The broad import is absent from frozen sources. |
| GD-F3 | fixed | The initial validation wrapper required compiled libraries for an unused package. It now verifies every pinned source revision and uses only available compiled dependency libraries, while requiring the main mathlib cache. |
| GD-S1 | documented | Deterministic labels are not graph-dependent marks. Rare adjacent realizations remain in the sample space and are controlled by a probability bound. |
| GD-S2 | open research boundary | The logarithmic growth restriction is sufficient. No optimal threshold or close-pair converse has been proved. |
| GD-S3 | open formalization boundary | Probability, spectral-gap-to-invertibility, derivative estimates, ordered multiplicities and asymptotic transfer remain paper proofs. |

The mathematical scope rows are explicit limits, not defects in the accepted theorem. Earlier formal source-v1 is retained as a valid but narrower component.
