# Independent formal replay and scope audit

November 15, 2026. Reviewer: root. Decision: accepted for the finite statements explicitly listed below.

Frozen targets:

- [Source manifest](../formalization/SOURCE_MANIFEST-v1.json), SHA256 57cd3e0e5c82c029a1cba48767c9819635ca753db8329656b4aa6ea4381b0d63.
- [Scope document](../formalization/README.md), SHA256 510462a8f2a22d08fa1ec673d8816c198006839fe63860b6d522e4b5adc41742.
- [Validator](../formalization/validate.py), SHA256 b73d33e6d9bc796d42d0e9fe70cae6ecf23a6a98e440634988256e57ecc87168.
- [Author receipt](../formalization/validation-v1/CHECK.json), SHA256 20ca4e73ff6dab085bc65d772e7086d80b63e58b9678b5f9cf7745a2fd2ee2f6.

The reviewer read all three new source modules, the scope document and the validator. The two copied source modules had already been read and audited in the preceding round. Their hashes remain identical to those earlier sources. The mathematical finite normal form was independently reconstructed in the [separate algebra review](finite-resonance-by-root-v1.md). This exposure is disclosed.

## Actual formal content

ExactModes proves coordinate actions for the full coupled star and pair matrix, not an assumed effective action. Its antisymmetric pair vector is nonzero and remains an exact eigenvector. Equal-weight symmetric pair differences are also nonzero eigenvectors with zero host coordinate. The general zero-sum profile equation allows a zero profile, and the scope document correctly distinguishes it from the nonzero eigenvector statements.

AggregateBlock constructs the actual linear embedding of three coordinates into host, constant free and constant pair coordinates. Positivity of both coordinate counts is required where divisions by their square roots occur. Injectivity and the exact squared Euclidean norm identity are proved. The intertwining theorem establishes an invariant linear-map range and lifts actual nonzero eigenvectors. The determinant is computed from the concrete three-dimensional matrix.

ResonanceBlock proves the actual orthogonal collective basis change, the normalized three-dimensional determinant and the two-dimensional characteristic equation. Both explicit two-level vectors are nonzero when the coupling is nonzero, and their roots are distinct. The equal-mass theorem concerns the two coordinates at zero detuning. It does not claim equal physical graph masses or an exact reduction of the finite three-dimensional matrix to two dimensions.

All 24 new declarations concern actual finite objects. The 23 copied declarations are recorded separately. The sources do not encode a full basis or multiplicity count for the coupled matrix, the asymptotic elimination of the third coordinate, a random graph, spectral projection perturbation, the host-resolvent lift or physical graph localization.

## Fresh replay

The reviewer copied the formalization directory to a fresh temporary directory and ran its copied validator. All five source files compiled in dependency order, producing fresh temporary compiled outputs. The retained [reviewer receipt](formal-replay-v1.json), SHA256 03c2d42e0cb302305480ee3b5dfd1ab16af8ad1c4719fc606005d4acd3bbab8a, reports 24 new and 23 reused declarations. All passed, with no warnings and only propext, Classical.choice and Quot.sound in their axiom lists. The original author receipt was checked unchanged after replay.

The validator checks source and manifest bindings, compiler version, dependency checkout revisions, declaration coverage and axiom lists. Each compilation is limited to two threads, 4096 MB and 120 seconds. The fresh output directory is first in the import path, so the copied local modules are compiled and used rather than replaced by prior local compiled artifacts. Previous success receipts are removed before each run.

Lean 4.31.0 and the pinned mathlib revision are retained. Installed compiler and cached dependency objects remain trusted inputs. Dependencies were not rebuilt, and checking source revisions is not a cryptographic audit of every cached object.

## Finding status

No formal statement or scope correction is required. This acceptance covers supporting finite algebra and the successful source replay. It does not certify the graph subspace theorem, the random limiting law, the spectral transfer or historical novelty from end to end.
