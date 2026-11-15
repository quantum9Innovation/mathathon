# Completed close-pair transition round

November 15, 2026, America/Los_Angeles. Sender and integrator: root. Intended recipient: the next spectral research session.

## Task and outcome

The user asked whether close marked pairs create a genuine transition near m=n^(1/3), requested removal of the logarithm, priority checking, independent reviews and formal key steps.

All parts of that bounded task are complete. SG-22 removes the logarithmic loss by two distinct proofs. SG-23 proves sharp necessity and actual eigenvalue divergence using close pairs. SG-24 identifies the postcritical scale m^2/n below sqrt(n), gives the full cluster width, and records critical tightness with divergent normalized expectations. The [frozen synthesis](root/transition-synthesis-v1.md) is the main reading artifact.

## Exact central revisions

| Item | SHA256 |
| --- | --- |
| root/nonbacktracking-upper-v1.md | d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896 |
| probability/chebyshev-proof-v1.md | d9265e631ea99465eb243aaeecda7ad5a6d27c92b977ebe3b4cf185ac411a011 |
| obstruction/proof-v1.md | cadd1408ff45526a328b78f7b2f063fa599278603e90282c216e364c68280a35 |
| obstruction/weighted-extension-v1.md | 3ffd9f003e3e4c3d94be96a9ff831f666da815e631eed531cdcbf1ba5d0f33d1 |
| obstruction/pair-scale-v1.md | 272cdb331e73e23aecc36685cb62211c9733d50022e438c6e7fa7f5fb18c505a |
| root/cluster-width-v1.md | e40164dcf711cca13d945b666645c26aa8095b835e1e727d2d6d7159a78e7b8f |
| root/transition-synthesis-v1.md | 4e53c4f754e5e80f78dc6ae0a4260eefb67152f37dd66b343ef3556e108417e5 |
| reviews/transition-synthesis-v1-review.md | c5e6d7e546122e1681502fb4816210e8cd0e3f5ab7f985216090307fb1b6342a |
| formalization/SOURCE_MANIFEST-v1.json | a656f70c2fb4d79f8d4ccd729f900681b41ccb18bc4759c5927c3a27a0ac8785 |
| reviews/formal-scope-v1.md | 5b0ad9280eedf3048415f60252c3eec8f904f4e727dc240bed95803adb341f7c |
| reviews/formal-replay-v1.json | 79c8244228699a08e52b4739fa5f466eeb9a878b14c05084a0bc143d935f389c |

The [verification inventory](VERIFICATION.json) binds every current-round file and the preserved preceding inputs. Separate reviews check the upper proofs, lower proofs, synthesis and formal scope. All declared findings are resolved, and no frozen proof needed a corrected revision.

## Formal and literature limits

Twenty new finite theorem declarations compiled without warnings and passed the axiom audit in both the author run and an independent isolated replay. The dependencies were read from the pinned existing cache, not rebuilt. Exact encoded objects and remaining graph, analytic and spectral bridges are in the formal README. The full transition theorem is a paper result, not an end-to-end formal certificate.

Priority checks compared splitting graphs, sparse-matrix polynomial decay, tree scattering, local resonances and growing-rank perturbation theory. The methods are credited. No exact prior statement was identified in the bounded comparison, but firstness and a published open-problem match are unverified.

The upper matching scale stops at m=o(sqrt(n)). The lower divergence continues to m=o(n). Predetermined marks, weighted attachments outside degree three, and the distinction from normalized-Laplacian or mixing claims remain essential.

## One next action

Follow the [proposed critical-law target](NEXT_PROBLEM.md): prove an effective operator retaining close-pair interactions and determine whether the top eigenvalues have a full-sequence or only a lattice-dependent subsequential limit. A localized eigenvector conclusion is not yet available.

The round stops because the requested transition, logarithm removal, matching structural extension, bounded priority audit and key-step formal verification are complete. No background runner, external correspondence or submission remains active.
