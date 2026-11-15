# Draft launch task for batch 050

Solve one bounded mathematical problem, not a general spectral survey. The goal is the
finite-defect resolvent and limiting eigenvalue problem prepared in
`results/spectral-research/batch-050/README.md`. Read that file completely before
registering a direction, plus `source-baseline.md`, `.ultramath/smwgfcleu/m5/DOSSIER.md`
Sections 1, 2.3, 2.5, 4 and 10, and `results/spectral-research/reviews/d3-first-review.md`.

The exact added-vertex determinant identity and spiked-tree spectrum are established.
The fixed-host resolvent limit and resulting finite-root law are not established. Fix
$d\ge3$ unless your route explicitly proves a different, fully labelled degree regime.
Do not substitute expectation for in-probability convergence, random $T$ for fixed $T$,
the one-sided tree resolvent branch for the full Kesten-McKay transform, or real-energy
limits for complex-$z$ bulk estimates without proof.

Register exactly one narrow direction matching one of the six prepared roles:
1. bounded-local-cycle concentration,
2. source applicability and closest existing proof,
3. nonbacktracking exterior resolvent expansion,
4. extension of the local-law domain to exterior real energies,
5. secular-root reduction under an explicitly minimal resolvent hypothesis,
6. adversarial counterexample and independent theorem verification.

Work independently and share concrete findings on the board. A direction is not
successful because it produces more numbers. Prove a claim or make its missing estimate
and the candidate counterexample explicit. Every imported theorem needs version,
number and verified hypotheses. Every numerical experiment must use reproducible
parameters, fixed seeds and honest sampler limits. `networkx.random_regular_graph` is
not certified uniform sampling. No novelty claim follows merely from a short search.

Respect the three gates in README.md: target correctness by 45 minutes, an actionable
proof reduction by 90 minutes, and the last 45 minutes for independent review only.
Do not continue a refuted target unchanged. Save proofs, source notes, counterexamples,
scripts and complete raw outputs under your member's project workspace so a reviewer
can rerun them. The final coordinator will decide acceptance against the tiered
criteria in README.md. A plausible but incomplete asymptotic argument is not enough.

Write a compact report naming your strongest result, its exact theorem or obstruction,
and the next unavoidable step. Preserve all limitations, including if the only defensible
outcome is that the original resolvent hypothesis was not proved. No Lean file is
mandatory, but any claimed formal proof must compile without sorry and have its statement
independently audited.
