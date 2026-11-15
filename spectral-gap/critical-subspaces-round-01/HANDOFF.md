# Critical subspace and resonance handoff

November 15, 2026. Task: critical-subspaces-round-01. Sender and integrator: root. Intended recipient: the next bounded spectral research round.

## Base and achieved results

The base is the [frozen input](input/NEXT_PROBLEM-v1.md) and [run contract](RUN_CONTRACT.json), using the accepted critical-law, close-pair and growing-defect rounds. Earlier frozen proofs and manifests are unchanged.

The current packet proves the actual graph spectral subspace theorem at every fixed nonzero critical level, including pair multiplicities and collective collisions. It constructs a near-isometric physical lift, proves basis-independent mass operators and establishes spatial concentration of noncollective level subspaces near their pair endpoints.

The graph resonance theorem determines the positive avoided crossing and the negative logarithmic splitting. Positive mixing is governed by the actual two-level matrix with off-diagonal kappa sqrt(p), on physical scale n^(-1/2). At exact leading resonance the two bright eigenvectors have physical masses (1/4,3/32,21/32). Negative collective and pair sectors split on physical scale s squared r, with coefficients -kappa squared/2 and -kappa squared at exact phase. The graph-normalization bridge is proved, not left conditional.

Integer tuning realizes both the square-root detuning tau and the logarithmic detuning a. The same first-order phase and tau=0 can give different ordered negative eigenvector masses in the actual graph. At a=-kappa squared/2 the logarithmic coefficients collide again. That retuned crossing remains open.

## Exact revisions

| Artifact | SHA256 |
| --- | --- |
| root/subspaces-v1.md | f13fbd47ba04bd638f4bafe940c20d604bfa4a4653df553b4b737f2e3779e87a |
| probability/refined-resolvent-v1.md | bd00db6c2f69813d480f5a86d5d22c8b6fe4922d9cc3d233f72840dddb29f8df |
| resonance/finite-normal-form-v1.md | 59bebac4b6a96d148d48830bf27130223d6820e53e16627720fb7f2f7216eed7 |
| probability/negative-log-scale-v1.md | faced6a02d91d451e4ef0e0989d3d46811da66d809d40e9344e9444012901409 |
| root/graph-resonance-v2.md | 907d90af7ea1af8a59ec49c100869046e01e3ffd251e81a55239a054bb59f289 |
| formalization/SOURCE_MANIFEST-v1.json | 57cd3e0e5c82c029a1cba48767c9819635ca753db8329656b4aa6ea4381b0d63 |

Use graph-resonance-v2 as the final synthesis. Its only changes from revision 1 are a revision note and the restored additive plus signs in equations (17) and (18). Both revisions remain available. The [issue registry](ISSUE_REGISTRY.md) preserves the finding and its resolution.

## Review and verification boundaries

The [README review map](README.md) links each paper proof to its separate exact-revision audit. The two complete graph application reviews disclose the finite-algebra and probability authors' respective exposure. The negative probability proof was separately reconstructed by the finite-formal workstream. The [evidence dependency record](EVIDENCE_DAG.json), [consistency check](EVIDENCE_CHECK.json) and [final verification](VERIFICATION.json) bind artifacts and review targets.

The finite formal packet has 24 new declarations and 23 copied declarations, counted separately. A fresh source-only replay passed with the original receipt preserved. The [formal scope audit](reviews/formal-scope-v1.md) identifies the actual finite matrices, invariant range, nonzero eigenvectors and remaining bridges. No full probability space, graph subspace transfer or asymptotic graph theorem is encoded. Pinned compiled dependencies were read without being rebuilt.

The scientific figure evaluates the limiting formulas. Its 303 positive and three negative checks are numerical corroboration of those formulas, not evidence replacing the proof. It is not a finite-graph simulation.

The primary-source comparisons identify substantial established perturbation and resonance methods. They find no directly supplying theorem in the inspected models, but do not establish historical firstness or resolution of an identified published open problem.

Native delegated tasks completed this round. The research_lab scheduler was not executed. No external submission, correspondence or unattended job was started.

## Requested next action

Start from [NEXT_PROBLEM.md](NEXT_PROBLEM.md). Resolve the retuned negative crossing by retaining the order-s graph normalization and the next collective centering. Begin with one resonant pair. Keep the current two-scale theorem intact and do not infer the missing finer basis from an o_P(sr) error bound.
