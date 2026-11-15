# Integration review, revision 1

November 15, 2026. Reviewer: fresh_referee. Recipient and integrator: root. Frozen before integration corrections.

## Decision

The integrated theorem scopes, constants and evidence counts agree with the frozen proofs and final priority addendum, subject to the two presentation corrections INT-01 and INT-02 below. INT-03 is a recommended hypothesis clarification. These findings do not refute a mathematical theorem or reopen the independent proof review.

This is a presentation and integration check. It is not another independent proof claim, a formal replay or a fresh literature search. The prior independent mathematical audit is structural-and-retuned-review-v1.md, SHA256 63566e44472708e94b98a9b929c1ea73a7e93fc419478633b91f4404991ac7cf.

## Exact reviewed revisions

All six requested hashes matched disk when the review began.

| Target, relative to spectral-gap/ | SHA256 |
| --- | --- |
| structural-defects-round-01/README.md | 01691714dc051675123a3300172e6cd745399ac1a7a713206bb0d683ed8e3c4c |
| structural-defects-round-01/EXPLANATION.md | b19164d0c8b64d8edc2147941f627ecd6c02f504363325cc26b900b462b2f26d |
| structural-defects-round-01/NEXT_PROBLEM.md | 95be8a598cb2d773a772a6a007821dafcc4c25b9c58e223a3619c4c73792ec57 |
| README.md | da7bc4e3e986a87bbd29ad11d8e443d74ace4a2d4d92a4d1b1347727b384b89b |
| CONTRIBUTION.md | 97a08695b97f5f6343feb0537119725f7c1b92f50f80d6c9f9a2913d0c0f1f14 |
| CLAIM_LEDGER.md | 57ba1a818d5d5271e7c04277c494c132be9e550b0289d041d32cebe963f544de |

The comparison also read the frozen sharp-growth extension, final priority addendum, scalar-port and triangle examples, formal packet description, source replay receipt and finite diagnostic receipt. Supporting hashes checked during this review are:

| Supporting evidence in this round | SHA256 |
| --- | --- |
| root/sharp-growth-v1.md | db71f673c134ffd6b58cf2fa3d47e8dd0532f12793321742672affa97093e88b |
| priority/FINAL_SCOPE-v1.md | 3fd8bca9b3b90f5b6b1337c3a0438c810ede404f5a0b64178bab72c19bb8db0a |
| formalization/README-v2.md | 43735ac99f1a4695fec21a3c802ec726aa4066b44b01f7d181e02f14df9b3431 |
| reviews/formal-replay-v2.json | 80cc664e28e34fe222340366a95eca0dbc6964ea05ce8ac3c76c7421c76a3a5e |
| root/graph-diagnostic-v1.json | 0baaf31cbaa443ce3d2e230a71de7749ddfb4a110e7f602831c291cbff421fa2 |

The integrator is producing EVIDENCE_DAG.json, EVIDENCE_CHECK.json, VERIFICATION.json and HANDOFF.md concurrently. Their transient absence was explicitly outside this review's finding scope.

## Findings

### INT-01. Historical open-target wording is still present tense

Status: open in the initial CLAIM_LEDGER.md revision above. Required presentation correction.

The SG-28 review cell ends with: "The exactly retuned logarithmic crossing and finer bases inside repeated pair groups remain open". The new SG-30 section correctly resolves the finite deterministic retuning, and the canonical README and contribution summary already explain that transition. The older cell nevertheless presents both items as currently open.

Requested correction: state that these were left open by SG-28, then identify the finite deterministic retuning as resolved by SG-30. Retain the finer repeated-pair basis problem as open. This changes the current ledger's historical description without modifying the frozen earlier proof or changing SG-28's original theorem scope.

### INT-02. Compact-mode example needs graph independence of the marks

Status: open in the initial EXPLANATION.md revision above. Required scope clarification.

The explanation says that "independently marked vertices" can support the exact compact modes for coupling (dI-A)E. The finite proof requires the marked vertices to form an independent set in the host, equivalently E transpose A E=0. Independent random selection of marks is a different condition and does not ensure that finite identity.

Indeed the proposed compact vector (Et,t) has lower output E transpose (dI-A)Et=d t-E transpose A E t. The extra term vanishes for all t precisely under the stated independent-set condition. Random predetermined marks have that property with high probability in the cited dilute range, but the exact algebra itself uses the deterministic condition.

Requested correction: use "marks that form an independent set in the host" or "marks with no host edges between them". The round README's "independent-mark cancellation checks" should use the same precise wording when describing the five diagnostics. The receipt's boolean independent_marks field was interpreted as the graph condition and not as a claim of probabilistic independence.

### INT-03. State the nonzero stationary coupling in the canonical opening

Status: optional clarification in the initial canonical README.md.

Its opening describes the class using one simple local resonant channel, then immediately states the sharp collective criterion. The linked theorem, round README, contribution summary and ledger correctly add nonzero stationary coupling. The cancellation example demonstrates that this condition matters.

Requested correction: include "nonzero stationary coupling" in the opening class description. No further expansion of the technical hypotheses is needed in that short summary.

## Checks that passed

### Theorem scopes and growth ranges

The sharp equivalence is stated for 1<=m=o(n), while the uniform upper width and matching postcritical top scale stop at m=o(sqrt(n)). The explanation table and SG-29 ledger cell preserve this distinction. They do not extend the upper bound into the full lower-obstruction range.

The critical isometry rate is presented in the critical-growth context. The broader class allows fixed weighted and signed data with a simple positive-semidefinite local resonance and nonzero stationary coupling. Adaptive marks, multiple critical channels and irregular hosts are not claimed.

The SG-30 summaries retain deterministic finite beta, cubic duplication, the logarithmic center, physical scale s squared=m/n and whole pair-group projections. They correctly distinguish zero leading signed mixing from random diagonal ordering. They do not reuse the cubic fine constants for every SG-29 attachment or claim a basis inside a repeated pair group.

### Constants and examples

The explanation's three unweighted examples match the frozen scalar and triangle calculations:

| Example | kappa squared | h | Pair added-vertex mass |
| --- | --- | --- | --- |
| Cubic duplication | 9/8 | 3/4 | 1/8 |
| Triangle attached at two vertices | 18/31 | 12/31 | 11/31 |
| Seven-leaf star attached at its center | 9/26 | 3/13 | 8/13 |

The general formula h=(d-1)kappa squared/[d(d-2)] is consistent with all three cubic values. The table's added-vertex counts 1, 3 and 8 agree with the actual constructions.

The fine law's center, pair coefficient 33/16-beta, collective constant 51/32, Poisson intensities (kappa theta/2)2^k and screened kernel kappa t/(kappa+t) agree with the frozen theorem. The physical mass triples in the SG-30 cell agree with the graph reconstruction.

### Evidence counts

The source replay receipt records 57 current-round declarations and 16 reused declarations, totaling 73. Summing its per-source theorem inventories independently reproduces those numbers. The 57 consist of 10 PortEnergy, 11 CancellationModes, 18 AttachmentLift, 9 StarSeven and 9 ArrowSchur declarations. The 16 reused declarations are 6 ProjectedResolvent and 10 InverseBridge declarations. Revision 1 and revision 2 totals are not added together in the summaries.

The diagnostic receipt contains six hosts, three motif cases per host and five nonnull compact-cancellation checks. All five have zero recorded residual and matching actual and expected rank. The maximum recorded identity error across the eighteen cases is 4.310506636229751e-14, below the summary's 4.4 times 10^(-14) bound. The summaries correctly call these finite consistency checks, not evidence proving an asymptotic law. No diagnostic or compiler replay was rerun for this integration check.

The priority audit contains nine direct primary-source comparisons. The final addendum and integrated summaries do not turn that bounded comparison into a historical-firstness certificate. They keep the locally resolved retuning problem distinct from a named published open problem. Supporting declarations and motif examples are not counted as separate solved open problems.

### Next-problem boundary

NEXT_PROBLEM.md is explicitly a proposed future investigation and does not launch work. Its multiple-local-channel target is outside the current simple-kernel theorem. It asks for the actual matrix metric, a decisive r=2 attachment, exact versus asymptotic dark modes, and an error below any proposed smaller scale. It preserves the current proofs and does not present the proposed extension as already established.

## Required resolution and handoff

Apply INT-01 and INT-02 to new integration revisions, and preferably INT-03. Preserve the initial reviewed texts and this report. Send the revised hashes for a separate revision-specific acceptance that resolves each finding explicitly. No root document was edited by this reviewer, and no mathematical claim status was changed.
