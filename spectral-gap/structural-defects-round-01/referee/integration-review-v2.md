# Integration acceptance, revision 2

November 15, 2026. Reviewer: fresh_referee. Recipient and integrator: root. Frozen after checking the explicit integration corrections.

## Decision and scope

Accepted at the six exact target revisions below. INT-01, INT-02 and INT-03 from integration-review-v1.md are resolved. No unresolved integration finding remains.

This accepts the presentation, statement scope, constants, evidence counts and historical target wording. It is not another independent mathematical proof, a new compiler replay or a historical-priority certification. The mathematical audit, finite formal scope and imported probability qualifications remain as described in the prior reviews.

The first integration review is preserved unchanged at SHA256 7774b12230ff46f459c80ae0d990101ee278f83ca001d85681ae22ade3b1c779. All six initial target texts are preserved under reviews/integration-input-v1/. Their snapshot bytes were checked against the original hashes recorded in revision 1.

## Exact accepted targets

Paths are relative to spectral-gap/. Each hash below was checked against disk after the corrections.

| Target | SHA256 |
| --- | --- |
| structural-defects-round-01/README.md | 9f16b820906f70c0dbbc51f9b7eb6c45dfe318f02422bddd8ee1aa8bad8b99cc |
| structural-defects-round-01/EXPLANATION.md | fff6289ba28f45ed58a96dee35d9795059771163e101151722e4038ef8ba8cff |
| structural-defects-round-01/NEXT_PROBLEM.md | 95be8a598cb2d773a772a6a007821dafcc4c25b9c58e223a3619c4c73792ec57 |
| README.md | 1157571b717ee5c4c6919f3b8044fd2207947cf5d96269e7150bc4ae6258e824 |
| CONTRIBUTION.md | 97a08695b97f5f6343feb0537119725f7c1b92f50f80d6c9f9a2913d0c0f1f14 |
| CLAIM_LEDGER.md | 4b3b9b49945dc080db77bc381a2b7c821adacc4cee84c59dfdc70404cd57fe60 |

NEXT_PROBLEM.md and CONTRIBUTION.md are unchanged from the first review. The other four target changes are the narrow presentation corrections below. No theorem source was changed. The vector-port, sharp-growth and retuned-graph source hashes remain respectively ff889b703f36bdf1bea9854c20c41b97578abdd92a474fc5e7c6bcc03472cde8, db71f673c134ffd6b58cf2fa3d47e8dd0532f12793321742672affa97093e88b and 5c2b7bd527a47ca2c870ada456a5bd57e985ffafe5e949cf3dfb595dda537e6e.

## Explicit finding resolutions

| Finding | Resolution checked | Status |
| --- | --- | --- |
| INT-01 | The SG-28 ledger cell now says the retuned logarithmic crossing was open in that frozen round, identifies SG-30 as resolving its stated finite deterministic retuning, and retains finer bases inside repeated pair groups as open | Resolved in CLAIM_LEDGER.md at 4b3b9b49945dc080db77bc381a2b7c821adacc4cee84c59dfdc70404cd57fe60 |
| INT-02 | EXPLANATION.md now requires marks forming an independent vertex set in the host and gives the equivalent condition E transpose A E=0. The round README now describes the five cancellation checks using the same independent-set condition | Resolved in EXPLANATION.md at fff6289ba28f45ed58a96dee35d9795059771163e101151722e4038ef8ba8cff and the round README at 9f16b820906f70c0dbbc51f9b7eb6c45dfe318f02422bddd8ee1aa8bad8b99cc |
| INT-03 | The canonical README opening explicitly includes nonzero stationary coupling alongside one simple local resonant channel | Resolved in README.md at 1157571b717ee5c4c6919f3b8044fd2207947cf5d96269e7150bc4ae6258e824 |

For INT-02, the diagnostic source was also inspected at its boolean definition. It computes independent_marks from the absence of nonzero entries in inclusion transpose times adjacency times inclusion. Thus the corrected prose states the condition actually tested by the diagnostic and required by the finite compact-mode identity.

The corrections preserve the scope of the sharp equivalence, the narrower postcritical upper range, the cubic fine-law constants, the grouped projector conclusions, the 57 new plus 16 reused declaration count, the eighteen finite motif cases and the bounded nine-source priority comparison. No weakening or expansion of a theorem was introduced.

## Handoff

The passed checks in integration-review-v1.md remain valid for these narrow revisions. Link this acceptance after the first review and mark INT-01 through INT-03 resolved in the integration evidence record. Keep the original target snapshots and both reviews. Any later substantive target change requires a new hash-specific check.
