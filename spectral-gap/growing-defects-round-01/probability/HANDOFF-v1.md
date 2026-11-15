# Probability proof handoff

Date: November 15, 2026, America/Los_Angeles.

Task: prove R1 and R2 for predetermined growing marked sets. Sender: probability workstream. Intended recipient: root integrator and a separate reviewer.

The exact frozen output is [proof-v1.md](proof-v1.md), SHA256 `56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b`.

The input packet hash is `0575afeaf42b43693ffbff4e2f3f20afb9386b52f49404d8e2753434917a55f8`. The SG-17 proof and review hashes are preserved in Section 10 of the frozen proof. No other new attempt was read before freezing.

## Output and hypotheses

Theorem 1 is an explicit finite-n tail bound for the marked projected resolvent and every derivative order. The graph is uniform simple labelled d-regular, d>=3 fixed, with nd even. The marked set is deterministic before graph sampling. The finite bound retains the actual simplicity probability and host-gap exceptional probability.

Corollary 2 proves the collective-scale estimate for every sequence with m cubed times log(n) squared divided by n tending to zero. The same range gives convergence of every fixed positive derivative order. Thus the originally requested m<=n^(1/3-epsilon) range is included and modestly enlarged, without changing the model.

The output also includes dimension-free local derivative bounds and the explicit probability bound d m(m-1)/(2(n-1)) for any marked host edge. No independence between these events is required.

No new canonical claim ID was assigned. Proposed status is complete paper argument awaiting separate review. Nothing is formally verified by this output.

## Checks and limitations

The proof reconstructs the nonnegative diagonal-return estimate, unconditional off-diagonal symmetry, stationary subtraction and operator tail. A separate exact arithmetic check verified the two weighted-sum formulas at 909 pairs of integer parameters, and the tree derivative and tuned derivative constants at 48 degrees. Those finite checks corroborate algebra only and are not premises of the general proof.

The logarithmic loss is not claimed sharp. The estimate does not cover a graph-dependent choice of labels, a simultaneous maximum over all marked sets, a bulk-edge shrinking window or a limit distribution of residual errors. The deterministic transfer still owns all augmented-graph root counts and ordering.

## Requested next action

Independently reconstruct equations (11) through (22) of the exact frozen revision, then check Corollary 2. In particular, confirm that the off-diagonal expectation remains under the unconditional simple graph law and that the projected tail is bounded as an operator. Return findings against this SHA256. Corrections, if needed, belong in a new proof revision.
