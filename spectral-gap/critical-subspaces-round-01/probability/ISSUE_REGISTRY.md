# Refined resonance probability issues

November 15, 2026.

| ID | Status | Issue and disposition |
| --- | --- | --- |
| SUB-PROB-01 | addressed in current proof | A full marked-operator error that vanishes only at the first spectral scale does not resolve collective-pair splitting. The current argument instead controls the compression and squared column error on the selected finite sector. |
| SUB-PROB-02 | explicit boundary | Conditioning on a particular rare pair could invalidate unconditional exchangeability bounds. The proof samples a uniform marked subset after the host and bounds pair-selected sums before conditioning. |
| SUB-PROB-03 | open at finer precision | The negative individual-mode basis is not determined by an error that is only small relative to m^(-1/2). Distance-dependent tree resolvent corrections have size (log n)/m in scaled units. No universal negative basis law at scale 1/m is asserted. |

Prior frozen proofs and canonical records are unchanged.

## SUB-PROB-04: Distinguish three negative precision levels

Status: addressed in `negative-log-scale-v1.md`, awaiting separate review. The first phase and zero m^(-1/2) detuning do not specify the finer tuning. The logarithmic parameter `(w-kappa)/(s r)` separates the collective and pair sectors except at -kappa^2/2. Exact phase is now resolved for the corrected retained operator. The graph-normalization bridge and the smaller 1/m law remain separate obligations.
