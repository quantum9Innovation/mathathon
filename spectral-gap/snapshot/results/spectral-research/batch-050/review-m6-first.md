# First review of m6, exterior resolvent and finite patterns

## Decision

Returned for revision. The absolute walk expansion and finite-pattern calculations are
useful, but Theorem A and the uniform conclusion of Theorem B rely on a gap in the
stochastic Montel step.

## Checked computations

The command `python3 resolvent_patterns.py 8000 3 3.2 11` ran in the member directory
with one OpenBLAS thread. It reproduced:

| Pattern | Measured | Predicted by corrected tree calculation |
| --- | ---: | ---: |
| One vertex | 0.5203657343 | 0.5201568001 |
| Adjacent pair | 1.4846994556 | 1.4833147735 |
| Three neighbours of one centre | 2.1273438555 | 2.1264056325 |

The finite-pair output also matched the reported value. These corroborate the pattern
correction but do not prove its limit. Exact pairing uniformity via `(d!)^n` is correct.
The adjacent-pair and neighbour Schur-complement values are consistent.

## Required proof repairs

1. A high-probability norm bound for each compact set and each $n$ does not produce the
   deterministic uniform bound on a whole modified holomorphic family asserted in
   Lemma 3. The revision must either prove the stochastic Vitali step with that
   distinction explicit or avoid it by a complete exterior argument.
2. The pairing simplicity probability needs an actual enumeration theorem and hypothesis
   check. The present citation number is borrowed from memory and the empirical rate is
   not a substitute.

The limitation about local cycles is not established by the warning in the bulk paper
alone. That warning is not itself a counterexample to the proposed exterior limit.

All other swarm work remains bounded inside batch 050. No formal verification was
claimed in this submission, and no eigenvalue-limit theorem was accepted.
