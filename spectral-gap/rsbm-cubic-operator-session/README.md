# RSBM operator session: recovery without proving real corank one

The decisive observation is that a **polynomial** fixed-field kernel
moment suffices for polynomial Boolean recovery. A sharp `Cp` moment or
a one-dimensional real eigenspace is unnecessary.

The exact star count and elementary entropy bounds give a polynomial
moment for every fixed `d1>d2>0` and every admissible block size. An
aggregate-fiber entropy bound makes the exponent **24 uniformly in the
fixed degrees**, allowing one universal enumeration cutoff. The
root task's conditional-variance/Pinsker inequality gives a strictly
negative entropy exponent for every macroscopic Boolean alternative,
including `(2,1)`. A previously proved small-support estimate handles
the remaining alternatives. These components establish polynomial exact
recovery for the full fixed-degree assortative model. Historical
priority is not asserted; a bounded primary-source audit is included.

## Proofs

- [Cubic recovery proof](POLYNOMIAL-RECOVERY.md): exact `O(N^24)` binary
  kernel moment, both recovery algorithms, complexity, and model transfer.
- [Self-contained cubic paper](cycle-structure/polynomial-recovery-cubic-rsbm.pdf)
  ([LaTeX](cycle-structure/polynomial-recovery-cubic-rsbm.tex)): eight pages,
  including a full independent Boolean rigidity appendix.
- [General-degree count and recovery](GENERAL-POLYNOMIAL-RECOVERY.md): exact
  two-star configuration formula, nonpositive entropy, explicit polynomial
  moment, and an `a>=3` rigidity proof valid also for odd block sizes.
- [Aggregate-fiber moment](AGGREGATE-FIBER-MOMENT.md): the strongest and
  simplest moment bound, `E 2^nullity=O_{a,b}(N^24)` for all fixed degrees,
  with a universal `n^27` candidate cutoff and fixed-degree `O(n^28)` time.
- [Unified Boolean variance-gap audit](BOOLEAN-VARIANCE-GAP-AUDIT.md):
  independently verifies the root's sharper argument for **all** `a>=2`,
  including cubic, without prime-field phase classification.

The fiber-moment and variance-gap notes give a unified all-parameter proof. The
separate sharp-moment argument for real corank one is in the other
session, `../rsbm-cubic-moment-session/full-proof.md`; it is not needed
for the recovery theorem here.

## Algorithm and checks

[`boolean-recovery/binary_recovery.py`](boolean-recovery/binary_recovery.py)
implements cubic `recover` and general `recover_regular(graph,b)` using
exact XOR elimination. The general parity system is `(A+dI)z=b 1` over
`F_2`; candidates are checked for exactly `b` opposite neighbors over the
integers. A polynomial enumeration cutoff bounds worst-case time.

The dependency-free test scripts are
[cubic](boolean-recovery/test_binary_recovery.py) and
[general](boolean-recovery/test_general_recovery.py).

Checks include all 154 ordered simple 2-factor pairs for block sizes
3--5; independent exact pairing/type moments through size 4; an exact
real-corank-two example with a unique Boolean partition; and uniform
simple configuration-rejection samples through block size 1000. General
tests cover odd block size 101 with `(a,b)=(4,1),(4,2),(4,3)`, with hidden
matching and vertex labels. Results are recorded in
[cubic JSON](boolean-recovery/binary-recovery-results.json) and
[general JSON](boolean-recovery/general-recovery-results.json).

## Independent audits

- [Coarse cubic moment and recovery](lift-literature/log-nullity-recovery-audit.md).
- [General exact star count and prefactors](cycle-structure/general-audit/general-star-audit.md).
- [General Boolean equality and rigidity](boolean-recovery/adverse-audit-generalization.md).
- [Primary-source priority and applicability](lift-literature/recovery-priority-audit.md).
- [Adverse audit of the separate sharp central saddle](lift-literature/central-phase-adverse-audit.md),
  with exact support-lattice checks at primes 3, 5, and 7.
- [Adverse audit of the separate entropy and near-constant phases](boolean-recovery/adverse-audit-moment-phases.md).

The uniform-simple model is obtained by conditioning configuration
factors on simplicity, an event of constant probability at fixed
degrees. No proof here imports a uniform-permutation 2-factor theorem by
contiguity. A separate quantitative change-of-measure lemma is in
[permutation-to-uniform-transfer.md](lift-literature/permutation-to-uniform-transfer.md).
