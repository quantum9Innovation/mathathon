# Sources and evidence for the close-pair obstruction

November 15, 2026, America/Los_Angeles.

The probability input is the positive limiting simplicity probability of the fixed-degree configuration model. The previous round directly inspected Angel, van der Hofstad and Holmgren's regular-degree formula

\[
\mathbb P(\text{simple})=
\exp\left(-\frac{d-1}{2}-\frac{(d-1)^2}{4}\right)+O(1/n).
\]

At d=3 this is exp(-2)+O(1/n). See the primary paper [Limit laws for self-loops and multiple edges in the configuration model](https://arxiv.org/abs/1603.07172) and the exact retained-source discussion in the previous [full-chain review](../../growing-defects-round-01/reviews/combined-v1-review.md), Section P1. This round reuses that inspected dependency. It does not claim to reconstruct the source's complete proof.

All further probabilistic estimates in [proof-v1.md](proof-v1.md) are derived there from uniform pairing exposure and sampling without replacement. The tree Green kernel follows by its radial resolvent recurrence. The Schur identity and variational witness are explicit finite-dimensional algebra. These are classical tools, not methods claimed as new here.

The problem packet was read from [PROBLEM-v1.md](../input/PROBLEM-v1.md), together with the run contract. Prior exposure includes the accepted previous-round graph, transfer and eigenvector proofs and their reviews, plus the integrator's description of the close-pair heuristic. Neither the current-round probability attempt nor the integrator's current subcritical proof was read before freezing this obstruction.

Historical priority is assessed separately in the owned priority directory. The proof makes no claim that the target was previously published as an open problem or that its resolution is historically first.
