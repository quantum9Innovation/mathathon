# Accepted revised m3 submission: bounded analytic continuation

## Decision

Accepted after revision. The bounded-domain repair addresses the earlier Harnack
objection, and the unjustified near-$d$ rate claim was withdrawn. This is another
valid exterior-resolvent proof, not a substitute for the m2 rank-one estimate.

## Domain repair

The original submission needed $|g_n|\le M$ throughout its complex domain, but
verified a bound only on a selected start and target region. It now uses a bounded
open rectangle whose closure lies in the resolvent half-plane and contains both a
target compact and an open disc above $d$. The spectral event therefore supplies a
fixed finite bound throughout that rectangle. Three-circles may legitimately be used
there. The $1/n$ factor in that uniform bound is dominated by its value at $n=1$.

## Near-$d$ scope

The revised section proves only that a root converges to the Perron point $d$ by
checking signs at a fixed two-sided window and using monotonicity. It explicitly
withdraws the earlier $O(1/n)$ claim. That withdrawal was necessary: fixed-energy
convergence does not control a root drifting to $d$ at an arbitrary scale.

The stronger $1/n$ law is instead proved by m2's exact rank-one decomposition and
was accepted separately after independent review. It must not be inferred from this
analytic-continuation argument.

## Checks

The regenerated output matches the current script hash `88f44a77...`.
All five Sherman-Morrison checks print `True`. My earlier independent execution of
`checkA` and of every $K_4$ combination of $\Delta=1,2,3$ and the three rational
energies also passed. The original `False` output file was stale, not a counterexample
to the current identity.

The integer-critical exclusion, the exact Perron sign and the adjacent-pair resolvent
correction were checked against the other accepted results.

See the [review of the first submission](review-m3-first.md) for the two original
defects. The revised verdict accepts the corrected argument while retaining all
limits on rate, bulk edge, clustered or growing sets and novelty.
