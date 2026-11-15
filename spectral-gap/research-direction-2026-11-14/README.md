# Spectral graph research direction

November 14, 2026, America/Los_Angeles.

This chat is devoted to spectral graph theory and spectral gaps. The research objective is to understand how local graph geometry produces global spectral outliers, resonances and rare failures of a spectral bound. The intended contribution is a predictive theory with explicit hypotheses, not a larger count of related lemmas.

The current decision is to develop quantitative marked-resolvent control and interacting defects as the next constructive investigation. Sharp tangle-controlled probabilities in random lifts are the larger graph objective. A bounded investigation of the original one-phase K4 proposal has also produced an explicit obstruction, whose exact proof and separate review are linked below.

## What the existing work supports

The authoritative record remains [CLAIM_LEDGER.md](../CLAIM_LEDGER.md). No second mathematical ledger is introduced.

| Evidence family | Supported contribution | Boundary |
| --- | --- | --- |
| Mixed permutation moments | Compatible conditioning, a replacement proof of the requested estimate, and attained extrema for zero, one and two conflicting singletons | Additional graph path sums and tangle estimates are needed for a new spectral theorem |
| Diagonal asymptotics | Sharp cubic scaling, parity transitions and uniform refinements | Several statements share one mechanism, and classical special-function overlap is substantial |
| SG-17 | Fixed-root resolvent precision and critical splitting for one cubic neighbourhood duplication | An isolated Perron resonance, not a bulk-edge transition or growing-defect theorem |

SG-04 mathematically answers the optimal-scale question in Collins and Nagatsu's published Remark 3.4. The [source passage](../audit-2026-11-14/collins-nagatsu-published.txt) and [priority assessment](../extension-round-02/PRIORITY_SYNTHESIS.md) distinguish that conclusion from historical firstness.

A fresh file inventory found no Lean, Coq, Isabelle or Agda source or toolchain files in the spectral topic or its reconciliation directory, including hidden directories. The existing spectral results are paper proofs with recorded internal reviews and computational corroboration. Typeset theorem blocks are not proof-assistant formalizations. This round does not rerun the full historical proof chain.

## The larger mathematical question

Which finite local structures create a spectral outlier, when do their modes interact, and how accurately can their frequency predict the probability that a sparse graph misses a target spectral bound?

A useful answer would connect three genuinely different obligations:

1. A deterministic rule mapping a marked local geometry to possible eigenvalues and localized vectors.
2. A probabilistic approximation transferring that rule to a finite random host, at the scale where the predicted modes split or collide.
3. Matching probability bounds for degree-compatible structures that arise spontaneously in the specified graph ensemble.

The first step alone is largely established spectral and scattering machinery. The [tree scattering theory of Colin de Verdiere and Truc](https://arxiv.org/abs/1209.1001v2) and [finite-rank perturbation theory of Benaych-Georges and Nadakuditi](https://arxiv.org/abs/0910.2120v3) are important baselines. Our possible contribution lies in new uniformity, critical-scale control, interaction laws or sharp graph-event probabilities.

This would be a structural synthesis within an already connected area of mathematics. It would become a meaningful new perspective if one theorem predicted behavior across substantially different local geometries and graph models. Neither that theorem nor a unification of whole fields is claimed.

## Three research questions

| Question | Concrete first target | What would make it substantial |
| --- | --- | --- |
| How do many local resonances interact? | The growing collection of duplicated cubic neighbourhoods in [NEXT_PROBLEM.md](NEXT_PROBLEM.md) | Uniform operator control for a growing marked set, followed by a real transition or interaction law |
| Which rare local structures determine gap failure? | For one fixed internal interval in the positive gap of K4,3 lifts, classify the lowest-excess admissible structures and seek matching probability powers | A lower witness together with an upper bound excluding other mechanisms |
| Can phases suppress the responsible structures? | Test cycle holonomies against the actual minimal tangles, after the one-edge obstruction below | A provable change in the tail coefficient, threshold or power in an explicitly different regime |

These are proposed investigations. The first target has the closest proof foothold. The internal-gap programme is harder and has no asserted optimal exponent. For K4,3, the positive gap is between zero and sqrt(3)-sqrt(2) in raw adjacency units. Structural zero modes and the old lift sector must be removed from any proposed event.

Deliberately adding vertices changes the degree sequence. A theorem for inserted defects does not establish occurrence probabilities for spontaneous defects in a regular graph. That model bridge is an explicit mathematical obligation.

## An obstruction in the original phase model

The [frozen proof](phase-obstruction/proof-v1.md) studies precisely the original independent-permutation K4 lift with one phased base edge. The unphased K4 minus that edge occurs with probability asymptotic to 1/n. Its completion by two binary trees supports an eigenvalue

\[
\lambda_*=r+2/r>2\sqrt2,\qquad r^3-r-2=0,\quad r>0.
\]

For every fixed \(0<\delta<\lambda_*-2\sqrt2\), the proof gives a graph event of probability at least \(1/n-C_\delta/n^2\) on which the largest new-sector eigenvalue exceeds \(2\sqrt2+\delta\) for every phase simultaneously. The normalized excess range is approximately \(0<\varepsilon<0.002516264778\). Exact algebraic values govern the claim.

This rules out an o(1/n) upper tail in that range by changing only the one phase, even if that phase is selected after observing the graph. It leaves constants, larger thresholds, conditioning away tangles and changes to other cycle phases open. The argument uses established tangle ideas, with no historical-firstness claim.

The [separate exact-revision review](reviews/phase-obstruction-v1-review.md) accepts the lower-bound proof with no unresolved mathematical finding. The canonical ledger records the later acceptance. The frozen proof retains its original awaiting-review header. The external upper bound and historical priority are outside that review.

## Current literature prevents stale targets

The random-lift matrix-coefficient setting is established by [Bordenave and Collins](https://arxiv.org/abs/1801.00876v4). Theorem 3.9 of [Chen, Garza-Vargas, Tropp and van Handel](https://arxiv.org/html/2405.16026v3#S3.SS3) supplies a fixed-excess O(1/n) baseline. Theorem 9.4 of [the later strong-convergence paper](https://arxiv.org/html/2412.00593v3#S9.SS2) improves the general upper deviation scale to \(O_{\mathbb P}((\log n/n)^{1/6})\). The obstruction here concerns fixed excess and does not improve that shrinking-excess scale.

Sharp tangle powers already occur in [Friedman and Kohler's regular Ramanujan-base theory](https://arxiv.org/abs/1911.05775). A general assertion that tangles govern rare spectral failures would therefore be insufficient as a novelty claim.

Fixed-degree random regular graph edge universality is already addressed by [Huang, McKenzie and Yau](https://arxiv.org/abs/2412.20263v2). Their ensemble is not automatically a magnetic fixed-base lift. The paper's primary record was inspected here, not its full proof. Exact model comparisons precede any claim that a proposed target is open.

## What the scientific implications would require

A spectral transition theorem could predict when a local alteration creates a localized signal or a collective mode. A sharp rare-event theorem could quantify the reliability of a spectral construction. A solver consequence additionally needs a bound for the actual normalized or preconditioned operator, with its nullspace and old sector treated correctly.

The distinction is already visible in SG-17. Its adjacency top gap shrinks at order \(n^{-1/2}\), but the augmented graph is irregular. This alone says nothing about a vanishing normalized-Laplacian gap. For a d-regular host of conductance \(\phi\), adding one vertex with d distinct neighbours preserves conductance at least \(\phi/3\). Indeed, an old cut boundary remains, while its smaller augmented side-volume is at most \(3d\min(|T|,n-|T|)\). Cuts isolating only the added vertex have conductance one. Cheeger's inequality then preserves a normalized-Laplacian gap of at least \(\phi^2/18\). This elementary check prevents an incorrect mixing interpretation of the adjacency resonance.

## Formal verification and coordination

Use the existing adaptive coordination protocol with one integrator, frozen attempts and separately reconstructed reviews. The old batch sidecar, research_lab and the local loop engine remain distinct implementations. None was launched in this round. The [orchestration audit](../../../spectral-reconciliation-2026-11-14/ORCHESTRATOR_AUDIT.md) records their actual roles.

The formalization track should prove complete statements about the actual sampled permutations and graph operators. A useful first target is the exact colored-core probability calculation and the projection inequality used above. A second is the Perron-separated block reduction behind the interacting-defect target. SG-11 supplies a further finite probability theorem to formalize. An abstract recurrence or Schur identity with its graph interpretation assumed is only a component.

Each result should have separately recorded proof status, review status, formalization scope, and literature comparison. A large declaration count does not replace those distinctions.

This round stops after research selection, the bounded phase obstruction and its review. The next mathematical action is the marked-resolvent estimate in NEXT_PROBLEM.md. No unattended research campaign or new deadline is implied.
