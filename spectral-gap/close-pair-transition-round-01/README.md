# A sharp collective-to-pair transition

Completed November 15, 2026, America/Los_Angeles. Canonical claims: SG-22 through SG-24 in the [claim ledger](../CLAIM_LEDGER.md).

The n^(1/3) transition is genuine, and the logarithmic loss is removed. For a random cubic host with predetermined duplicated neighbourhoods, within m=o(n),

\[
\frac{\lambda_{\max}-3}{\sqrt{m/n}}
\xrightarrow{\mathbb P}\frac3{\sqrt8}
\quad\Longleftrightarrow\quad m^3/n\longrightarrow0.
\]

The result extends to every fixed degree through the critically weighted attachment, with the stated bounded weak interactions. Read the [complete theorem and explanation](root/transition-synthesis-v1.md) for exact quantifiers and constants.

| Number of marks | Established behavior |
| --- | --- |
| m=o(n^(1/3)) | The whole collective cluster and the previous eigenvector mass laws hold with no logarithmic restriction |
| m/n^(1/3) tends to a positive constant | The normalized cluster is tight, but close pairs force a nonvanishing probability of deviations beyond every fixed top threshold |
| n^(1/3)<<m<<sqrt(n) | The top displacement has scale m^2/n, both tight and bounded away from zero in probability |
| n^(1/3)<<m<<n | The top displacement divided by sqrt(m/n) diverges in probability, with a matching upper scale asserted only in the preceding row |

At criticality the normalized top expectation diverges even though the random variables are tight. The reciprocal tail lower bound proves this distinction. No critical distribution or exact expectation growth rate is claimed.

## Proof map

The [two-walk proof](root/nonbacktracking-upper-v1.md) removes the logarithm using only the earlier fixed host-gap input. It excludes short marked paths, then controls the remaining nonbacktracking interactions by a squared Frobenius bound and exact label sampling. A distinct [polynomial proof](probability/chebyshev-proof-v1.md) reaches the same range using a stronger published host-spectrum rate.

The [cubic pair proof](obstruction/proof-v1.md) uses positivity of the full resolvent above the host spectrum. A close pair gives a concrete negative Schur quadratic form, hence an actual eigenvalue beyond the tested threshold. The [weighted extension](obstruction/weighted-extension-v1.md) and [pair-scale lower estimate](obstruction/pair-scale-v1.md) give the structural versions. The [cluster-width proof](root/cluster-width-v1.md) supplies the matching upper scale by monotonicity of the retained Schur matrix.

## Review and formal evidence

- [First independent upper review](reviews/nonbacktracking-upper-v1-review.md) and [second upper and cluster review](reviews/cluster-width-v1-review.md).
- [Polynomial reconstruction](reviews/chebyshev-v1-integrator-review.md), [cubic lower reconstruction](reviews/obstruction-v1-integrator-review.md), and [weighted lower reconstruction](reviews/weighted-pair-v1-integrator-review.md).
- [Exact-revision synthesis review](reviews/transition-synthesis-v1-review.md), including sharp necessity and expectation divergence.
- [Formal scope and theorem inventory](formalization/README.md), [independent scope audit](reviews/formal-scope-v1.md), and [retained independent replay receipt](reviews/formal-replay-v1.json).

All paper reviews accept their frozen revisions with no unresolved findings. Reviewers declare prior exposure and authorship boundaries. This is internal review, not external refereeing.

The 20 new finite formal declarations check actual uniform-subset counting, the stationary far-row inequality, the symmetric pair test and an actual inverse Schur witness. They passed an independent fresh source replay. They are separate from the previous 27 declarations. Neither count represents new research results, and the full probability and spectral theorem is not formally verified.

## Priority and limits

The [primary-source comparison](priority/PRIORITY-v1.md) and [upper-method addendum](priority/UPPER_METHODS-v1.md) credit established splitting graphs, scattering, resonant interactions, polynomial locality and deformation methods. No directly subsuming theorem was identified in this bounded search. Historical firstness and an exact published open-problem match remain unverified.

Marks are chosen before the graph. Uniformity over bounded H does not authorize graph-dependent marks. Outside d=3 the critical attachment is weighted. The result concerns adjacency eigenvalues near the isolated host Perron mode. It does not establish spatial localization, a normalized-Laplacian gap, mixing improvement or a solver guarantee.

[Verification inventory](VERIFICATION.json), [handoff](HANDOFF.md), and [next research target](NEXT_PROBLEM.md) preserve the exact current state. Earlier frozen files are unchanged. No unattended process or external submission is active.
