# Separate review of the transition synthesis

November 15, 2026, America/Los_Angeles.

Verdict: accept [transition-synthesis-v1.md](../root/transition-synthesis-v1.md) at SHA256 4e53c4f754e5e80f78dc6ae0a4260eefb67152f37dd66b343ef3556e108417e5. The complete synthesis was read and every displayed implication checked against its stated proof inputs. No mathematical overreach or unsupported inference was identified.

## Exposure and dependency scope

The reviewer constructed the lower-obstruction proofs and separately reviewed the nonbacktracking and cluster-width upper proofs at their frozen hashes. That upper review is [cluster-width-v1-review.md](cluster-width-v1-review.md), SHA256 48c917bd1e9f9442877e7973815253fe22bf6cf4a079698fc680d6ddbd16ce52. The integrator separately reviewed the lower proofs. This synthesis review checks their logical assembly and the new expectation consequence. It does not provide an independent second review of its reviewer's own lower-proof construction.

The alternate Chebyshev proof was not read in this review. The accepted nonbacktracking route already supplies every probability input needed for the synthesis. Earlier transfer and mass dependencies were previously reviewed at their frozen revisions. No proof file was edited.

## The if-and-only-if criterion

Sufficiency follows from the newly proved o_P(s) marked-resolvent error, fixed-order derivative convergence, the vanishing marked-edge probability and the earlier deterministic transfer. The allowed range includes bounded m. The H=0 effective matrix has exactly two nonzero eigenvalues, plus and minus kappa_d, which gives the claimed top coefficient.

For necessity, failure of m^3/n tending to zero yields a subsequence with theta>=theta_0>0. Along it, m must tend to infinity, so the lower theorem's hypothesis is satisfied. The overall dilute condition m=o(n) persists. For any K>kappa_d the positive lower tail contradicts convergence to kappa_d along that subsequence. This proves the equivalence without assuming that theta has a limit or stays bounded.

The uniform-H cluster approximation also fails outside this sufficient range because its parameter ball contains H=0. No new assertion about eigenvector asymptotics outside the subcritical range is hidden in the equivalence.

## Critical tightness and the larger scale

When m/n^(1/3) tends to c>0, a/s tends to c^(3/2). The cluster-width scale max(s,a) is therefore comparable to s. This proves tightness of the maximum scaled deviation of the entire top cluster. The lower tail in equation (3) is positive for every fixed K, which excludes convergence of the top coordinate to any finite constant. It is consistent with tightness because the lower bound decreases to zero as K increases.

The reciprocal upper-tail statement follows from the upper proof's C/K estimate at threshold C K max(s,a), after rescaling by the fixed critical ratio. Constants need not agree with the lower bound. No limiting distribution or exact tail coefficient follows.

For n^(1/3)<<m<<sqrt(n), max(s,a)=a eventually. The upper bound is uniform tightness at scale a. The lower theorem gives equation (5) for the infimum over bounded H. Its complement bounds the probability of falling below K by K/(K+beta_d), which tends to zero as the fixed K decreases. This establishes precisely the defined meaning of Theta_P, with no deterministic limiting coefficient. The extension of divergence at scale s to m=o(n) uses only the broader lower theorem and does not improperly extend the matching upper scale beyond sqrt(n).

## Expectation divergence

The new consequence is valid. The host is a principal submatrix, so lambda_max(A_H)>=d for every H, including negative and graph-dependent bounded H. All normalized top displacements under discussion are nonnegative.

For a nonnegative X_n and finite L,

\[
\mathbb E X_n\ge\int_0^L\mathbb P(X_n>K)\,dK.
\]

Fatou's lemma applies to these nonnegative measurable tail functions. The pointwise limiting lower bound b/(K+b) therefore yields

\[
\liminf_n\mathbb E X_n\ge b\log(1+L/b).
\]

There is no exchange of an unbounded integral with a limit and no need for an estimate uniform in K at finite n. Letting the fixed L tend to infinity makes the lower bound arbitrarily large, which is exactly convergence of the expectations to positive infinity. At criticality b=beta_d c^(3/2). At the postcritical pair scale b=beta_d. The latter also works for any bounded-H choice, because its uniform lower-tail event was already proved.

Tightness does not imply uniform integrability, so the expectation conclusion does not conflict with the typical-scale estimates. The synthesis correctly avoids asserting a logarithmic or any other precise divergence rate.

## Scope and disposition

The constants, weighted convention for d other than three, deterministic mark requirement and simultaneous bounded-H qualification are preserved. The explanation of the one-third exponent is supported by the actual upper and lower proofs. The proposed critical distribution and spatial localization questions are explicitly left unproved.

This is acceptance of the paper theorem assembly and its expectation corollary. It is not full formal verification, historical-firstness certification, a normalized-Laplacian gap result or an algorithmic guarantee. No required repair or first unsupported inference was found at this exact revision.
