# Independent reconstruction of the close-pair obstruction

November 15, 2026. Reviewer: root. Reviewed source: [proof-v1.md](../obstruction/proof-v1.md), SHA256 cadd1408ff45526a328b78f7b2f063fa599278603e90282c216e364c68280a35.

Verdict: accepted within its stated scope. No mathematical correction is required.

Exposure: the reviewer supplied the initial nearest-pair heuristic and read short progress messages, but did not author the obstruction proof. The exact frozen argument was reconstructed after freezing. This is separate authorship and review, not blind or access-isolated review.

1. The full resolvent at z>3 has a positive walk expansion, including disconnected hosts. The path-lifting map is injective for walks with a fixed starting lift. Selecting one lift of the other mark gives the claimed lower kernel bound without a tree-neighbourhood hypothesis.
2. The Schur identity is correctly signed. At distance at least two, the selected two-coordinate compression of E^T A E vanishes. The symmetric normalized pair produces f(z)-z^2 g(z)t(z)^ell, with no missing factor two. At z=3+2^(-r)/2, its rescaling tends to 4-6=-2. The explicit reconstructed test vector proves an actual eigenvalue bound.
3. The distance-ball count L_r=3(2^r-2) excludes neighbours and the root. Exploration only through level r is sufficient. The pairing collision estimate is conservative and uniform. Conditioning on simplicity costs a bounded factor. Markov's inequality supplies a host event on which the proportion of maximal balls tends to one.
4. Uniform mark sampling is justified by joint relabelling invariance and never conditions the fixed-mark graph law on an adaptively selected event. Disjoint auxiliary-edge inclusion events have nonpositive covariance. The overlapping-pair count and the ratio p_3/(n p_2^2) were recomputed. They give the displayed variance bound and second-moment probability.
5. The floor in the radius produces the factor 8 in the critical lower bound. The simplicity and exploration errors tend to zero because 4^r/n<=1/(4K^2m). Taking theta to infinity gives probability tending to one for every fixed K, throughout m=o(n).

The only sourced probability input is positive asymptotic simplicity probability, already checked in the previous full-chain source review and recorded in [sources-v1.md](../obstruction/sources-v1.md). The host spectral-gap theorem is not a premise of this lower bound.

The proof establishes neither a limiting critical distribution nor spatial localization of the associated eigenvector. It does not prove a normalized-Laplacian or mixing statement. Those limitations are accurate and must remain attached to the result.
