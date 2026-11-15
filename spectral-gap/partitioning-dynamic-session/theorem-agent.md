# Independent theorem audit: a strong obstruction, plus a classical soft replacement

The complete proof is in `theorem-agent.tex`. No frozen manuscript was changed.

## Falsified big-if target

There is no dimension-independent modulus tending to zero with edit leverage that controls either unique Fiedler-projector motion or the fraction of labels changed by unique exact minimum bisection, even for connected simple **weighted bipartite graphs of maximum combinatorial degree four**, with **unit vertex masses**, when **one existing unit edge is doubled**.

Explicit family on n=4r vertices (r≥2): use the underlying graph C4 square P_r. Let δ=1/n and M=nr². At each path coordinate j, square edges 12 and 34 have weight 1+δ, and edges 13 and 24 have weight 1. Each of the four length-r paths has edge weights 2M. Double one square edge 13 at any fixed path coordinate.

The old unique Fiedler vector has group signs (+,+,−,−), and the new one has (+,−,+,−). Every coordinate is ±1/sqrt(n), so their signs give exact bisections. They are orthogonal; their rank-one projectors differ by operator norm one. Both sign cuts attain the corresponding spectral lower bound, and hence both are unique exact minimum bisections up to complement. They disagree on n/2 vertices. The old/new optimal cut weights are n/2 and n/2+1/2, while the old cut's updated cost is n/2+1.

The single edited edge has leverage τ<13/(4n)<4/n. Thus τ→0. For every fixed 0<α<1, the full positive fractional relative response has norm at most (1+τ)^α−1≤ατ→0. Thus even vanishing relative fractional response does not force label or hard-projector continuity.

The proof is exact. The old graph is a tensor sum, with coarse eigenvalues 0,2,2(1+δ),2(2+δ), and all internal modes ≥8n. The edited edge is orthogonal to the new vector. A scalar secular-function sign test shows that the other low eigenvalue crosses above 2(1+δ). Large internal conductances are essential to the stated construction; it is not an unweighted-host example.

## Classical soft replacement

For F_A(s)=s(A+sI)^−1 and F_B(s)=s(B+sI)^−1, B=A+d bb^T, their difference D_s is PSD rank one, bounded by I. Sherman–Morrison and logarithmic differentiation give the exact identity

    ∫ tr(D_s) ds/s = ∫ ||D_s|| ds/s = log(1+τ).

Consequently ∫||D_s||_F² ds/s≤log(1+τ), and the logarithmic measure of scales with ||D_s||>η is at most log(1+τ)/η. This is an elementary classical resolvent/determinant consequence, not a new spectral partition theorem.

## Cautions for the final synthesis

- All spectral and balance statements use the combinatorial Laplacian and Euclidean unit-mass normalization. Do not transfer them silently to degree-normalized Laplacians with a changing degree mass.
- For unweighted hosts, a single unit-edge addition/doubling cannot strictly replace one unique exact minimum bisection with a different unique optimum, by integrality; it can introduce ties. This observation does not prevent Fiedler-vector instability.
- L^α preserves the eigenvectors and their order. Fractional response compression alone does not improve the ordinary spectral partition approximation ratio.
- A positive label-stability theorem needs a partition-specific margin, controlled ambiguous labels, or a changed smooth output. Uniform energy certificates are useful but are corollaries of the existing response approximation theorem.
