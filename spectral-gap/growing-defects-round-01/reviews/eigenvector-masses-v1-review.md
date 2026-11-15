# Separate review of collective-mode masses

November 15, 2026, America/Los_Angeles.

Verdict: accept the frozen eigenvector extension at the exact revision below. Every section was read and the reconstruction, normalization, uniform residual, ordered simplicity and mass conclusions were checked independently. No unsupported inference or unresolved mathematical finding was identified.

This is an internal paper-proof review. It does not establish end-to-end formal verification, historical priority or external specialist acceptance.

## Exact revisions and exposure

| Input | SHA256 |
| --- | --- |
| [Eigenvector extension v1](../root/eigenvector-masses-v1.md) | a98fa21b356991a4e3d6a51f1568984f9d0592d3c81c893e0ec81f6fb11561d6 |
| [Graph theorem v1](../root/graph-theorem-v1.md) | b4a00f7b6490590a51e112c99be336e895723f29df4819c68d00dec526a4d2e3 |
| [Deterministic transfer v1](../root/transfer-v1.md) | deb05e53631ad4d273f48b2d6253014352c1263010d3990ebcc4e0b616351b99 |
| [Probability proof v1](../probability/proof-v1.md) | 56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b |
| [Full-chain review](combined-v1-review.md) | fbebdf56a7caae70311f29e0c833a9b9fc6188c6a8bbaf9c8078c4771ddb7f50 |

Prior exposure included the full-chain proofs already reviewed, the priority sources, and an advance description of the proposed mass fractions and the derivative normalization argument. The frozen extension was first read after its hash was supplied. This is a separately reconstructed review with shared target exposure, not access isolation. No proof file was edited and no numerical observation was used as a premise.

## Reconstruction and exact normalization

On the host-gap event, every near-d eigenvalue z is outside the spectrum of A restricted to the constant-vector complement. Projecting the host equation gives

\[
h_\perp=(zI-A_Q)^{-1}QB_ny.
\]

The constant-vector projection and the new-vertex equation give exactly K(z)(x,y)=0 with the stated signs. There is no missing homogeneous host-complement solution. In particular, x=y=0 would force the full eigenvector to vanish.

The derivative of the resolvent is minus its square. Therefore differentiating F(z)=zI-B_n^\top Q(zI-A_Q)^{-1}QB_n gives

\[
F'(z)=I+B_n^\top Q(zI-A_Q)^{-2}QB_n.
\]

Orthogonality of x u and h_perp proves the exact full normalization 1=x^2+y^\top F'(z)y. This identity includes the squared norm on the new vertices through the identity term in F'. It is not merely a host normalization.

The earlier derivative estimate at d and the uniform second-derivative bound imply the supremum estimate in equation (8). The interval has length proportional to s_n tending to zero. This step is an operator-norm estimate with no dimension factor and requires no new probability input.

## Effective residual and uniformity

For w=(x,sqrt(D)y), the relation (x,y)=S w is correct. Multiplying the exact kernel equation on the left by S produces the same symmetric effective pencil as the deterministic transfer. The error divided by s_n tends to zero uniformly over the relevant real interval.

The normalization identity gives ||w||^2=1+o_P(1) uniformly. It also has a deterministic bound because x^2+||y||^2<=1 and D is fixed. Consequently the operator error gives equation (10) for every unit eigenvector on the same event. No union bound over the growing collection of roots or vectors is needed.

The probability law has a finite sample space for each n. Suprema over the compact unit spheres of the actual eigenspaces are measurable. Assigning bounded values on exceptional events preserves the convergence statements.

## Extreme branches and simplicity

The effective matrix has the exact decomposition into v_plus, v_minus and the orthogonal zero sector. Its nonzero eigenvalues are plus and minus kappa. For fixed d, kappa is bounded away from zero independently of m. The ordered eigenvalue comparison therefore separates the scaled extreme root from every other effective eigenvalue. Applying that separation to the residual shows that w approaches the corresponding one-dimensional subspace.

Together with ||w||^2 tending to one, this yields x^2 tending to 1/2, D||y||^2 tending to 1/2, and the stated signed relation between sqrt(D)y and x e. An arbitrary global eigenvector sign does not affect this relation. Full normalization then gives the perpendicular-host mass (D-1)/(2D).

Simplicity is justified at the level of the actual ordered eigenvalues. When m>=2, each extreme is separated from its neighboring middle root by a positive multiple of s_n. When m=1, the two roots are separated from one another. The host gap and interlacing separate the lower extreme from the remaining spectrum. A repeated extreme eigenvalue would contradict one of these ordered gaps.

## Middle cluster and growing multiplicity

For every middle root, the scaled displacement tends to zero uniformly. The common residual and bounded norm therefore imply that the effective matrix times w tends uniformly to zero. Its squared norm is exactly

\[
\kappa^2\bigl(x^2+D|\langle e,y\rangle|^2\bigr).
\]

Both terms are nonnegative. Thus x and the constant marked-coordinate component vanish uniformly. The effective normalization then gives D||y||^2 tending to one, and full normalization gives the perpendicular-host mass (D-1)/D.

This applies to every unit vector in each repeated actual eigenspace because such a vector satisfies the same exact eigenvalue equation. It does not establish a result for arbitrary combinations of vectors with distinct eigenvalues. The statement makes this distinction explicitly, so no unsupported whole-span projection claim is present.

## Scope and disposition

At d=3, D=8, giving extreme masses 1/2, 1/16 and 7/16, and middle masses 0, 1/8 and 7/8. These constants and the stated direction relations are correct. The fixed-d weighted model, deterministic marks and growth condition are inherited without alteration from the graph theorem.

The result concerns mass in three specified subspaces. It does not prove graph-distance decay, support near individual marks, bulk localization, a middle eigenvalue fluctuation scale or a nonzero-H eigenvector law. The conclusion that half the extreme-mode mass remains in the extended host constant direction is consistent with the stated limitations.

All inspected obligations are closed at the frozen revision. There is no first unsupported inference to report. Priority remains separate and is discussed in the [eigenvector comparison addendum](../priority/EIGENVECTOR_PRIORITY-v1.md).
