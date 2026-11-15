# Review of the actual retuned graph law

Date: November 15, 2026. Reviewer: structural workstream. Revision 1.

Target: `../root/retuned-graph-law-v1.md`, SHA256 `5c2b7bd527a47ca2c870ada456a5bd57e985ffafe5e949cf3dfb595dda537e6e`.

Verdict: accepted as a paper theorem at this exact revision, conditional only on its frozen and separately reviewed premises. No open mathematical finding was identified. Historical priority and end-to-end formalization are outside this verdict.

## Exposure and review scope

The reviewer had separately reviewed all five probability files named by the target and several earlier critical graph proofs. Those acceptances were not treated as an automatic proof of the graph application. The target was first read after it was frozen. The review reconstructs the exact graph pencil, nonlinear root count, scale conversion, physical-vector reconstruction, rank-p projection transfer and random-multiplicity mixture.

No live earlier version of this root synthesis was read. The reviewer independently derived a separate structural attachment theorem during the same round. That theorem is not used as a substitute for the fine-scale graph reduction here.

## 1. Exact pencil and physical scale

For z=3+sx in the bounded window under consideration, the host complement remains uniformly separated below z. Eliminating it from zI-mathcal A gives the retained block with entries z-3, -3 times the constant marked row divided by sqrt(n), and F(z). Congruence by diag(1,8^(-1/2)I), followed by division by s, is exactly xI-mathcal T_n(x). No inversion of z-3 is used, and the host constant mode has not been discarded.

The second reduction uses the complementary inverse on range(Q_-), whose fixed gap is supplied by the reviewed probability chain. It preserves kernels and inertia changes. Its dimension is p+1 for fixed p, including p=0.

The fine retained coordinate is x=x_n^0+s t. Therefore the actual graph eigenvalue is z=3+s x_n^0+s squared t. The stated physical center is exactly 3+s x_n^0, and the physical fine scale is s squared=m/n. This is distinct from the older logarithmic physical correction s squared r. The application does not divide an O_P(s) approximate cluster operator error by s and assume it vanishes. It uses the exact energy-dependent pencil and the new o_P(s) reduced error.

## 2. Nonlinear root count

For each fixed M, the reduced expansion holds uniformly for |x-x_n^0|<=Ms. The retained pencil derivative is O_P(s log squared n). Differentiating the complementary inverse introduces a bounded factor, while its coupling columns are O_P(sqrt(s)). Thus the reduced derivative is o_P(1) uniformly on that interval.

Choose M with margin beyond the deterministic pair coefficient and outside a high-probability bound for the tight collective coefficient. At the left endpoint xI-B_n(x) is negative definite, and at the right endpoint it is positive definite, with conditional probability tending to the prescribed high bound. Its derivative is at least I/2 on the good event. Every ordered eigenvalue function is consequently continuous and strictly increasing, crossing zero exactly once. There are p+1 roots counted with multiplicity.

Uniform Weyl comparison brackets each ordered root by the corresponding diagonal entry in the expansion plus or minus the uniform error. Repeated pair roots need not be followed as differentiable branches. At a multiple crossing the kernel dimension equals the number of zero ordered eigenvalues. The exact congruences transfer that multiplicity to the real symmetric graph matrix.

The coarse critical subspace theorem supplies exactly p+1 actual eigenvalues in the fixed window I_n. Its chosen epsilon=kappa/10 is below the separation to every other limiting level. Thus, after M is made large, the local roots exhaust the coarse group with arbitrarily high conditional probability. Sending n first and then M gives the ordered convergence without losing a root in an unbounded retained interval.

## 3. Noncoincidence and retained coordinates

For each fixed p, the limiting collective scalar has no atoms. Hence the probability that its finite-n coefficient lies within a shrinking fixed tolerance of the pair coefficient can be made arbitrarily small by first taking n large and then taking the tolerance to zero.

On a separation event with gap at least 2delta s in the reduced matrix, the o_P(s) perturbation forces the collective kernel coordinate to approach the first coordinate axis. At each pair root, the same equation forces its first coordinate to vanish and the remaining coordinates to approach the pair coordinate space. This statement follows directly by applying the coordinate projectors to the residual equation and dividing by the separated diagonal difference. It does not require treating the energy-dependent matrices at distinct roots as one fixed matrix.

The exact complementary reconstruction has norm O_P(sqrt(s)) on bounded normalized kernel coordinates. Therefore the entire retained collective and pair directions approach their reference spaces U_-. All p pair coordinates are retained. No residual negative target mode remains in Q_-.

The one-dimensional collective group has one root and is simple on the separation event. The pair group has total multiplicity p and may have unresolved internal splitting. The theorem correctly states convergence of its grouped projector rather than a particular basis.

## 4. Physical graph vectors and projectors

The first Schur reconstruction maps retained coordinates (alpha,v) to

\[
 (\alpha u+R_Q(3+sx)AEv/\sqrt8,\ v/\sqrt8).
\]

The factor sqrt(8) agrees with the preceding congruence. Its host-complement part solves the original graph equation exactly, and the retained kernel equation supplies the constant-host and added-coordinate equations.

The host resolvent identity gives ||J_x-J_0||=O(s) uniformly over the bounded coarse window. The derivative premise gives J_0^TJ_0=I+o_P(1). Hence the physical reconstruction is uniformly close to an isometry on the relevant retained vectors.

For the grouped pair statement, take an orthonormal basis of the actual p-dimensional spectral group. Its reconstructed retained vectors have Gram matrix I+o_P(1), since J_x-J_0 is uniformly small and p is fixed. Their kernel coordinates have vanishing collective component, so their span approaches the full p-dimensional pair reference space. Equal dimensions and the near-isometry imply operator-norm convergence of the projection matrices. This makes explicit why using different x values for different pair roots does not obstruct the projector conclusion.

The collective line is treated by the same reconstruction with rank one. Passing to arbitrary fixed p and then removing the small separation tolerance proves the target assertions.

The constant-host mass is alpha squared exactly for J_0. The added-coordinate mass is ||v|| squared/8 exactly. Its perpendicular-host Gram form tends to 7||v|| squared/8. Applied to c_- these give (1/2,1/16,7/16). Applied uniformly to the antisymmetric pair span they give (0,1/8,7/8). The operator-norm projector transfer preserves these uniform mass statements.

## 5. Random multiplicity and the limiting law

All conditional statements are proved for each fixed p and uniformly over a finite range of p. The distance-r count converges to its Poisson law and is tight. Summing over a finite p range and then removing that truncation proves the joint finite-point-measure law. This is a valid random-dimension mixture argument, including the p=0 case with only the collective atom.

The limiting scalar and P_0 use the same Poisson family. In particular conditioning on p shifts the collective law by kappa p/(2theta). The mean, variance, smooth-density and integer-tuning assertions are exactly the separately reviewed probability statements. No finite-n moment convergence is inferred from them.

The random ordering comes from distinct diagonal limits with a vanishing leading mixed block. It is not an avoided-crossing law with nonzero limiting mixing. The theorem appropriately excludes graph-adaptive tuning and shrinking conditioning on a coincidence event. It also does not resolve the finer splitting inside a repeated pair group or transfer the cubic constants to the broader attachment class.

No revision is requested for mathematical validity at the reviewed target hash.
