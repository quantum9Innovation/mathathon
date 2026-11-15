# Uniform-phase prefactors for intertwiners of random regular lifts

Derived 2026-11-15. This is a self-contained local calculation. It proves a bounded contribution from a fixed neighborhood of the full uniform phase, for every finite vector alphabet and every linear target matrix. It does not use an entropy-only inference at a zero of the entropy exponent.

## The result

Let B be a fixed simple d-regular base on k vertices, d>=3, and let A_n be the adjacency matrix of its random n-lift: every base edge independently carries a uniform perfect matching between two fibers of size n. Put V=F_p^r, q=|V|, and fix any r-by-r matrix R over F_p. Rows x are acted on as xR. No invertibility or semisimplicity hypothesis on R is imposed.

For an intertwiner Y with A_n Y=YR, record on each directed base edge i->j the q-by-q table m_ij(a,b) of pairs (root label a, neighbor label b). Let Z_unif be the contribution to E|{Y:A_n Y=YR}| for which all such tables satisfy

    ||m_ij-(n/q^2)J|| <= delta n.                         (1)

Here delta>0 is sufficiently small and fixed; it may depend on the fixed data. Then

    limsup_(n->infinity) Z_unif <= q^(kq).                (2)

The limsup is over every positive integer n; there is no parity condition or residue-class restriction. In particular the required uniform-phase contribution is bounded independently of n. The bound (2) itself is independent of R and d once k,q are fixed, although the neighborhood and asymptotic threshold need not be.

For a connected nonbipartite base, an odd prime p, and a scalar R=lambda, the exact limit is sharper:

    Z_unif = p^t+o_p,B(1),  t=dim_Fp ker(B-lambda I).      (3)

For K4 this is p^3 at lambda=-1, p at lambda=3, and 1 at all other lambda, for every odd prime. Formula (2) also applies to vector R=A_K4, with q=p^4, without any further calculation.

## 1. Exact two probability models

At old vertex i a legal ordered star consists of a root a and one label b_j for each of its d neighbors, subject to

    sum_(j~i) b_j = aR.                                  (4)

There are q^d legal stars. Let P be the law in which the legal star is chosen uniformly, independently at each vertex of each fiber. Thus the root and any d-1 neighbor labels are independent uniform; the last label is determined by (4).

Let Q instead choose the root and all d neighbor labels independently uniform. Use n iid copies of the vector containing one independent star of each old type. The resulting directed tables are denoted M=(M_ij).

For a compatible array, meaning m_ji=m_ij^T, put

    W(m)= product_({i,j} in E(B)) [ product_(a,b) m_ij(a,b)! / n! ].

For incompatible arrays set W=0. Counting the bijections in each cross matching gives the exact identities

    E Z_R(A_n) = q^(dkn) E_P W(M),                        (5)
    q^(dkn) E_Q W(M) = 1.                                (6)

To see (6), sum over all independent-neighbor ordered-star assignments. Every lift and every assignment of its kn root labels determines its ordered neighbors uniquely. Thus the total weighted number of assignments is q^(kn); dividing by q^((d+1)kn) gives q^(-dkn). This is exact for every n.

Equation (6) is useful for retaining all Gaussian and lattice normalization constants: it normalizes the same weighted Gaussian that appears in (5).

## 2. Real span and identical covariance

Let H_i be the real vector space of collections of d q-by-q tables with total zero in each table and identical row sums in all d tables. These are exactly the real deterministic linear restrictions for one old type. Put H=direct-sum_i H_i. Its dimension is

    h=k[(q-1)+d q(q-1)].                                 (7)

Let P_row be the orthogonal projection, in each H_i, onto the subspace whose tables are identical and constant within each row. Its dimension is q-1. The other d q(q-1) coordinates are row-centered table coordinates.

Under both P and Q, the local table mean is q^(-2)J on each slot, and the covariance on H_i is

    Sigma_i=q^(-2)[I+(d-1)P_row].                        (8)

Consequently Sigma_i has eigenvalue d/q^2 with multiplicity q-1, and 1/q^2 with multiplicity d q(q-1). In particular it is positive definite on all of H_i, so no further real linear restrictions occur.

For verification, conditional on the root A, any two distinct neighbor labels are independent uniform under P, because d>=3 leaves at least one other coordinate to absorb the sum constraint. They are also independent under Q. For test tables f_j with row means g_j(a), the variance of sum_j f_j(A,B_j) is the sum of the conditional variances plus the variance of sum_j g_j(A). On H_i the row means g_j coincide. This gives exactly (8). Different old types are sampled independently, so the joint covariance is Sigma=direct-sum_i Sigma_i, the same in the two models.

This argument applies to every finite vector alphabet, arbitrary R, and every characteristic. Only the real covariance is inverted; neither d nor R is divided by in F_p.

## 3. Exact maximal lattices

Let L0 be the full integer lattice in H. The differences of the Q-support generate L0. Indeed one may change one neighbor label within one fixed root row and slot, generating every within-row transfer. Changing the root from a to a' while all neighbor labels are zero changes the common row count from a to a', generating the remaining common-row directions.

The P-lattice L is a finite-index sublattice of L0. It has this exact description: for each old type i and every root label a in V,

    C_i,a(m):=sum_(j~i) sum_b b m_ij(a,b) -(aR)n_i(a)=0
                       in V,                            (9)

where n_i(a)=sum_b m_ij(a,b), independent of j. These are q vector congruences per old type. They are independent on L0: within a fixed root row, changing a single neighbor label by any element of V changes C_i,a by that element, with no effect on another root row or old type.

For completeness, (9) supplies all lattice periods. A circle-valued character constant on the legal local support has row functions theta_j(a,b). At fixed a, the sum of theta_j(a,b_j) is constant on sum_j b_j=aR. Since d>=3, varying two coordinates freely while a third compensates gives the additive Cauchy equation. Therefore all d row functions have the form

    theta_j(a,b)=alpha_j(a)+chi_a(b),

with a common additive character chi_a of V. Variation of a forces

    sum_j alpha_j(a)+chi_a(aR)=constant.

Modulo characters already constant on L0's common-row support, this is exactly the character sum_a chi_a(C_i,a). Conversely every such character is constant on the legal support. There are q choices for each chi_a, hence q^q characters per old type. Duality of finite-index integer lattices proves

    [L0:L]=q^(kq)=:I.                                    (10)

No extra periods are being ignored. In particular the characteristic torus for L has only one modulus-one point modulo its reciprocal lattice.

The affine lattice hulls of the n-fold supports have the form n v0+L or n v0+L0, where v0 is the array from the all-zero local stars. The actual supports are finite subsets of these lattices; the relative local CLT below establishes full support in the growing central window for sufficiently large n. The zero star is legal for every linear R. Thus both affine lattices have a compatible point for every n. This excludes a hidden n modulo p condition.

## 4. Relative local CLT and central comparison

For a finite-support lattice law whose support differences generate its maximal lattice, exponential tilting and Fourier inversion give the relative local estimate, uniformly for

    ||m-n mu|| <= sqrt(n) log n,

    P(M=m)=(1+o(1)) covol(L)(2 pi n)^(-h/2)(det Sigma)^(-1/2)
          exp[-<m-n mu,Sigma^(-1)(m-n mu)>/(2n)].         (11)

The same formula holds for Q with L0 instead of L. Both use exactly the same Euclidean measure on H and the same Sigma from (8). Hence, on the P affine lattice in that window,

    P_P(M=m) = I(1+o(1)) P_Q(M=m),                       (12)

uniformly; outside that affine lattice the left side is zero.

The estimate is relative, not an absolute-error LLT. One proof is to tilt the finite law so that its mean is m/n. The tilt is O(log n/sqrt(n)), and covariance changes by o(1). At the tilted mean, Fourier inversion has one Gaussian maximum on the maximal-lattice torus; outside its neighborhood the modulus is uniformly less than one. Inside, log characteristic function equals its quadratic covariance term plus a uniform O(||xi||^3). Cutting at ||xi||=n^(-2/5), rescaling by sqrt(n), and using Gaussian domination yields the exact covolume and determinant in (11), with uniform relative error. Undoing the tilt has rate-function Taylor error O(log^3 n/sqrt(n))=o(1). Thus (11)--(12) include all finite lattice periods and remain valid at every n.

Multiply (12) by the nonnegative weight q^(dkn)W(m), and sum only compatible m in the window. The exact normalization (6) immediately gives

    central-window contribution under P <= I+o(1).       (13)

This comparison retains the full prefactor. A polynomial Stirling error or an entropy bound alone would not establish (13).

## 5. Factorial prefactors and the weighted Gaussian tail

It remains to justify enlarging the logarithmic window to the fixed neighborhood (1). Let m_ij=(n/q^2)J+sqrt(n)X_ij. Uniformly in the logarithmic window, Stirling gives for each undirected edge

    product_ab m_ij(a,b)!/n!
      = q^(-2n)(2 pi n)^((q^2-1)/2) q^(-q^2)
        exp[(q^2/2)||X_ij||^2](1+o(1)).                 (14)

All entries are positive there; the error is O_q(log^3 n/sqrt(n)). Write e=kd/2 for the number of base edges. The factorial power of n is e(q^2-1)/2.

On the compatible real subspace S of H, write uniquely

    X_ij(a,b)=[r_i(a)+r_j(b)]/q + Z_ij(a,b),

where each r_i has zero total and each Z_ij has all row and column sums zero, with Z_ji=Z_ij^T. Its dimension is

    s=k(q-1)+e(q-1)^2.                                  (15)

The total Euclidean norm counts both directed orientations. Thus

    ||X||^2=(2d/q)sum_i||r_i||^2+2sum_edges||Z_ij||^2,
    ||P_row X||^2=(d/q)sum_i||r_i||^2.

Combining the Gaussian exponent from (8),(11) with the factorial exponent from (14) gives exactly

    -1/2<X,Sigma^(-1)X> +(q^2/4)||X||^2
      =-(q/2)sum_i||r_i||^2 -(q^2/2)sum_edges||Z_ij||^2. (16)

This is strictly negative on every nonzero compatible tangent. Equivalently its precision eigenvalues on S are q^2/(2d) on the root-margin modes and q^2/2 on the interaction modes. The dimensions and all powers match:

    e(q^2-1)-h+s=0.                                     (17)

Thus there is neither a residual power of n nor an unexamined flat Gaussian direction.

The finite-support Cramer rate function for P is analytic near mu and has quadratic term one half of the Sigma inverse form. The logarithm of the pairing weight has the quadratic term in (14). Equation (16) says that their difference is positive definite on S. Choosing delta sufficiently small makes all cubic remainders less than half this positive quadratic form. Chernoff's bound and Stirling then give, throughout (1),

    q^(dkn) P_P(M=m) W(m)
       <= C n^(e(q^2-1)/2) exp[-c||m-n mu||^2/n].        (18)

The constants depend only on the fixed data. The number of possible tables is polynomial in n. Outside the sqrt(n)log n window, the bound (18) is summable and tends to zero, since exp[-c log^2 n] defeats every fixed polynomial. Equations (13),(18) prove (2).

This local-tail proof is independent of the global entropy classification. It is valid whenever m is in the fixed full-uniform table neighborhood, even if one does not separately restrict the complete star empirical law.

## 6. Exact scalar coefficient for nonbipartite bases

Suppose now V=F_p, p odd, R=lambda, and the base is connected and nonbipartite. Let K0=L0 intersect S be the compatible integer direction lattice. It is the full integer lattice of edge tables with prescribed common root margins: choose arbitrary integer root margins r_i of total zero and, independently on each edge, arbitrary (p-1)-by-(p-1) interior entries; the last row and column are uniquely filled. In particular its reduction modulo p is precisely the compatible F_p table space, with no saturation issue.

Restrict the kp scalar congruences (9) to K0. Let their rank be rho. A linear dependence with coefficients h_i(a) annihilates every 2-by-2 interaction transfer on every edge, so

    [h_i(a)-h_i(a')](b-b')
     +[h_j(b)-h_j(b')](a-a')=0                          (19)

for every edge ij and all labels. This forces

    h_i(a)=t_i a+k_i,     t_i+t_j=0 for ij in E(B).

An odd cycle and odd characteristic force every t_i=0. The remaining root-margin coefficients are

    ((B-lambda I)k)_i a.

Since root margins at different old vertices are freely variable subject only to their own zero total, these annihilate all root-margin variations exactly when (B-lambda I)k=0. Therefore

    rho=kp-t,       t=dim ker(B-lambda I).                (20)

The compatible legal sublattice has index p^rho in K0. A Gaussian Riemann sum on any fixed finite-index affine sublattice has exactly that index's reciprocal fraction of the full sum. The Gaussian is the positive one in (16); lattice translates do not change the limit. Combining this fraction with the unrestricted density ratio p^(kp) in (12) gives p^t times the Q central contribution.

The latter tends to one, not merely at most one. Under the normalized weighted law in (6), choose a random lift and iid uniform root labels. Along any one base edge, its n matched label pairs are independent uniform pairs. Chebyshev's inequality, followed by a union bound over finitely many base edges, puts every table in the sqrt(n)log n window with probability 1-o(1). Hence the Q central contribution is 1-o(1), proving (3).

For K4, B=J-I. In odd characteristic, the one-dimensional constant eigenspace has eigenvalue 3 and its three-dimensional zero-sum complement has eigenvalue -1; these eigenvalues remain distinct because p does not divide 4. This gives the three explicit values stated above.

## Scope for the full moment

This note supplies the bounded full-uniform contribution for arbitrary R and vector alphabet. A global bounded first moment additionally requires classification and control of every other zero-entropy phase. If a separate induction treats the proper-subspace/coset phases and entropy compactness removes the remaining region, (2) is the missing prefactor input to that induction. No conclusion about the complete moment is inferred solely from the nonpositive entropy exponent here.

## Appendix: bipartite bases with two different vector alphabets

The prefactor argument extends to the unequal-space phases needed in a bipartite induction. Here is the precise statement and the changes in all normalizations.

Let the fixed base be d-regular and bipartite, d>=3, with parts L,R of sizes k_L,k_R. Regularity gives k_L=k_R, and e=d k_L=d k_R. Give the two sides vector spaces V_L,V_R over the same finite field, with sizes u,v. Either space may be the zero-dimensional space of size one. At a vertex of side L, constrain the sum of its V_R-valued neighbors to equal T_i(a), where T_i:V_L->V_R is any fixed linear map; use the reverse kind of map at side R. The maps may depend on the old vertex. The same argument allows fixed affine maps T_i(a)+c_i as well.

The expected number of such labelings, restricted to a sufficiently small full-uniform edge-table neighborhood, has

    limsup_(n->infinity) Z_unif
       <= v^(k_L u) u^(k_R v).                           (19)

This includes all n, irrespective of their residues. If u=v=1 the only labeling is deterministic and (19) is immediate. Otherwise all covariance statements below are on their positive-dimensional real spans; zero-dimensional factors simply contribute one.

At an old vertex i, put q_i=|V_i| and q'_i=|V_opposite|. The legal-star count is q_i(q'_i)^(d-1). The product of these counts over all lifted vertices is

    [(u v^(d-1))^(k_L) (v u^(d-1))^(k_R)]^n
       =(uv)^(e n).                                    (20)

The independent-neighbor Q model has q_i(q'_i)^d stars locally. The ratio of its total number of stars to the number of unrestricted root assignments is also (uv)^(e n). Thus the exact versions of (5),(6) are

    E Z(A_n)=(uv)^(e n) E_P W(M),
    (uv)^(e n) E_Q W(M)=1.                              (21)

The weight W is still the product of compatible edge factorial ratios; every edge table is u-by-v or its transpose.

The local real table space has dimension

    (q_i-1)+d q_i(q'_i-1).

Covariance on this space is

    Sigma_i=(uv)^(-1)[I+(d-1)P_row],                     (22)

because conditional on the root any two legal neighbor labels are independent uniform, just as under Q. It has positive eigenvalues d/(uv) on the q_i-1 common-row modes and 1/(uv) on the d q_i(q'_i-1) row-centered modes. The independent-neighbor differences generate the full common-row integer lattice, exactly as before. The legal differences are characterized by one V_opposite-valued sum congruence per root label. The same additive-character argument gives local lattice index (q'_i)^(q_i). Therefore the full maximal-lattice index is exactly

    I_bip=v^(k_L u) u^(k_R v).                           (23)

These conclusions do not require either map to be injective or surjective. For affine maps, the affine lattice translates change, but the index and covariance do not. It is unnecessary for every affine lattice translate to have a compatible point: if it has none, its contribution is zero. Every legal-support point is still an independent-neighbor support point, which is all that the upper comparison needs.

The tilted relative LLT comparison is again P_P(M=m)=I_bip(1+o(1))P_Q(M=m) on the legal affine lattice in the logarithmic window. The exact normalization (21) bounds that window by I_bip+o(1).

For completeness, the Stirling and positive-precision checks also persist. One edge contributes

    product_ab m_ab!/n!
      =(uv)^(-n)(2 pi n)^((uv-1)/2)(uv)^(-uv/2)
        exp[(uv/2)||X_ij||^2](1+o(1)),                  (24)

where m_ij=nJ/(uv)+sqrt(n)X_ij. On compatible deviations write

    X_ij(a,b)=r_i(a)/q_j+r_j(b)/q_i+Z_ij(a,b),

where each r_i has zero total and each Z has zero row and column sums. Combining (22) with (24) gives exactly

    -1/2<X,Sigma^(-1)X> +(uv/4)||X||^2
      =-1/2 sum_i q_i||r_i||^2
       -(uv/2)sum_edges||Z_ij||^2.                     (25)

This is positive precision on every nonzero compatible direction, even when u=1 or v=1 (the corresponding absent modes have dimension zero). The ambient and compatible dimensions are

    h_bip=sum_i[(q_i-1)+d q_i(q'_i-1)],
    s_bip=sum_i(q_i-1)+e(u-1)(v-1),

and satisfy

    h_bip-s_bip=e(uv-1).                                (26)

Thus the matching prefactors cancel the dimension difference exactly. The same analytic rate-function argument as in (18), now using (25), removes the part of a fixed full-uniform neighborhood outside the logarithmic window. This proves (19) with the full prefactor and finite lattice effects accounted for.

### Exact scalar coefficient on connected bipartite bases

For reference the scalar exact calculation also has a short bipartite form. Keep p odd and put t0=dim ker(B-lambda I). The interaction annihilator calculation (19) now permits alternating slopes

    h_i(a)=sigma_i t a+k_i,

where sigma is +1 on one base side and -1 on the other. The residual coefficient on root margins is

    ((B-lambda I)k)_i a -lambda sigma_i t a^2.

The functions 1,a,a^2 on F_p are linearly independent for every odd p. Therefore k must lie in ker(B-lambda I), and lambda t=0. The dependence dimension is t0 when lambda!=0 and t0+1 when lambda=0. The same finite-index Gaussian summation as in Section 6 proves

    Z_unif=p^(t0+1_{lambda=0})+o(1)                     (27)

on a connected bipartite base. This is only the full-uniform phase coefficient; at lambda=0 there are additional mixed zero phases, treated by the two-space induction. At lambda!=0 there are only the uniform and point phases.
