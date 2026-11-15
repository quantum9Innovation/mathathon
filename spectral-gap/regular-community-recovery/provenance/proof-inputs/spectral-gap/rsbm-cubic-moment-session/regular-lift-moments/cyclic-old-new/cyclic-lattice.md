# Cyclic target matrices: exact compatible-lattice uniform coefficient

Prepared 2026-11-15. This is a direct finite-field/lattice proof. No external theorem or source is imported. The finite-support tilted local CLT and matching Stirling estimates are the elementary ones proved in the frozen `../central-lift-uniform.md`; their necessary formulas are recalled below. No file in the frozen packet is modified.

## The statement and conventions

Let B be the adjacency matrix of a fixed connected simple nonbipartite d-regular base, with k vertices and d>=3. Let A_n be its random n-lift, with independent uniform edge matchings. Fix an odd prime p, V=F_p^{1-by-r}, q=p^r, and an arbitrary r-by-r matrix R. A label a is a **row** vector, and the local equation is

    sum_(j~i) b_j = aR.                                  (1)

Let

    h_old(R)=dim_Fp {Y in F_p^(k-by-r): BY=YR},
    a(R)=dim_Fp {K: K^T=-K, RK=KR^T}.                    (2)

The full-uniform phase contribution to E#{Y:A_nY=YR}, with every directed edge table in a sufficiently small fixed neighborhood of nJ/q^2, is

    p^[h_old(R)+a(R)] +o(1).                             (3)

In particular, if the right action a->aR is cyclic, then a(R)=0 and the coefficient is exactly

    p^h_old(R).                                         (4)

Here cyclic means that some row v has v,vR,...,vR^(r-1) as a basis. Every companion matrix has this property (for the usual column companion, its last coordinate row supplies a triangular reversed basis). The result includes cyclic reducible and nonsemisimple targets; only an irreducible target has just the point and full-uniform phases globally. Formula (3) is a statement about the uniform contribution and does not omit possible proper-subspace phases for other R.

All limits are for fixed p,R,B. They hold along **every** positive integer n, with no assumption concerning p|n or parity.

## 1. Full maximal lattice before edge compatibility

For old vertex i, let m_ij(a,b) be the directed table in neighbor slot j. Its row margins are the common root counts n_i(a), independent of j, and each table has total n. In the direction space the table totals and sum_a n_i(a) are zero. Let L0 be the full integer direction lattice with these common-row constraints, over all old vertices.

Uniform independent-neighbor stars (Q: root and all d neighbors iid uniform) generate exactly L0. Within a fixed root row one may change one slot's neighbor label, generating all within-row transfers. Changing the root while putting all neighbors at zero generates every common-row-margin direction.

Uniform legal stars (P: root plus any d-1 neighbors iid uniform, last neighbor from (1)) generate the sublattice L specified by the vector congruences

    C_i(a;m)=sum_(j~i) sum_b b m_ij(a,b) -(aR)n_i(a)=0
                         in V,                           (5)

one congruence per old type i and label a in V. Precisely,

    L={m in L0: all C_i(a;m)=0},
    [L0:L]=p^(kqr).                                      (6)

Here is a proof that these are the **maximal** periods, rather than merely necessary congruences. A circle-valued character constant on a legal local support has functions theta_j(a,b). At fixed a, the sum of these functions is constant when sum_j b_j=aR. Since d>=3, varying two labels freely with a third compensating forces the additive Cauchy equation. Therefore

    theta_j(a,b)=alpha_j(a)+chi_a(b),

where chi_a is one common additive character of V for all d slots. Variation of the root requires sum_j alpha_j(a)+chi_a(aR) to be constant. Modulo characters already constant on the common-row lattice L0, the resulting character is exactly sum_a chi_a(C_i(a;m)). Conversely every such character is a period. There are q choices of chi_a for each of q root labels, hence q^q=p^(rq) periods per old type. The congruences are independent on L0: changing one neighbor value in a fixed root row changes its C_i(a) by an arbitrary element of V, without changing any other C. Thus their kernel has precisely this index and is the generated legal-star lattice. Independence over old types gives (6).

The real covariance on L0's real span is positive definite and is identical under P and Q: conditional on the root, any two neighbor labels are independent uniform for d>=3. Thus the generated lattices have the same full real span; no additional real constraint is hidden in (6).

## 2. The compatible integer lattice is saturated in the required sense

Let S be the real direction space of compatible tables m_ji=m_ij^T, with a common root margin at each old vertex and total zero in each table. Put

    K0=L0 intersect S.

There is an explicit integer parameterization of K0. Choose arbitrary integer root-margin vectors u_i(a) of total zero, independently for each i. For each undirected edge ij, orient it and choose arbitrary entries m_ij(a,b) for a!=0,b!=0. Fill the last column and row to have row margins u_i and column margins u_j. Explicitly,

    m(a,0)=u_i(a)-sum_(b!=0)m(a,b),       a!=0,
    m(0,b)=u_j(b)-sum_(a!=0)m(a,b),       b!=0,
    m(0,0)=u_i(0)+u_j(0)+sum_(a,b!=0)m(a,b).

This gives every compatible integer direction uniquely. Hence

    rank_Z K0=k(q-1)+|E(B)|(q-1)^2,                      (7)

and reduction modulo p gives exactly the compatible F_p direction space. In particular there is no extra saturation index, division by d or n, or unproved lifting of a field-compatible table.

Restrict (5) to K0, and let rho be the F_p rank of the resulting congruence map. Then

    K=K0 intersect L=ker(C:K0->V^(kq)),
    [K0:K]=p^rho.                                       (8)

The rest of the algebra computes rho exactly.

## 3. All compatible congruence dependencies

A left dependency of the congruences is a family of **column** vectors h_i(a) in F_p^(r-by-1), with the pairing b h_i(a). It is a dependency exactly when the scalar functional

    ell_h(m)=sum_(i,a) C_i(a;m) h_i(a)                    (9)

vanishes on K0. By Section 2 this can equivalently be tested on the entire compatible direction space over F_p.

### Interaction transfers force affine-linear functions

For any edge ij and labels a,a',b,b', a 2-by-2 table transfer has zero root margins. Applying (9) gives

    (b-b')[h_i(a)-h_i(a')]
     +(a-a')[h_j(b)-h_j(b')]=0.                          (10)

Put k_i=h_i(0), U_i(a)=h_i(a)-k_i, and set a'=b'=0. Then

    b U_i(a)+a U_j(b)=0                                 (11)

for all row vectors a,b. Fix b at each coordinate row e_l. Equation (11) writes each coordinate of U_i(a) as a linear function of the coordinates of a. Thus U_i is F_p-linear, without any initial regularity assumption on h_i. There are matrices K_i with

    h_i(a)=K_i a^T+k_i.

Substitution in (11) gives

    a(K_i^T+K_j)b^T=0 for all a,b,
    hence K_j=-K_i^T.                                   (12)

Connectivity propagates K_i by the involution T(K)=-K^T. An odd cycle forces K_i=T(K_i), so K_i is skew-symmetric. Once this happens T(K_i)=K_i; consequently every old vertex has one common matrix K with

    K^T=-K.                                             (13)

This proves the claimed affine-linear form and its global consistency. It also proves the converse interaction assertion: with (13), all edge interaction coefficients cancel.

### Root-margin tests separate the quadratic and linear parts

Using the compatible edge tables to collect margins at their endpoints, substitution of h_i(a)=K a^T+k_i into (9) leaves

    ell_h(m)=sum_(i,a) [ a(sum_(j~i)k_j-Rk_i)
                              -aRK a^T ] n_i(a).        (14)

For clarity, the two endpoint edge terms are

    bK a^T+aK b^T=0,
    b k_i+a k_j,

and the on-site term is -aR(K a^T+k_i), which verifies the signs and transposes in (14).

Root margins at each old vertex vary freely subject only to their own total zero. The coefficient in square brackets must therefore be constant in a. Its value at a=0 is zero, so it vanishes for every a. Evaluate it at a and -a. Since p is odd, addition and subtraction separate the linear and quadratic parts and give

    sum_(j~i) k_j=Rk_i for every i,                      (15)
    aRK a^T=0 for every a.                               (16)

For any matrix M, the condition aMa^T=0 for every a is equivalent in odd characteristic to M+M^T=0: use coordinate rows and their pairwise sums. Since K^T=-K, (16) is therefore equivalent to

    RK=KR^T.                                            (17)

Conversely (13),(15),(17) make (14) vanish. Thus they give a necessary **and sufficient** classification of every dependency.

### The linear dependency dimension is exactly h_old(R)

Put the rows k_i^T into a k-by-r matrix X. Equation (15) becomes

    BX=XR^T.                                            (18)

Let S_R(Y)=BY-YR on the kr-dimensional matrix space. Under the nondegenerate Frobenius pairing tr(X^T Y), its adjoint is

    S_R^*(X)=B^T X-XR^T=BX-XR^T,

because the base adjacency is symmetric. A linear map and its transpose have the same rank and, here, the same domain dimension. Hence dim ker S_R^*=dim ker S_R=h_old(R).

The choices of K in (13),(17) and of k in (15) are independent and uniquely recoverable from h. We have proved

    dim_Fp Dependency(C|K0)=h_old(R)+a(R),
    rho=kqr-h_old(R)-a(R).                               (19)

No base semisimplicity, irreducibility of R, or restriction on n entered this calculation.

## 4. A cyclic operator admits no such alternating form

For K satisfying (13),(17), define the alternating bilinear form on row vectors

    beta(a,b)=aK b^T.

Equation (17) says precisely that the **right action R** is self-adjoint for beta:

    beta(aR,b)=aRK b^T=aKR^T b^T=beta(a,bR).               (20)

This remains meaningful for degenerate K. If v is a cyclic row, every a,b can be written a=vf(R), b=vg(R). Moving polynomial actions across the pairing by (20) gives

    beta(vf(R),vg(R))=beta(v,v g(R)f(R)).

The right side is symmetric in f,g. Therefore beta is symmetric on the whole row space. But it is alternating, hence skew-symmetric; since 2 is invertible, beta=0 and K=0. We conclude

    R cyclic and p odd  ==> a(R)=0.                      (21)

This proves the cyclic assertion without requiring K nondegenerate, R invertible, R diagonalizable, or the base semisimple.

## 5. Exact Gaussian fraction and all affine lattice translates

Here we verify that the algebraic dependency dimension is the exact uniform prefactor rather than only a count of necessary constraints.

Write the full directed-table mean as mu=J/q^2, and let P and Q denote the two iid star laws in Section 1. The exact matching weight is

    W(m)=1_compatible product_edges [product_ab m_ij(a,b)!/n!].

As in the frozen central calculation,

    E Z_R(A_n)=q^(dkn) E_P W(M),
    q^(dkn) E_Q W(M)=1.                                 (22)

In the logarithmic window ||m-n mu||<=sqrt(n)log n, the tilted finite-support local CLT is a **relative** estimate. Identical covariance under P,Q and their exact maximal lattices (6) imply, uniformly on P's affine lattice,

    P_P(M=m)=p^(kqr)(1+o(1)) P_Q(M=m).                   (23)

At other points the P probability is zero. The estimate follows by tilting to mean m/n, applying Fourier inversion on the maximal-lattice torus, and undoing the tilt; the rate Taylor error is O(log^3 n/sqrt(n)). Thus every period in (6) is retained.

There is no missing compatible affine residue. Use the all-zero legal star as v0. The two affine lattice hulls of the n-fold supports are n v0+L and n v0+L0. Their compatible intersections are exactly

    n v0+K,       n v0+K0.                               (24)

They are nonempty for **every n**, because n v0 itself is compatible. Each K has full rank in S and fixed finite index, so every translated central mesh is within a bounded distance of the mean before scaling. A tilted LLT moreover makes all points of these affine hulls in the central window actual support points for sufficiently large n; it does not assume finite support equals its affine hull globally.

To see the precise fraction after compatibility, use the explicit weighted Gaussian from the frozen prefactor calculation. For compatible X=(m-n mu)/sqrt(n), write

    X_ij(a,b)=[u_i(a)+u_j(b)]/q+Z_ij(a,b),

with each u_i of total zero and each Z_ij of zero row and column sums. Stirling plus the common covariance give the strictly positive Gaussian exponent

    -Q(X)=-(q/2)sum_i||u_i||^2
                       -(q^2/2)sum_edges||Z_ij||^2.     (25)

The factorial power n^[|E|(q^2-1)/2] cancels the difference between the ambient local-table dimension and the compatible-table dimension. Consequently Q's normalized matching mass on its central affine lattice is an m-independent prefactor times exp[-Q(X)](1+o(1)), with uniform relative error in the logarithmic window.

A Gaussian Riemann sum on n v0+K has fraction [K0:K]^(-1)=p^(-rho) of the sum on n v0+K0. This is valid uniformly in the translate n v0-n mu: reduce its offset modulo a fundamental cell of the fixed lattice, then scale by 1/sqrt(n). On a fixed compact region, translated lattice Riemann sums converge uniformly; the positive Gaussian (25) gives uniform integrable tails. There is no n modulo p factor. Thus the fraction is exactly p^(-rho), not an unspecified bounded constant.

Finally the Q central sum tends to one. Under its exactly normalized weighted law in (22), first choose a random lift and then iid uniform root labels. Along one fixed base edge its n matched label pairs are iid uniform pairs, so each table lies in its sqrt(n)log n window with probability 1-o(1), by Chebyshev and a union bound over the fixed number of edges. It follows that the compatible legal part of this Q central sum tends to p^(-rho).

Multiplying by (23), the P uniform-window contribution is

    p^(kqr-rho)+o(1)=p^[h_old(R)+a(R)]+o(1).              (26)

The frozen central estimate extends this window to a sufficiently small fixed full-uniform neighborhood. For completeness its reason is local, not a global entropy assumption: the iid rate function is analytic near mu with inverse-covariance Hessian; subtracting the factorial Hessian gives exactly the positive form (25). Shrinking the neighborhood controls cubic errors, and outside sqrt(n)log n the resulting exp[-c||m-n mu||^2/n] beats every fixed polynomial type factor. Hence the omitted contribution is o(1).

This proves (3), and (21) proves (4), with maximal-lattice saturation, compatibility, Gaussian normalization and every affine n-residue accounted for.

## Independent finite-field checks

`central-cyclic-check.js` constructs the congruence map directly on the integer parameter basis in Section 2 and computes its rank over finite fields; it does not assume the dependency classification. It separately computes h_old(R) and a(R). The checked K4 cases include scalar shifts, an irreducible quadratic at p=3 and p=5, a cyclic matrix with distinct eigenvalues, a cyclic Jordan block, and a noncyclic scalar double. All eight checks satisfy

    rank(C|K0)=kqr-h_old(R)-a(R).

The noncyclic double has one extra alternating dependency, verifying that omitting the a(R) term without the cyclic hypothesis would be incorrect. These checks support the algebra; the proof above applies in every fixed dimension.
