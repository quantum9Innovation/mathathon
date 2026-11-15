# Bipartite compatible-lattice forms and exact uniform coefficients

Prepared 2026-11-15. Direct algebra and finite lattice counting; no external theorem or source is imported. The relative local CLT, matching Stirling factors and positive weighted precision are the proved elementary inputs in the frozen `../../central-lift-uniform.md` and `../cyclic-lattice.md`. All lattice indices needed for the present coefficients are proved below. Frozen files are unchanged.

## 1. Statement

Let B be the adjacency matrix of a fixed connected simple bipartite d-regular base, d>=3, on k=2m vertices with parts L,Rbase. Let A_n be its independent uniform n-lift. Fix an odd prime p and a row alphabet V=F_p^{1-by-r}, with root map a->aR for an r-by-r matrix R. Put

    h(R)=dim_Fp {Y in F_p^(k-by-r): BY=YR},
    b(R)=dim_Fp {M: RM and RM^T are skew-symmetric}.       (1)

Then the contribution to E#{Y:A_nY=YR} from a sufficiently small fixed full-uniform directed-edge-table neighborhood is exactly

    p^[h(R)+b(R)]+o(1).                                  (2)

The limit is over every n, with no parity or residue restriction.

If R is a companion of a monic irreducible polynomial g over F_p, then

    g=t:                    b(R)=1,
    g!=t and g not even:    b(R)=0,
    g even, deg(g)=2s:      b(R)=s.                       (3)

Here even means g(-t)=g(t). Consequently the full-uniform coefficients are p^(h+1), p^h and p^(h+s) respectively. Formula (2) concerns the full-uniform phase only; additional mixed phases must be counted separately in the even and zero cases.

## 2. Congruence dependencies and all signs

Use row labels a,b in V and column dual coefficients h_i(a). Before compatibility, the legal-star maximal lattice is the kernel of

    C_i(a)=sum_(j~i) sum_b b m_ij(a,b) -(aR)n_i(a) in V,  (4)

inside the integer common-root-margin lattice L0. Its exact index is

    [L0:L]=p^(k r q),       q=p^r.                       (5)

Indeed there is one independent V-valued congruence for every root label and old vertex. There are no further finite periods: at fixed root a, a character constant on the legal sum support has the same additive character chi_a(b) in every neighbor slot, by the d>=3 Cauchy argument; its root intercept is forced to subtract chi_a(aR). Thus these and only these characters occur. This argument is unchanged by bipartiteness.

Let K0 be the compatible integer direction lattice m_ji=m_ij^T, with common root margins and table totals zero. It reduces onto the whole compatible F_p direction space: choose arbitrary integer root margins of total zero and arbitrary (q-1)-by-(q-1) interior entries on each edge, and fill the last row/column. This gives an integer bijective parameterization, so reduction introduces no saturation issue.

A left dependency of (4) is a family of dual columns h_i(a) such that sum_(i,a) C_i(a)h_i(a) vanishes on K0. Interaction 2-by-2 transfers on edge ij force

    (b-b')[h_i(a)-h_i(a')]
      +(a-a')[h_j(b)-h_j(b')]=0.                         (6)

Setting a'=b'=0 and fixing b successively at coordinate rows proves directly that every h_i is affine-linear:

    h_i(a)=K_i a^T+k_i,       K_j=-K_i^T on each edge.    (7)

No linearity assumption on the original functions h_i is made. Connectivity and bipartiteness imply that there is one arbitrary matrix M with

    K_i=M on L,       K_i=-M^T on Rbase.                 (8)

Unlike an odd-cycle base, there is no condition M=-M^T at this stage.

The remaining root-margin coefficient at vertex i is

    a(sum_(j~i)k_j-Rk_i) -aR K_i a^T.                   (9)

Root margins are independently variable subject only to their total zero. The coefficient must therefore be zero for all a, since its value at a=0 is zero. Evaluating a and -a separates the linear and quadratic terms in odd characteristic. The precise conditions are

    sum_(j~i) k_j=Rk_i,                                 (10)
    RM skew on L,       R(-M^T) skew on Rbase.           (11)

The latter is exactly the pair of conditions in (1); changing the sign of a matrix does not affect skew-symmetry. Conversely (8),(10),(11) make the entire functional vanish, so the classification is sufficient as well as necessary.

Putting the rows k_i^T into X turns (10) into BX=XR^T. As in the nonbipartite proof, its dimension equals h(R): the two Sylvester maps BY-YR and BX-XR^T are Frobenius adjoints because B=B^T. The matrix M and the constants k are independent choices. Therefore the congruence rank on K0 is exactly

    rho=k r q-h(R)-b(R).                                (12)

## 3. Invertible R: reduction to alternating forms for R squared

Assume R invertible. Put

    Lform=RM.                                          (13)

The first condition in (11) says Lform^T=-Lform. Moreover

    M=R^(-1)Lform,
    M^T=-Lform R^(-T),
    RM^T=-R Lform R^(-T).

Requiring RM^T to be skew is equivalent to requiring R Lform R^(-T) to be skew. Taking its transpose gives

    (R Lform R^(-T))^T=-R^(-1)Lform R^T.

Thus its skew condition is

    R^(-1)Lform R^T=R Lform R^(-T).

Multiplying on the left by R and on the right by R^T proves the exact equivalence

    R^2 Lform=Lform (R^T)^2.                            (14)

There is no inverse of d or n here. The map M->Lform is a bijection, hence

    b(R)=dim{Lform:Lform^T=-Lform,
                       R^2 Lform=Lform (R^T)^2}.        (15)

The bilinear form beta(a,b)=a Lform b^T is alternating, and (14) says precisely that the right action R^2 is self-adjoint:

    beta(aR^2,b)=beta(a,bR^2).

The form is permitted to be degenerate.

## 4. The finite-field dichotomy for irreducible g

Let g!=t be monic irreducible of degree r. Its constant term is nonzero, so R is invertible. Identify the row module V with

    E=F_p[lambda]=F_p[t]/(g),

so the right action R is multiplication by lambda. Put K=F_p[lambda^2]. Since lambda solves x^2-lambda^2 over K,

    [E:K] is either 1 or 2.                             (16)

If the index is 2, the minimal polynomial of lambda over K is x^2-lambda^2. Its nontrivial K-automorphism sends lambda to -lambda, since p is odd and lambda!=0. It follows that -lambda has the same F_p minimal polynomial as lambda. Consequently g(-t)=(-1)^r g(t). Evaluating the nonzero constant term gives (-1)^r=1, so r is even and g is even.

Conversely, if g is even, substitution lambda->-lambda defines a nontrivial F_p automorphism of E that fixes lambda^2, hence fixes K. Thus K is proper and (16) forces [E:K]=2. Writing r=2s then gives

    |K|=p^s,       dim_K E=2.                           (17)

If g is not even, the index in (16) is one. Thus K=E and multiplication by lambda^2 is cyclic and irreducible over F_p: any nonzero vector e generates E under F_p[lambda^2]. In particular no alternating form can make it self-adjoint, by the cyclic alternating-form lemma.

This proves the exact dichotomy, without a choice of splitting prime or a prescribed finite-field factorization pattern.

## 5. Balanced alternating forms: trace proof and dimension

The following argument proves the even case and also directly covers the non-even one. Let K/F_p be a finite field of size p^s, let W be a finite-dimensional K-vector space, and let beta:W x W->F_p be an alternating F_p-bilinear form. Say it is K-balanced if

    beta(cx,y)=beta(x,cy) for every c in K.               (18)

Such forms are in bijection with alternating K-bilinear forms Omega:W x W->K, through

    beta(x,y)=Tr_(K/Fp)(Omega(x,y)).                     (19)

Here are all details. Define the trace by

    Tr(z)=z+z^p+...+z^(p^(s-1)).

It is F_p-linear and takes values in F_p, because z^(p^s)=z in K. It is nonzero: its defining polynomial has nonzero leading coefficient and degree p^(s-1)<p^s, so cannot vanish on all of K. Therefore the pairing (c,z)->Tr(cz) is nondegenerate: for z!=0 multiplication by z is a bijection of K, and some element has nonzero trace.

For fixed x,y, the function c->beta(cx,y) is F_p-linear on K. Nondegeneracy gives a unique Omega(x,y) in K satisfying

    Tr(c Omega(x,y))=beta(cx,y) for all c in K.           (20)

Uniqueness proves additivity in x,y. For a in K,

    Tr(c Omega(ax,y))=beta(cax,y)=Tr(ca Omega(x,y)),

so Omega(ax,y)=a Omega(x,y). Balance gives similarly

    Tr(c Omega(x,ay))=beta(cx,ay)=beta(acx,y),

so Omega(x,ay)=a Omega(x,y). Finally

    beta(cy,x)=-beta(x,cy)=-beta(cx,y)

shows Omega(y,x)=-Omega(x,y). Odd characteristic implies Omega(x,x)=0, hence Omega is alternating. Setting c=1 gives (19).

Conversely an alternating K-bilinear Omega gives an alternating F_p-bilinear beta by (19), and K-balance is immediate. Applying (20) recovers Omega, so this correspondence is injective and surjective, including degenerate forms.

If dim_K W=n0, the K-space of alternating K-bilinear forms has dimension n0(n0-1)/2: choose its values on the unordered pairs of a K-basis. Thus the F_p dimension of the balanced alternating forms is

    s n0(n0-1)/2.                                      (21)

In (15), self-adjointness of R^2 is equivalent to balance by every c in K=F_p[lambda^2], since it extends from the generator to all polynomials. If g is even, W=E has K-dimension two and (21) gives b(R)=s. If g is not even, K=E and W has K-dimension one, giving b(R)=0. This also supplies a trace proof of the cyclic vanishing assertion in this case.

For g=t, r=1 and R=0. Both conditions RM and RM^T skew are vacuous, and a scalar M is arbitrary. Hence b(R)=1. All three cases of (3) are proved.

## 6. Exact lattice fraction, normalization and every n-residue

We finish the prefactor proof of (2), so the extra form dimension is not merely an entropy heuristic.

The legal-star and independent-neighbor models P,Q have the same full covariance on the common-row direction space. Their maximal lattices have exact ratio p^(krq) by (5). The finite-support tilted local CLT therefore gives

    P_P(M=m)=p^(krq)(1+o(1))P_Q(M=m)                    (22)

uniformly for ||m-n mu||<=sqrt(n)log n, on legal affine-lattice points. It is zero on the other points. The error is relative; its tilted rate-function remainder is O(log^3 n/sqrt(n)).

The exact Q weighted normalization is

    q^(dkn) E_Q W(M)=1,

where W is the product of compatible matching factorial ratios. Its normalized weighted law is exactly a random lift together with iid uniform root labels. Along any fixed base edge the n label pairs are iid uniform pairs. Hence the Q mass of the logarithmic central window tends to one.

On compatible tables, matching Stirling factors and the common Gaussian density have positive precision

    Q(X)=(q/2)sum_i||u_i||^2
                         +(q^2/2)sum_edges||Z_ij||^2,

with X_ij=[u_i(a)+u_j(b)]/q+Z_ij and zero row/column sums for Z. The factorial power and dimension difference cancel exactly, as in the frozen proof. Consequently restricting the Q Gaussian sum to a fixed index-p^rho compatible affine sublattice takes exactly fraction p^(-rho) in the limit.

That sublattice index is exact by (12): the compatible integer lattice has the integer free-margin/free-interior parameterization, the congruence rank is rho, and its kernel therefore has index p^rho. There are no additional parity or saturation factors. If v0 is the all-zero legal star array, the compatible affine lattice hulls are n v0+K0 and n v0+ker(C|K0). They are nonempty for every n. After scaling by 1/sqrt(n), the translate can always be reduced to a bounded fundamental cell of the fixed lattice. Gaussian Riemann sums converge uniformly in that offset, with density equal to the reciprocal covolume. Thus their ratio is p^(-rho) for every n sequence, including p|n.

Multiplying this fraction by the density ratio (22) yields

    p^(krq-rho)=p^[h(R)+b(R)].

The strictly positive precision permits a sufficiently small fixed uniform neighborhood to replace the logarithmic window: analytic rate-function and Stirling remainders are cubic, so outside the logarithmic window their negative quadratic exponent beats every polynomial type factor. This proves (2) with every prefactor accounted for.

## 7. Auxiliary mixed-phase central coefficients

These two local calculations are useful when assembling the additional phases. They do not by themselves count leakage or claim a full moment.

### A line over K in the even case

Let U=K as an s-dimensional F_p space, and use two copies on the two base sides. Let the root map on L be the identity and on Rbase be multiplication by c=lambda^2, whose minimal polynomial over F_p has degree s. Denote its matrix by C. Interaction dependency matrices are again M on L and -M^T on Rbase. The left root constraint makes M skew. The right constraint makes CM^T skew, equivalently CM=MC^T. Since the right action C is cyclic, the alternating form lemma gives M=0.

The linear dependencies are the kernel of the adjoint of the old two-map operator (sum of neighbors minus the side's on-site map). Its dimension equals the old homogeneous two-map solution dimension h_U. The maximal-lattice/compatible-index argument above therefore gives restricted full-uniform coefficient exactly

    p^h_U.                                             (23)

The proof uses no semisimplicity and allows s=1. The square old operator has the same domain and codomain dimension because both sides have the same alphabet dimension; its adjoint is precisely the constant-dependency operator.

### One scalar side and one zero-dimensional side

Write B=[[0,T],[T^T,0]] with T m-by-m. Put F_p labels on L and the singleton zero space on Rbase; all on-site maps are zero. The local legal lattice has one scalar congruence at each old Rbase vertex and none at the L vertices, so its index is p^m. Compatible tables are completely specified by the left root margins n_i(a). The congruence vector is

    T^T w,       w_i=sum_a a n_i(a).

Direction margins allow every w in F_p^m, using the transfer from label 0 to label 1. Therefore the compatible congruence rank is rank(T), with no saturation factor. If s0=dim ker T=dim ker T^T, the uniform coefficient is exactly

    p^(m-rank T)=p^s0.                                  (24)

The opposite mixed side has the same coefficient. The unequal-alphabet Gaussian and exact independent-neighbor normalizer in the frozen bipartite appendix apply even with a singleton side, so (24) retains its full prefactor and is valid for every n. No inverse of n or d is used.

## Independent checks

`bipartite-forms-check.js` directly computes the dimension of matrices M satisfying the two skew conditions, and separately constructs the congruence map on the explicit compatible integer parameter basis. The eight form-space checks include irreducible even degrees two and four (dimensions one and two), a non-even irreducible quadratic (dimension zero), scalar zero, cyclic Jordan, and reducible/noncyclic controls. Four direct K3,3 lattice-rank checks verify

    rho=krq-h(R)-b(R)

in scalar zero/nonzero and even/non-even irreducible quadratic cases. All checks pass; the proof above is dimension-independent.
