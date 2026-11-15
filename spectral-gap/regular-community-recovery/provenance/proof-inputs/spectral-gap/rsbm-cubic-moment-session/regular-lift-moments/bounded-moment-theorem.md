# Bounded intertwiner moments for random regular lifts

Derived November 15, 2026. This note assembles three separately proved
inputs in this directory. It strengthens the polynomial moment in the
all-slot entropy packet to a bound independent of lift size. Historical
novelty is not asserted.

## The theorem

Let B be a fixed connected simple d-regular graph, d>=3, with k vertices.
Let A_N be the adjacency matrix of its random N-lift: the matching above
each base edge is independently uniform. Fix a prime p, an integer r>=0,
and a matrix R in Mat_r(Fp). Put

    Z_R(A_N)=#{Y in Fp^(kN by r): A_N Y=Y R}.

Then there is a finite constant C=C(B,p,r), independent of N and R, such
that

    sup_(N>=1) E Z_R(A_N) <= C.                             (T)

Equivalently, if h_R is the dimension of this linear solution space,

    sup_N E p^(h_R) < infinity.

Both bipartite and nonbipartite bases are included. Every positive lift
size is allowed. R may be singular or nonsemisimple, and p may divide d.
The constant can depend substantially on B,p,r; no uniformity in growing
parameters is claimed.

In particular (T) holds for B=K4 and R=A_K4, over every fixed prime field.
It also holds simultaneously over any fixed finite family of candidate
matrices by summing their bounds.

## Exact count and nonpositive entropy

At a vertex of old type i, a legal ordered star consists of a root
x in V=Fp^r and a neighbor label z_j for each j~i, satisfying

    sum_(j~i) z_j=xR.

There are q^d such stars, q=p^r. For empirical star counts T_i(s) and
directed pair counts m_ij(a,b), compatibility is m_ji=m_ij^T. Exact
matching enumeration gives the type contribution

    product_i [N!/product_s T_i(s)!]
      * product_(edges ij) [product_(a,b) m_ij(a,b)!/N!].    (1)

The multinomials already assign the root labels. There is no additional
root multinomial. Each factor is an actual random matching, so there is
no configuration conditioning or change of graph law.

For star laws P_i and pair laws nu_ij=m_ij/N define

    Phi(P)=sum_i H(P_i)-sum_(edges ij) H(nu_ij).

Uniform Stirling bounds, including zero counts, give

    log contribution=N Phi+O_(B,p,r)(log(N+1)).              (2)

There are polynomially many types for fixed data. The all-slot identity is

    Phi=-(d-2)/d sum_edges I(nu_ij)
         -(1/d) sum_i sum_(t~i) J_it <= 0,                 (3)

where J_it is the conditional total correlation of the retained d-1
neighbor labels given the root. Omitting any physical slot loses no
information because its coefficient in the local equation is one.

The exact entropy identity is the one in the audited
regular-no-internal packet; [zero-phases.md](zero-phases.md) proves the
phase classification needed below, rather than inferring a bounded
moment from (3).

## The zero phases

At Phi=0, root and neighbor are independent on every edge, and each
retained neighbor tuple is conditionally a product with root-independent
marginals. The finite-group lemma in [zero-phases.md](zero-phases.md)
then forces every root law to be uniform on a full affine coset.

If the base is connected and nonbipartite, all root cosets use one
common subspace H<=V. The phases are exactly

    HR subseteq H,
    a_i R-sum_(j~i) a_j in H,       for every i,             (4)

with root law Uniform(a_i+H). The legal star laws are uniquely uniform
on their affine supports. Thus there is one full uniform phase H=V,
and finitely many proper-subspace phases. At H=0 these are the
fiber-constant base intertwiners.

For a connected bipartite base there can instead be subspaces H_L,H_R
on its two sides, with H_L R subseteq H_R and H_R R subseteq H_L.
These mixed phases are real and cannot be omitted. The next two
sections explain why they cause no obstruction to a bounded moment.

## Full uniform prefactors: a genuine bounded contribution

[central-lift-uniform.md](central-lift-uniform.md) proves the needed
estimate for the full uniform edge-table neighborhood, with all
prefactors and finite lattice periods retained:

    limsup_N E[Z_R; all edge tables near uniform] <= q^(kq). (5)

Here the notation means the expected number of solutions satisfying
the indicated table restriction, not an event imposed on a random
single solution.

A useful exact comparison makes this local estimate especially
transparent. Let P choose each legal star uniformly. Let Q choose the
root and ALL d neighbor labels independently uniformly. For the
compatible matching weight

    W(m)=product_edges product_(a,b) m_ij(a,b)!/N!,

the exact identities are

    E Z_R=q^(dkN) E_P W,
    q^(dkN) E_Q W=1.                                      (6)

The two iid table laws have the SAME positive covariance: under P,
any two neighbor labels are independent uniform given the root because
d>=3. The only real table restrictions are identical root-row margins
at each vertex. The legal law has maximal lattice index q^(kq) relative
to the independent law. A relative tilted lattice local CLT therefore
bounds its central weighted sum by q^(kq) times the EXACT normalizer 1.

This argument also controls the fixed-neighborhood tails. Write a
compatible centered edge table as

    X_ij(a,b)=[r_i(a)+r_j(b)]/q+Z_ij(a,b),

where Z has zero row and column sums and each r_i has zero total.
After combining the covariance density with the exact factorial
weight, the quadratic exponent is

    -(q/2) sum_i ||r_i||^2
       -(q^2/2) sum_edges ||Z_ij||^2.                     (7)

It is strictly negative on every nonzero compatible direction. The
dimension identity in the companion note cancels every power of N.
Analytic rate-function expansion and Stirling bounds make the tail
outside sqrt(N)log N a polynomial times exp(-c log^2 N). This is the
prefactor and tail input that the entropy inequality by itself lacks.

## Boundary neighborhoods: quotient support and conditional rank

For a proper invariant H and quotient point map (4), let D_a(Y) be the
number of individual lift vertices whose labels lie outside a_i+H.
Let M_H(N) be the homogeneous intertwiner moment with alphabet H and
restricted target R|_H. The rigorous proposition in
[sparse-lift-common-subspace.md](sparse-lift-common-subspace.md) gives,
for a sufficiently small fixed epsilon>0,

    E #{Y: A_NY=YR, D_a(Y)<=epsilon N}
      <= M_H(N)[1+O(N^(-(d-2)))].                          (8)

The representatives a_i need not form exact intertwiners in V; only
the quotient equation is needed.

Here is the mechanism, including the correlation issue. Quotienting
by H and subtracting the fiber-constant quotient point map gives a
quotient solution with sparse support S. Any outside vertex touched
by S must have at least two support neighbors. The certificate of all
edges incident to S therefore satisfies

    E-V >= (d-2)|S|/2.

For every fixed quotient assignment, its lifts form an affine fiber,
empty or of cardinality exactly Z_H(A_N). A certificate with E forced
matching edges is produced from independent uniform matchings by at
most E image-transpositions. The output is exactly uniform conditional
on those edges. Each transposition changes at most four vertex rows,
so under this explicit coupling

    Z_H(A_N conditioned on certificate)
       <= p^(4 dim(H) E) Z_H(A_N)

pointwise. Consequently its conditional expectation is at most
p^(4 dim(H) E) M_H(N). This exponential-in-|S| factor is absorbed into
the dense-certificate enumeration; it cannot create a power of N.
The resulting bound is

    E #{lifts with k quotient defects}
      <= M_H(N) dk C0^k (k/N)^((d-2)k/2).

Support one is impossible in a lift of a simple base. Choosing epsilon
small and summing k>=2 proves (8). In particular no independence of the
rare support event and the bulk kernel size has been assumed.

## Induction for nonbipartite bases

Induct on r=dim V. At r=0, the moment equals 1. Assume every smaller
dimension is bounded, uniformly over its target matrices. There are
finitely many proper invariant subspaces and quotient coset maps (4).
For each one, (8) is bounded by the induction hypothesis. Their sum
is bounded because the phase family is finite.

The full uniform neighborhood is bounded by (5). The remaining feasible
type region is compact and contains no zero of (3): each proper phase
has an open root-coset neighborhood inside D_a<epsilon N, while the full
uniform phase is inside the chosen edge-table neighborhood. Hence (2)
bounds the complementary contribution by a polynomial times exp(-cN).

This proves a finite limsup for every R in dimension r. There are only
finitely many r-by-r matrices over Fp, so their limsups have a common
finite bound. Finally the finitely many lift sizes below any eventual
threshold have finite moments. This yields the supremum in (T).

## Bipartite closure by two vector spaces

For a bipartite base, enlarge the induction class as follows. Assign
V_L=Fp^(r_L), V_R=Fp^(r_R), and linear maps

    T_L:V_L -> V_R,       T_R:V_R -> V_L.

At a left lift vertex require the sum of right neighbor labels to equal
T_L of its label; at a right vertex use T_R. The original problem is the
case V_L=V_R=V and T_L=T_R=R.

The exact type formula and all-slot identity are unchanged. Every zero
phase consists of cosets a_i+H_side with

    T_L H_L subseteq H_R,       T_R H_R subseteq H_L,

and the corresponding quotient point-map equations. This is proved in
the two-space appendix of [zero-phases.md](zero-phases.md).

The full uniform estimate is proved, rather than assumed, in the
two-space appendix of [central-lift-uniform.md](central-lift-uniform.md).
For u=|V_L|, v=|V_R| its explicit bound is

    limsup uniform contribution <= v^(|L|u) u^(|R|v).       (9)

The exact independent-star normalizer is still 1. Both laws have the
same positive covariance; the weighted exponent is

    -1/2 sum_i |V_side(i)| ||r_i||^2
        -(uv/2) sum_edges ||Z_ij||^2.

All powers cancel, and the maximal lattice indices are v^u at a left
type and u^v at a right type. The assertion includes u=1 or v=1; if both
are 1, the system has only its zero solution.

The two-space appendix of
[sparse-lift-common-subspace.md](sparse-lift-common-subspace.md) proves
(8) for H_L,H_R, with its homogeneous restricted-system moment on the
right. The conditioned rank comparison remains valid for this
rectangular variable-space operator: a transposition changes two left
and two right rows, of total dimension at most 2(dim H_L+dim H_R).

Now induct on r_L+r_R. Every phase except the full uniform one makes at
least one inclusion H_side<V_side proper and strictly lowers that sum.
The zero-dimensional base case is 1. The full uniform estimate,
boundary proposition and compact entropy complement prove boundedness
exactly as before. This closes the enlarged class and hence proves (T)
for every bipartite regular base as well.

## Scalar K4 sharpening

For a scalar target lambda, a connected nonbipartite base and odd p,
there are only full uniform and point phases. The sharper lattice
calculation in [central-lift-uniform.md](central-lift-uniform.md) gives

    E |ker_Fp(A_N-lambda I)|
      =2 p^(dim ker_Fp(B-lambda I))+o_(B,p)(1).             (10)

Each point phase contributes 1+o(1) by the sparse estimate. For K4,
the exponent is 3 at lambda=-1, 1 at lambda=3, and 0 otherwise.
For this equality, choose the uniform edge neighborhood and the finitely
many point neighborhoods disjoint. This is possible for fixed p: a point
phase has a point-mass root margin, whereas every root margin in a
sufficiently small uniform edge neighborhood is close to uniform.

Thus, in particular,

    P(dim_R ker(A_N+I)=3) -> 1

for random K4 lifts: the old three-dimensional kernel is deterministic,
real excess nullity implies modular excess, and (10) gives limsup
excess probability at most 1/(p-1), followed by fixed odd p tending
to infinity. This sharpening is separate from the general bounded
matrix moment and does not assert exact moments for all matrix R.

## Scope and algorithmic consequence

The theorem is about a fixed finite base, prime field and target
dimension. It controls rare large kernels in the unconditioned lift
law and so can replace the polynomial moment input in an enumeration
algorithm over any fixed finite candidate family.

On its own it does not establish a particular implementation's
near-quadratic kernel-computation cost; that linear-algebra step must
be supplied separately. No claim is made for growing bases or fields,
degree-two bases, arbitrary deterministic lifts, noise, or nonregular
old degree frames.

## Independent audit record

All three independent cross-audits passed:

- [audit-sparse-on-central.md](audit-sparse-on-central.md) checks the
  exact normalizers, covariance, maximal lattices, relative local CLT,
  factorial weights, positive precision, dimension cancellation and
  unequal bipartite alphabets.
- [audit-central-on-boundary.md](audit-central-on-boundary.md) checks
  zero phases, affine fibers, uniform conditional forcing, rank
  comparison, support enumeration and the two-space induction.
- [audit-entropy-on-assembly.md](audit-entropy-on-assembly.md) checks
  the complete phase coverage, compact complementary region, induction
  quantifiers, zero-dimensional sides and assembly of the estimates.

The source now distinguishes the affine lattice hull from the finite
support itself; full support in the central window follows from the
relative local CLT. No bounded moment is inferred from entropy alone.
