# Complete old/new spectral disjointness for regular simple base lifts

Derived November 15, 2026. This is the bipartite completion of the frozen
nonbipartite result. Every new proof, check and audit is confined to this
directory. The parent packets remain unchanged. Historical novelty is
not asserted.

## The theorem

Let B be the adjacency matrix of a fixed connected SIMPLE d-regular graph,
d>=3, and let A_N be its independent uniform random N-lift. Let U_N be
the real subspace of vectors constant on each fiber and W_N=U_N^perp.
Then

    P[spec(A_N|W_N) intersects spec(B)] -> 0.               (1)

All positive lift sizes are allowed. In particular every old eigenvalue,
including irrational ones and repeated ones, retains exactly its base
multiplicity with high probability.

The nonbipartite case is proved in
[../old-new-disjointness.md](../old-new-disjointness.md).
This document proves the remaining bipartite case. It does not extend
(1) to arbitrary degree frames with unequal old class proportions or
unequal numbers of old types in their two parts. Square bipartite blocks
are essential to the zero-target argument below.

## Exact moments for a bipartite base

Write the bipartite base and lift as

    B=[0 T; T^T 0],       A_N=[0 X; X^T 0].

Regularity implies equal base part sizes m, so T is m-by-m and X is
mN-by-mN. Fix an odd prime p and a monic irreducible g in Fp[t] of degree r.
Let R_g be its companion and set

    Z_g(A)=#{Y: AY=Y R_g}=|ker g(A)|,
    h=dim_Fp ker g(B).

The identity between companion intertwiners and the polynomial kernel
holds for every modular matrix, including matrices with Jordan blocks.
The exponent h is the GEOMETRIC kernel dimension; replacing it by r times
the characteristic-polynomial exponent requires a good base prime.

The exact bipartite formulas are

    g=t:                   E Z_g(A_N)=(p+3)p^h+o(1);
    g!=t, g not even:       E Z_g(A_N)=2p^h+o(1);
    g even, deg g=2s:       E Z_g(A_N)=2(p^s+1)p^h+o(1).    (2)

Even means g(-t)=g(t). Each limit fixes the base, p and g first and
then takes N through ALL positive integers. There is no p|N or p|d
exception. The next sections prove the constants, rather than reading
them from a zero entropy exponent.

## Full uniformity: the extra bipartite form

The maximal local lattice and relative local CLT are the frozen central
inputs. The new compatible congruence calculation is proved in
[bipartite-lattice-forms.md](bipartite-lattice-forms.md).

The vector congruences before matching compatibility are

    C_i(a)=sum_(j~i,b) b m_ij(a,b)-(aR)n_i(a)=0.

A compatible 2-by-2 table transfer forces every dual dependency to be

    h_i(a)=K_i a^T+k_i,       K_j=-K_i^T along an edge.

Connectivity now leaves K_i=M on the left and K_i=-M^T on the right.
Root-margin tests, evaluated at a and -a, give the old dual-intertwiner
equation on the constants and the two conditions

    RM and RM^T are skew-symmetric.

Consequently the full-uniform contribution is exactly

    p^(h+b(R))+o(1),
    b(R)=dim_Fp{M: RM and RM^T are skew-symmetric}.         (3)

The compatible integer direction lattice has free integer root margins
and edge-interior entries. It reduces surjectively modulo p, so its
congruence rank determines the exact index, with no saturation assumption.
The legal/independent-star density ratio is p^(krq), while compatibility
retains the reciprocal of its restricted index. Their product is (3).
The independent-star weighted normalizer is exactly 1. The proved
positive weighted Gaussian precision and matching factorial dimensions
justify the full prefactor and fixed-neighborhood tails for every N.

For invertible R set L=RM. The two skew conditions are equivalent to

    L^T=-L,       R^2 L=L(R^T)^2.                          (4)

Thus b(R) counts alternating Fp-valued forms for which R^2 is
self-adjoint. This is the distinction from the odd-cycle calculation.

## The finite-field dichotomy and trace-form dimension

For irreducible g!=t, identify the right-action module with the field

    E=Fp[lambda],       K=Fp[lambda^2].

Since lambda satisfies z^2-lambda^2 over K, the index [E:K] is at most
two. It is two exactly when g is even: the nontrivial automorphism sends
lambda to -lambda, and conversely an even minimal polynomial provides
that automorphism. In the even case r=2s and |K|=p^s.

If g is not even, K=E and R^2 is cyclic. Its self-adjoint alternating
forms vanish in odd characteristic by the proved cyclic-form lemma.
Therefore b(R)=0. Moreover a zero phase has
H_R=lambda H_L and H_L stable under lambda^2; irreducibility of R^2
leaves only the point and full-uniform phases. Each point contributes
1+o(1), giving the second formula of (2).

If g is even, E has dimension two over K. The forms in (4) are exactly
the K-balanced alternating Fp-bilinear forms on E. They are in bijection
with alternating K-bilinear forms Omega via

    beta(x,y)=Tr_(K/Fp) Omega(x,y).

The trace pairing is nondegenerate even when p divides s. To see this
without assuming Tr(1)!=0, its trace polynomial is nonzero and has degree
below |K|. Reconstruct Omega uniquely from
Tr(c Omega(x,y))=beta(cx,y) for every c in K; balance proves K-linearity
in both variables and odd characteristic proves alternation. Hence the
form space has K-dimension one and Fp-dimension s. This proves b(R)=s
and the full-uniform coefficient p^(h+s).

For g=t, R=0 is scalar and the two skew conditions impose no condition
on scalar M. Thus b(0)=1 and full uniformity contributes p^(h+1).

## Even irreducibles: all mixed phases and their exact contributions

The zero-phase classification forces

    H_R=lambda H_L,       lambda^2 H_L=H_L.

Besides H_L=0 and H_L=E, every possibility is a K-line in E. There are

    Q+1=p^s+1

such pairs. Fix one, H_L=uK and H_R=lambda uK. In their coordinates the
restricted maps are

    T_L=I,       T_R=C,

where C is multiplication by c=lambda^2 on K, cyclic over Fp.

Choose any complementary K-line H_L'=u'K and H_R'=lambda u'K.
Both pairs are compatible with multiplication by lambda in both
directions. Thus the complete equation operator, for the base and
EVERY lift, is a direct sum of two identical restricted operators.
If h_H is the restricted old solution dimension, then

    h=2h_H.

The quotient representation is isomorphic to this restriction. Therefore
it has p^(h_H) old point maps, each with an EXACT old lift through the
fixed complementary section. No affine coset obstruction or N-residue
condition remains.

The restricted full-uniform coefficient is exactly p^(h_H):
the left identity map forces its interaction-dependency matrix M to be
skew, and the right map forces CM=MC^T. Cyclicity of C kills M. All
remaining dependencies are the adjoint old solution space, of dimension
h_H. The same saturated integer lattice, exact Q normalizer and relative
Gaussian fraction used in (3) give precisely that coefficient.

This is proved in [mixed-phases.md](mixed-phases.md). For each quotient
point map, translation by its exact old section identifies the zero-defect
part with the restricted HOMOGENEOUS uniform-phase calculation. Thus
one fixed line pair contributes

    p^(h_H) * p^(h_H)=p^h.

It is important here to restrict the within-coset edge tables to the
uniform law of that phase. The entire in-coset restricted moment would
include point phases and double count them.

Leakage outside the cosets is o(1): the frozen sparse-boundary estimate
bounds it by O(N^(-(d-2))) times the restricted homogeneous moment,
which is bounded by the frozen two-space theorem. That estimate includes
the conditional matching-forcing rank bound and does not assume
independence between sparse defects and a large bulk kernel.

Choose disjoint sufficiently small edge neighborhoods around the finitely
many phase centers. All are distinct because their product pair laws
determine their root cosets. Their complements have a strict entropy
gap; exact factorial counts make the remainder o(1). Summing point,
full-uniform and mixed contributions gives

    p^h+p^(h+s)+(Q+1)p^h
       =2(Q+1)p^h,

as asserted in the even case of (2).

## Zero target: two one-sided mixed families

Put s0=dim ker T=dim ker T^T, so h=2s0. There are four subspace pairs:

    (0,0), (Fp,Fp), (Fp,0), (0,Fp).

The point family contributes p^h; the full-uniform phase contributes
p^(h+1). For H_L=Fp,H_R=0, quotient point maps are right old vectors
a_R in ker T, of which there are p^s0. They lift exactly by making
right labels fiber-constant and putting left labels initially zero.
The homogeneous restriction is X^T z_L=0.

Its full legal lattice has one scalar neighbor-sum congruence at each
old right type, giving index p^m. Compatible integer tables are just
arbitrary left root margins. Their first moments S_i=sum_a a n_i(a)
range independently over Fp, and the congruence map is T^T S, of rank
m-s0. Thus its exact uniform coefficient is

    p^m / p^(m-s0)=p^s0.

The singleton-side local CLT, positive root-margin precision and exact
independent-star normalizer retain this fraction for every N. Translating
each quotient point map gives total p^(2s0)=p^h for this mixed family.
The opposite family contributes the same. Narrow uniform edge
neighborhoods and the bounded restricted moment control leakage just
as in the even case.

[zero-target-transfer.md](zero-target-transfer.md) proves these details,
including integer parameterization and all affine residues. Summing
the four families gives (p+3)p^h, completing (2).

## Excess-module probability: the zero case needs a two-step threshold

Fiber-constant pullback injects every old companion space into the lift
space over every field, even when p divides N. For nonzero irreducible g,
the Fp kernel dimensions are multiples of r. Subtract p^h before Markov
and use (2):

    g not even, g!=t:
      limsup_N P[dim ker g(A_N)>h] <=1/(p^r-1);

    g even, r=2s:
      limsup_N P[dim ker g(A_N)>h]
         <=(2p^s+1)/(p^(2s)-1).                           (5)

For g=t the square bipartite block structure gives, over EVERY field,

    dim ker A_N=2 dim ker X,

and h is even too. Therefore any excess is at least two, giving

    limsup_N P[dim ker A_N>h] <=(p+2)/(p^2-1).             (6)

A one-step threshold would not suffice at zero because its moment
coefficient grows like p. Equal base part sizes, and hence square X,
are substantive here.

For p>=3, all bounds (5)-(6) are at most 2/(p-1). This gives a uniform
vanishing bound for every irreducible factor type without controlling
how an integer polynomial factors as the prime varies.

## Complete real spectral transfer

Let F be the squarefree part of charpoly(B), which is the minimal
polynomial because B is real symmetric. It is monic integral and
has nonzero discriminant. Fix any odd prime not dividing disc(F).

For an old irreducible integer factor f of degree ell and old
multiplicity t, factor its squarefree reduction as product_j g_j,
with r_j=deg g_j and sum_j r_j=ell. The base modulo p is annihilated
by squarefree Fbar, hence is semisimple, and its old g_j-kernel
dimension is r_j t.

A new real root of f increases the rational dimension of ker f(A_N)
to at least ell(t+1). The integer matrix f(A_N) cannot gain rank
on reduction modulo p. Polynomial CRT, valid even for nonsemisimple
A_N modulo p, gives

    ker fbar(A_N mod p)=direct-sum_j ker g_j(A_N mod p).

At least one factor exceeds its old geometric baseline. If that factor
is g=t, its excess is automatically even, so (6) applies. Otherwise use
(5). A finite union bound therefore gives

    limsup_N P[new spectrum meets roots(f)]
       <=2 ell/(p-1).

Summing over the fixed old factors yields

    limsup_N P[any old/new collision] <=2 deg(F)/(p-1).     (7)

Good primes are arbitrarily large. Let them tend to infinity AFTER the
lift-size limsup. This proves (1) for bipartite bases and completes it for
ALL fixed connected simple regular bases of degree at least three.

No modular old/new splitting or division by N is used; only the
injective old pullback and total modular kernel dimensions are needed.
The proof in [../module-transfer.md](../module-transfer.md) supplies the
same deterministic transfer in full detail.

## Checks and limits

The companion component notes independently derive the full-uniform,
mixed and zero coefficients. Supplementary exact checks are in
[check-bipartite-lattice.js](check-bipartite-lattice.js) and
[bipartite-lattice-results.json](bipartite-lattice-results.json).
Eight direct compatible-rank cases pass, including K3,3 and the
Heawood cubic base. At p=3 the latter has irreducible old factor
g=t^2+1 with h=12: the full compatible rank is 239 out of 252,
including one extra form. Its line restriction has old dimension six
and rank 36 out of 42 with no extra form.

These finite checks corroborate the dimension-independent proofs.
The result does not assert simple new spectrum, irreducibility of the
new characteristic polynomial, growing-base uniformity, noisy recovery
or spectral disjointness for arbitrary unequal degree frames.

A further trace check in [check-trace-degree6.js](check-trace-degree6.js)
uses the even irreducible polynomial t^6+2t^2+1 over F3. Here s=3 is
divisible by p, so Tr(1)=0, but the extra form dimension is still exactly
three, as proved by the nondegenerate trace-pairing argument. Its result
is recorded in [trace-degree6-results.json](trace-degree6-results.json).

## Final independent audits

All component and assembly audits passed:

- [audit-forms-on-phases.md](audit-forms-on-phases.md) independently
  checks the mixed representations, exact quotient sections, singleton
  phases, leakage and spectral transfer.
- [audit-phases-on-forms.md](audit-phases-on-forms.md) independently
  checks every sign, field dichotomy, trace-form dimension, finite
  lattice fraction, zero-target threshold and common probability bound.
- [audit-zero-on-assembly.md](audit-zero-on-assembly.md) checks the
  complete all-base theorem as written, including disjoint narrow
  neighborhoods, every lift-size residue, modular Jordan issues,
  fixed-prime quantifiers and the precise simple regular base scope.

The main agent also rederived the three cases and executed the eight
generic two-space rank checks plus the degree-six trace check. No
remaining proof gap was found. Historical priority remains unverified.
