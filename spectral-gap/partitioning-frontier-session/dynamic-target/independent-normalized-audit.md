# Independent normalized-response audit — 2026-11-15

Scope: reconstruction of the parent session's proposed normalization-aware
fractional energy and its four-vertex quadrature obstruction. These are
mathematical checks; historical novelty is not certified. No dynamic
partitioning approximation or update-time breakthrough follows yet.

## 1. Correct object and determinant identity

Let a connected graph have combinatorial Laplacian L, positive degree
matrix D, degree vector d=D1, and volume v=1^TD1. For 0<α<1 put

    Hα(D,L)=D^(1/2)(D^(-1/2)L D^(-1/2))^α D^(1/2).

This is the weighted operator geometric mean D#αL. Its kernel is exactly
span{1}; joint monotonicity of the geometric mean implies
Hα(D',L')≥Hα(D,L) after a positive edge update. This fixes the moving
kernel of the ordinary normalized Laplacian. A direct comparison of
normalized fractional Laplacians in relative Loewner order fails whenever
their nullvectors differ.

The exact identity on 1-perp is

    pdet Hα=(pdet L)^α (n detD/v)^(1-α).

Independent derivation: regularize the normalized Laplacian N by εI.
The determinant of Hε=D^(1/2)(N+εI)^αD^(1/2) is asymptotic to
detD·ε^α·(pdetN)^α. Its new rank-one leading term on the kernel of H is
ε^α dd^T/v. On the unit vector 1/√n this has quadratic form ε^α v/n,
so detHε~ε^α(v/n)pdetH. Finally
pdetN=v·pdetL/(n detD), by the cofactor formula. Combining gives the claim.

For L'=L+δbb^T, D'=D+δ(e_ue_u^T+e_ve_v^T), and
R=b^TL†b, the relative PSD response C=H^(-1/2)(H'-H)H^(-1/2) has

    log det(I+C)=B
      =α log(1+δR)
       +(1-α)[log(1+δ/d_u)+log(1+δ/d_v)-log(1+2δ/v)].

All inverses here are restricted to 1-perp. Consequently
N_C(ε) < B/log(1+ε) for N_C(ε)>0. This is a determinant count, not an
attainability theorem or a conductance approximation.

## 2. Positive factor integrals checked independently

Write cα=sin(πα)/π, M=L+δbb^T, E=[e_u,e_v], and R_t=(L+tD)^(-1),
Q_t=(M+tD)^(-1). Then H'-H=Δ_L+Δ_D, where

    Δ_L=cα∫₀∞ δt^α DR_t b b^T R_tD/(1+δ b^TR_tb) dt,

    Δ_D=cα∫₀∞ t^(α-1) M Q_t E
             (δ^(-1)I₂+tE^TQ_tE)^(-1)E^TQ_t M dt.

Each integrand is PSD and has rank at most one or two; every factor
column sums to zero. To verify the second identity without inverting
singular L, use

    D-tD(L+tD)^(-1)D = t^(-1)[L-L(L+tD)^(-1)L]

and Woodbury for tδEE^T. These positive formulas are exact but do not
by themselves establish a gap-free quadrature or charged construction.

An alternative exact reduction uses S(D)=D-dd^T/v, the shorted mass
matrix. On 1-perp,

    Hα(D,L)=L#_(1-α) S(D).

This follows by taking the Schur complement of D along the nullspace of
L in the standard geometric-mean perspective. A degree update has the
rank-two PSD shorted update

    S(D')-S(D)=F K F^T,
    F=E-d(1,1)/v,
    K=δI₂-δ²(1,1)^T(1,1)/(v+2δ).

Direct expansion proves this formula; K>0. Thus the mass update is a
classical rank-two positive update after shorting, but its natural metric
contains L† and does not inherit the old dipole maximum-principle bound.

## 3. An exact worst determinant budget for unweighted edge doubling

For every connected simple unweighted graph with m≥2 edges, doubling an
existing unit edge satisfies

    B≤αlog2+(1-α)log[3m/(m+1)].

This upper bound is attained precisely when the edited edge is a bridge
with endpoint degrees {1,2}. Indeed R≤1, v=2m, and the endpoint-degree
product (1+1/d_u)(1+1/d_v) is at most 3: both degrees cannot equal one
in a connected graph with m≥2, and the product decreases in either
degree. Equality in the leverage term requires a bridge and equality in
the degree product requires {1,2}. A path of any m≥2 has such an edge.
For m=1 the budget is log2. For arbitrary weighted edge doubling the
simple universal bound B≤(2-α)log2 follows from δR≤1 and δ≤d_u,d_v;
the unweighted bound uses integrality of degrees.

This is only sharpness of the total determinant budget. It does not
settle the maximum number of ε-sized relative modes: compulsory local
response can consume budget, as already happens in the repository's
unnormalized sharp degree theorem.

## 4. Four-vertex obstruction to copying the old cutoff

Take the weighted path with edge weights (1,h,1), 0<h<1, double its first
edge, and let x=(1,1,-1,-1). The edited-edge leverage is exactly one,
n=4, the total volumes stay bounded, and all endpoint degree ratios stay
bounded as h→0. Nevertheless

    x^THα(D,L)x =4h^α(1+o(1)),
    x^THα(D',L')x =4h^α(4/3)^(1-α)(1+o(1)).

Independent reconstruction: before the update the two fast components
have degree masses 2 and 2. Their one nonzero slow generalized eigenvalue
is h(1/2+1/2)=h+O(h²), and x has slow mass 4. After the update the masses
are 4 and 2, the slow eigenvalue is 3h/4+O(h²), and the D'-centered x has
slow mass 16/3+O(h). Contributions from the fast modes to x's fractional
energy are O(h²). This gives the formulas above.

For any fixed lower integration cutoff t_->0, the retained integrals in
section 2 have x-energy O(h²). For the mass term use
x^TMQ_tE=(Mx)^TQ_tE=O(h/t), since Mx=O(h). For the edge term, x^Tb=0
and the resolvent identity give
x^TDR_tb=-t^(-1)(Lx)^TR_tb=O(h/t²). The inverse resolvents are bounded
uniformly for t≥t_-, and their large-t decay makes the integral bounds
integrable. Therefore the retained response divided by x^THx tends to
zero, while the exact relative quadratic response tends to
(4/3)^(1-α)-1>0.

The conclusion is narrow and useful: this particular positive integral
has no relative-accurate low cutoff depending only on n, leverage, ε,
bounded endpoint degree ratios and bounded total volume. A cutoff must
resolve h or be supplemented by a separate low-frequency construction.
This does not prove impossibility of a different gap-free algorithm.

## 5. Strong target and what it would still need

For the normalization-aware Hα, construct a PSD factor X with

    -εHα ≼ Hα'−Hα−XX^T ≼ εHα,
    rankX ≲ B/ε,

in expected (m+n)polylog(n,1/ε,1/δ_failure) exact-real work for unit edge
doubling, with no hidden inverse normalized gap or conductance-ratio
dependence. The four-vertex example identifies a genuine missing part in
the old charged proof: positive tail truncation alone does not do this.
An algorithm must capture component-mass changes at arbitrarily small
spectral scales. Even proving this target would still need a separate
rounding/query theorem before it implied faster balanced partitioning.

No claim of historical priority or a field-scale breakthrough is made.
