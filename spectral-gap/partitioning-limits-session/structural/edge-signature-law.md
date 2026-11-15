# Exact balanced-cut response to finitely many edge edits

Research note, 2026-11-15. This is a proved structural statement with a
bounded-degree sharpness construction. Historical priority is **not** established.
The envelope observation is elementary parametric discrete optimization and
should not be sold as a new spectral method.

## 1. Exact signature law

Let G be a finite weighted graph on an even number N of vertices. Let
e_1,...,e_k be distinct edges, and increase their conductances by
t=(t_1,...,t_k) in R_+^k. A bisection is identified with its complement.
For a bisection S let chi(S) in {0,1}^k record which edited edges it cuts.
Put

    a_sigma = min { cut_G(S) : S a bisection, chi(S)=sigma },

with +infinity for an empty family, and let M_sigma be the corresponding
set of family minimizers.

**Theorem 1.** The complete optimal-bisection response is

    OPT(t) = min_sigma [a_sigma + t dot sigma],
    argmin cut_{G(t)}
       = union { M_sigma : a_sigma+t dot sigma=OPT(t) }.

Consequently at most 2^k different bisections can occur as unique
optimizers (modulo complement) as t ranges over R_+^k. For k=1 there is at
most one switch, at t=a_0-a_1 when this threshold is nonnegative. Optimizers
cannot switch between distinct bisections having the same signature.

**Proof.** For every S,

    cut_{G(t)}(S) = cut_G(S) + t dot chi(S).

Within one signature family the additive term is independent of S.
Minimize first within families and then over signatures. If a family has
two minimizers, they remain tied at every parameter, so neither is ever a
unique global optimizer. This proves the count bound.

The same identity describes *all* delta-near-optimal cuts exactly: a cut S
of signature sigma is delta-near-optimal if and only if

    cut_G(S)-a_sigma
       <= delta - [a_sigma+t dot sigma-OPT(t)].

This law concerns the unnormalized cut objective with an exact cardinality
constraint. It is not automatically a conductance/normalized-cut law,
because degrees and volumes also change under the edits.

## 2. The 2^k bound is sharp on bounded-degree unweighted hosts

**Theorem 2.** For every k>=1 there is a connected simple unweighted graph
G of maximum degree at most 14, with k designated existing edges, such
that all 2^k edit signatures occur as different unique minimum bisections
(modulo complement) at parameters in the finite box

    t in {0, 201/100}^k.

The number of vertices can be large; no polynomial-size claim is made.

We use only the following classical expander existence consequence of
Friedman's theorem: for every sufficiently large even m there is a simple
13-regular graph H_m such that every U with |U|<=m/2 satisfies

    |boundary_Hm(U)| >= h |U|,   h=151/50=3.02.

Indeed Friedman permits adjacency second eigenvalue at most
2 sqrt(12)+0.01<6.96; the variational spectral bound gives edge expansion
at least (13-6.96)/2=3.02. Only this standard existence input is used.

**Construction.** Choose even cloud sizes m_i recursively so that

    m_1 > 4k,
    m_i > 2 sum_{j<i}m_j + 2k   (i>1),

and large enough for the stated expanders. Gadget i has four disjoint
clouds A_i,B_i,C_i,D_i, each a copy of H_{m_i}. Insert one edge A_i-B_i,
one C_i-D_i, two A_i-C_i edges, and two B_i-D_i edges. The two edges
between the same pair of clouds use different endpoints, so the graph
is simple. The A_i-B_i edge is the designated edited edge e_i.

Connect consecutive gadgets by one edge B_i-A_{i+1}. Choose all external
ports in each cloud distinct. Thus each vertex has at most one external
edge and the maximum combinatorial degree is at most 14. The graph is
connected and all baseline conductances are one.

For each gadget the three ways to divide whole clouds two against two
have costs

    P_i = A_i B_i | C_i D_i : 4,
    Q_i = A_i C_i | B_i D_i : 2+t_i,
    R_i = A_i D_i | B_i C_i : 6+t_i.

**Cloud-indivisibility proof.** There is always a bisection of cost 4k:
use P_i in every gadget and orient the gadgets along the connecting path
so every connecting edge is uncut. Therefore every optimum S has cost
at most 4k.

For each cloud let r_cloud be the number of vertices on its minority
side, and put r=sum r_cloud. Expansion charges h r to the cut, hence

    r <= 4k/h < 2k.

No cloud has a tied majority, since m_i/2>2k. Round every cloud to its
majority side, obtaining Sbar. If q_i is the number of clouds of gadget i
rounded into Sbar, then

    ||Sbar|-N/2| = |sum_i (q_i-2)m_i| <= r < 2k.

The superincreasing inequalities force q_i=2 for every i. To see this,
take the largest index i with q_i-2 nonzero: its contribution has absolute
value at least m_i, while all preceding contributions have total absolute
value at most 2 sum_{j<i}m_j, leaving a difference greater than 2k.
The i=1 case follows from m_1>4k. Thus Sbar is itself a bisection.

Rounding removes all internal cuts, decreasing cost by at least h r.
Every changed vertex has at most one external incident edge, and every
external conductance is at most 1+201/100=301/100=3.01. The external cost
can therefore increase by at most 3.01 r. Since h>3.01, any r>0 strictly
improves the cut, contradicting optimality. Every optimal bisection leaves
every cloud whole and divides each gadget two against two.

**Sharpness conclusion.** At t_i=0 the unique best local division is Q_i;
at t_i=201/100 it is P_i. Once these local divisions are chosen, orientations
can and must make all path edges uncut. The path determines all orientations
from the first, leaving only global complementation. Thus every one of the
2^k choices gives a different unique global optimum.

## 2b. A sharp one-edit versus two-edit discontinuity law

For unweighted graphs, or integer baseline conductances, an extra exact
restriction is easy to miss.

**Theorem 3.** Under one unit conductance increase or decrease of one edge,
the old and new families of minimum bisections have nonempty intersection.
If the old minimum bisection is unique modulo complement, it remains
optimal after the edit. In particular, one unit insertion/deletion cannot
force a unique minimum bisection to become a different unique minimum
bisection.

Two unit edge insertions suffice for an orthogonal jump between unique
minimum bisections, on connected simple unweighted graphs of maximum degree
five and arbitrarily large order. The same holds for two existing-edge
doublings on an unweighted baseline.

**Proof of the upper restriction.** Baseline cut costs are integers. If the
old optimizer S is unique, every competitor costs at least cut(S)+1.
One unit edge edit changes the difference between two cut costs by at most
one, so S stays optimal. For the statement with ties, choose among the old
minimizers one with minimum edited-edge signature for an increase, or
maximum signature for a decrease. If the chosen signature has favorable
sign, its objective does not worsen; otherwise every old minimum changes
by the same amount and every other cut starts at least one unit above it.
In each case this chosen old minimum remains optimal. This proof applies
to any fixed feasible cut family, including exact bisections.

**Sharp construction.** Fix an odd integer m>=5. Make four equal clouds
A,B,C,D, each the square of the cycle C_m. The edges of distances one and
two form two edge-disjoint Hamilton cycles, so every nontrivial split of
a cloud cuts at least four internal edges.

Insert one AB edge, one CD edge, one AC edge, and two BD edges, using
distinct external ports in every cloud. All baseline conductances are one.
The whole-cloud bisections have costs

    P=AB|CD : 3,    Q=AC|BD : 2,    R=AD|BC : 5.

Every optimum has cost at most three, and therefore cannot split a cloud.
The baseline optimum Q is consequently unique modulo complement. Insert
one additional AB edge and one additional CD edge, again via unused ports.
The three costs become 3,4,7, so P is now the unique optimum. Each cloud
needs at most four distinct external ports, available since m>=5. Every
vertex has four internal edges and at most one external edge, so both
graphs are simple, connected, and have maximum degree at most five.

The normalized sign vectors of P and Q are orthogonal: their signs on
the four equal clouds are (+,+,-,-) and (+,-,+,-). After the better global
complement choice, exactly half the vertices change sides. Letting odd
m tend to infinity gives arbitrarily large examples. Alternatively double
the two existing AB and CD edges; the same three cut costs and uniqueness
conclusion follow.

For a single existing AB-edge conductance increase by an arbitrary real t,
the same construction has costs 3,2+t,5+t. Its unique optimum switches at
t=1: a unit doubling creates a tie, and every increase larger than one
selects the other unique bisection. Thus the one-unit endpoint is exact.

## 3. Exact cutspace at the simultaneous transition

In the same graph set every t_i=2. P_i and Q_i tie, while R_i is worse.
The preceding cloud-rounding proof still applies. Thus there are exactly
2^k optimal bisections modulo complement, all of cost 4k.

Their centered sign vectors span a space of dimension exactly k+1. To
verify this, fix the sign on A_1 to be +1 and let p_0=1. The successive
path alignments allow p_1,...,p_k to vary independently in {+1,-1}. The
signs on gadget i are

    (A_i,B_i,C_i,D_i) = (p_{i-1}, p_i, -p_i, -p_{i-1}).

Write x(p)=v_0+sum_{j=1}^k p_j v_j. Here v_0 is supported on A_1,D_1;
v_k is supported on B_k,C_k; and v_j, 0<j<k, is supported on
B_j,C_j,A_{j+1},D_{j+1}. These k+1 vectors have pairwise disjoint nonempty
supports. All belong to the span of the x(p), by averaging x(p) and p_j x(p)
over the cube. Hence the dimension is exactly k+1.

This provides a concrete all-optimizer space, but does **not** imply an
approximation lower bound of k+1 at fixed normalized error: the cloud sizes
are superincreasing and some directions have small normalized mass.

## 4. A four-vertex certificate separating Fiedler behavior from the cut optimum

There is an especially transparent weighted example, with unit vertex
masses, on vertices a,b,c,d and cycle conductances

    w_ab=1+t, w_cd=1, w_ac=w_bd=2,       t>0.

Its three bisections have precisely the costs P=4, Q=2+t, R=6+t above.
Thus Q uniquely minimizes for t<2 and P uniquely minimizes for t>2.
The normalized sign vectors for P and Q are orthogonal, so the optimum
jumps by half the vertices even across an arbitrarily small change in t.

Let

    p=(1,1,-1,-1)/2,
    q=(1,-1,1,-1)/2,
    r=(1,-1,-1,1)/2.

These are an orthonormal basis of the orthogonal complement of constants.
The Laplacian acts by Lp=4p, and on span(q,r) it has matrix

    [ 2+t    t   ]
    [  t    6+t ].

Its eigenvalues are 4+t +/- sqrt(4+t^2). Consequently the Fiedler
eigenvalue is simple for every t>0 and is the minus choice, strictly below
4. Its eigenvector is proportional to q+c(t)r, where

    c(t) = [2-sqrt(4+t^2)]/t,       -1<c(t)<0.

Its positive vertices are always a,c, so its sign cut and its exact
median bisection are always Q. For t>2 the approximation ratio is
(2+t)/4, unbounded as t tends to infinity. This is an exact weighted
four-vertex example; it is not a bounded-conductance unweighted family.

At the combinatorial transition t=2, the spectral gap above Fiedler is

    lambda_3-lambda_2 = 2 sqrt(2)-2 > 0.

Thus even a nonvanishing Fiedler eigengap cannot certify uniqueness or
continuity of the exact balanced-cut optimizer. Across t=2 +/- eta,
the change in L is exactly 2 eta (e_a-e_b)(e_a-e_b)^T, of rank one,
and the two optimal cuts remain orthogonal. Moreover, relative to L(2-eta),
the perturbation norm on constants-perpendicular is at most
2 eta/(3-eta), by the edge-resistance bound R_ab<=1/(3-eta).

The first-order spectral decomposition above is an exact certificate for
why Fiedler fails here: the cut direction p has Rayleigh quotient four,
but the continuous relaxation can lower energy by mixing q and r, while
the median cut cannot change its q-signature.

## Primary sources and scope

* Joel Friedman, *A proof of Alon's second eigenvalue conjecture and related
  problems*, https://arxiv.org/abs/cs/0405020 — only the standard expander
  existence input in Theorem 2 is attributed to this source.
* *Complexity of Source-Sink Monotone 2-parameter min cut*, publisher page
  https://www.sciencedirect.com/science/article/abs/pii/S0167637721001796
  — related parametric minimum-cut
  complexity; its multiple-edge parameter dependence differs from the
  edited-edge signature count used here. The search-returned publisher
  abstract states an exponential parametric-cut claim; the full text and
  exact bibliographic metadata were not inspected.
* Recent low-eigenspace/cut-dimension work:
  https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX-RANDOM.2025.16
  discusses approximate containment of sparse cuts in low spectral spaces.
  The present note does not claim to improve those guarantees.

The upper envelope identity and the four-vertex example are elementary.
The bounded-degree sharpness argument is the substantive construction in
this note. No historical-firstness claim has been established, and no
general spectral-partitioning breakthrough should be inferred.
