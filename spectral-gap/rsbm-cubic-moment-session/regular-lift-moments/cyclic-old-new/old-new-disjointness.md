# Old and new spectra are disjoint for fixed nonbipartite regular bases

Derived November 15, 2026. This is a proof assembled from the finite-field
moment packet and the new cyclic-target lattice calculation. No claim of
historical novelty is made. All previous frozen files remain unchanged.

## The theorem

Let B be the adjacency matrix of a fixed connected simple nonbipartite
d-regular graph, d>=3. Let A_N be the adjacency of its independent
uniform random N-lift. On real vectors let U_N be the fiber-constant
subspace and W_N=U_N^perp. Then

    P[spec(A_N|W_N) intersects spec(B)] -> 0.               (1)

Thus every old eigenvalue retains exactly its base multiplicity with
high probability, including irrational old eigenvalues. The lift size
runs through every positive integer. The theorem concerns exact
equality, without requiring a macroscopic gap around an old eigenvalue.

The new inputs are proved in [cyclic-lattice.md](cyclic-lattice.md),
[module-transfer.md](module-transfer.md), and
[irreducible-moment-assembly.md](irreducible-moment-assembly.md).
The latter two independently check the module transfer. The finite
field always has fixed odd characteristic before N tends to infinity.

## Exact irreducible-companion moment

Fix a monic irreducible polynomial g over Fp of degree r, p odd, and
let R_g be a companion matrix. Set

    H_g(M)={Y: MY=Y R_g},
    h_B(g)=dim_Fp H_g(B)=dim_Fp ker g(B).

The exact moment is

    E |H_g(A_N)|=2p^(h_B(g))+o_(B,p,g)(1).                  (2)

It holds without semisimplicity of B or A_N modulo p and without an
N-residue condition. The equality h_B(g)=r times the characteristic
polynomial exponent is used only at good base primes later.

Here is the complete phase argument. The frozen entropy classification
says that zero phases are common R_g-invariant subspaces plus quotient
coset maps. The row module for an irreducible companion has only the
subspaces 0 and V=Fp^r. Hence there are exactly p^(h_B(g)) point phases
and one full-uniform phase.

Each point phase lifts deterministically and its small support
neighborhood contributes 1+O(N^(-(d-2))) by the frozen sparse certificate
bound. The neighborhoods may be chosen pairwise disjoint and disjoint
from the uniform edge neighborhood. The exact cyclic-target calculation
below gives p^(h_B(g))+o(1) at full uniformity. All remaining types lie
in a compact set with a strict negative entropy gap; uniform factorial
bounds and polynomially many types make their contribution o(1).
This proves (2), including all zero-exponent prefactors.

## The new lattice calculation

Rows a are labels, and the local target is aR. Before compatibility,
the maximal legal directed-table lattice is cut out by

    C_i(a)=sum_(j~i,b) b m_ij(a,b)-(aR)n_i(a)=0 in V.

There are kq vector congruences, q=p^r, giving full index p^(kqr).
This is the maximal lattice proved in the frozen central note.

After identifying reverse edge tables by transpose, the compatible
integer direction lattice K0 has free parameters: arbitrary
total-zero root margins at each old vertex and arbitrary
(q-1)-by-(q-1) interior entries on each undirected edge. Filling the
last row and column is integral. Thus its reduction modulo p is the
ENTIRE compatible field direction space, with no saturation assumption.

Let h_i(a) be a column-vector dependency coefficient for C_i(a).
A 2-by-2 edge-table transfer forces

    (b-b')[h_i(a)-h_i(a')]
      +(a-a')[h_j(b)-h_j(b')]=0.

Setting a'=b'=0 and testing coordinate rows proves

    h_i(a)=K_i a^T+k_i,       K_j=-K_i^T.

Connectivity and an odd cycle force one common skew-symmetric K.
Collecting freely varying root margins leaves

    a(sum_(j~i)k_j-Rk_i)-aRK a^T=0 for every a.

Evaluation at a and -a separates the linear and quadratic pieces in
odd characteristic:

    sum_(j~i)k_j=Rk_i,       RK=KR^T.                       (3)

The first equation's solution dimension equals h_old(R)=dim{X:BX=XR},
by the Frobenius adjoint of the Sylvester operator and B=B^T.

The second condition makes R self-adjoint for the alternating form

    beta(a,b)=aK b^T.

If R is cyclic, choose a cyclic row v. For polynomials f,g,

    beta(vf(R),vg(R))=beta(v,v g(R)f(R)),

which is symmetric in f,g. The alternating form is therefore also
symmetric, so it vanishes in odd characteristic. Degeneracy of the
form causes no exception: no inverse of K is used. Hence K=0 for
every cyclic R, including every irreducible companion.

There are consequently exactly h_old(R) compatible congruence
dependencies, and their restricted rank is

    rho=kqr-h_old(R).                                    (4)

The relative local CLT density ratio of legal to independent stars
is p^(kqr). In the compatible table space, the legal sublattice
occupies exactly the fraction p^(-rho) of the positive weighted
Gaussian sum. The independent-star weighted normalizer is exactly 1,
and its central contribution tends to 1. All integer powers of N,
covariance determinants and matching factorials have already been
retained in that same Gaussian comparison. Thus the uniform
coefficient is exactly

    p^(kqr-rho)=p^(h_old(R)).

The zero legal star provides a compatible affine-lattice point for
every N. Finite-index translated Gaussian sums have the same limit
for every N residue. The fixed-neighborhood tails are controlled by
the positive weighted precision from the frozen central proof.
This establishes the uniform input used in (2).

For noncyclic R an extra term can occur: the general uniform
coefficient is p^(h_old(R)+a(R)), where

    a(R)=dim{K: K^T=-K, RK=KR^T}.

The cyclic condition is substantive and cannot be silently dropped.

## Old modules, geometric dimensions and shifted Markov

For any matrix M over Fp, evaluation at a cyclic column for R_g gives

    H_g(M) isomorphic to ker g(M).

Indeed an intertwiner is determined by w=Yv and must send R_g^j v to
M^j w; the last cyclic relation is exactly g(M)w=0. The latter kernel
is a vector space over Fp[t]/(g), so its Fp dimension is a multiple
of r. No modular diagonalizability is assumed.

The fiber-constant embedding J remains injective over every field,
including p dividing N, and A_NJ=JB. Therefore

    dim H_g(A_N)>=h_B(g)

deterministically. Subtracting its p^(h_B(g)) baseline before Markov,
equation (2) gives

    limsup_N P[dim H_g(A_N)>=h_B(g)+r]
       <=1/(p^r-1).                                      (5)

This detects excess TOTAL modular dimension. A modular decomposition
into canonical old and new summands is unnecessary and may not exist
when p divides N.

## A single finite set of bad primes

Over the integers factor the base characteristic polynomial as

    char_B(t)=product_alpha f_alpha(t)^(t_alpha),

with distinct monic irreducible f_alpha. Put

    F(t)=product_alpha f_alpha(t).

Real symmetry of B implies F(B)=0. Thus F is the squarefree minimal
polynomial and has nonzero integer discriminant. Choose any odd prime

    p not dividing disc(F).                              (6)

These primes are arbitrarily large. At such a prime the reductions
of all f_alpha are squarefree and mutually coprime, and B modulo p
is annihilated by squarefree Fbar. Therefore it is semisimple.

For one f of degree ell and exponent t, factor

    fbar=product_(j=1)^s g_j,       r_j=deg g_j,
    sum_j r_j=ell.

Every old g_j-kernel then has dimension r_j t. No prescribed splitting
pattern is needed. Using the discriminant of char_B itself would be
wrong when the old spectrum has multiplicities; disc(F) is the correct
nonzero integer.

## Transfer a real collision through ker f(A)

Over Q, the old fiber-constant space and the fiber-sum-zero space give
an invariant direct sum, with old restriction B. Their characteristic
polynomial quotient is rational (in fact integral). If the new real
spectrum contains one root of the irreducible f, rationality forces f
to divide the new characteristic polynomial. Since A_N is symmetric,

    dim_Q ker f(A_N)>=ell(t+1).                            (7)

The integer matrix f(A_N) cannot gain rank on reduction modulo p,
so its modular nullity obeys the same lower bound. Because fbar is
squarefree, polynomial CRT gives

    ker fbar(A_N mod p)=direct-sum_j ker g_j(A_N mod p),    (8)

for ANY modular A_N, including matrices with Jordan blocks.
The old dimensions on the right sum to ell t. Thus some j must have
dimension greater than r_j t, and divisibility by r_j makes it at
least r_j(t+1).

Consequently (5), followed by a finite union bound, gives

    limsup_N P[new real spectrum meets roots(f)]
       <=sum_j 1/(p^(r_j)-1) <=ell/(p-1).                 (9)

The integer-rank argument is essential. Characteristic-polynomial
multiplicity modulo p alone could increase through Jordan blocks
without increasing the geometric kernel or companion-Hom dimension.

Summing (9) over the finitely many old factors gives

    limsup_N P[any old/new collision] <=deg(F)/(p-1).

Now let arbitrarily large fixed good primes tend to infinity AFTER
the N-limsup. This proves (1), with no estimate uniform in a growing p.

## Audit and finite checks

The cyclic dependency calculation, exact moment assembly and module
transfer have independent proofs in the component notes above.
Supplementary direct finite-field rank checks are in
[check-cyclic-lattice.js](check-cyclic-lattice.js) and
[cyclic-lattice-results.json](cyclic-lattice-results.json). They include
irreducible, cyclic Jordan and noncyclic control targets, plus the
cubic nonbipartite Mobius graph on eight vertices with the irrational
old factor x^2+2x-1. At p=3 that factor is irreducible, with
h_old=4; the compatible congruence rank is 140 out of 144.

These finite checks corroborate the proof and do not replace it.
The separate [priority-audit.md](priority-audit.md) records a bounded
primary-source comparison; historical firstness remains unverified.

The result here is restricted to fixed connected NONBIPARTITE regular
simple bases of degree at least three. No bipartite extension is
claimed by this packet.

Independent cross-audits passed:

- [audit-module-on-cyclic.md](audit-module-on-cyclic.md) checks all
  cyclic-lattice signs, the alternating-form lemma, integer saturation,
  affine residues, exact Gaussian fraction and direct rank tests.
- [audit-cyclic-on-transfer.md](audit-cyclic-on-transfer.md) checks the
  irreducible moment assembly, geometric module dimensions, finite
  good-prime set, integer-rank/CRT implication and shifted Markov step.
- [irreducible-moment-assembly.md](irreducible-moment-assembly.md) contains
  an additional independent audit of the cyclic calculation and a
  separate full derivation of the modular-to-real transfer.

The main agent also rederived both algebraic calculations and directly
computed seven compatible-congruence ranks, including the irrational
old-factor example. All these checks passed. The previous frozen moment
packet was not modified; only files in this new subdirectory were written.
