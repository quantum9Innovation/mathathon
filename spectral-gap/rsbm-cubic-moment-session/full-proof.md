# Planted eigenvalue simplicity for the uniform (2,1) model

Prepared November 15, 2026. This is a derived argument with exact counting
and lattice calculations supplied in the three companion notes. No claim
of historical novelty is made.

## Result

Let C1,C2 be independent uniform simple degree-two graphs on N vertices.
Let the cross edges form an independent uniform perfect matching.
Relabeling the second block by the matching gives

    A = [ C1  I ],       sigma=(1_N,-1_N),       A sigma=sigma.
        [ I  C2 ]

For every fixed odd prime p,

    limsup_(N→∞) E |ker_Fp(A-I)| <= (1+exp(3/2)) p.             (1)

The coefficient is independent of p. Consequently

    P(dim_R ker(A-I)=1) → 1.                                  (2)

This proves the requested even-N case. The proof uses no parity
restriction and applies along all block sizes N→∞. Every intermediate
limit fixes p first; no estimate uniform in a growing prime is needed.

## Exact configuration-model moment

First independently pair 2N distinguished internal stubs in each block.
A loop contributes twice to the adjacency diagonal. Conjugating A-I
by diag(I,-I) gives the same kernel size and the equations

    C1 x=x+z=C2 z.

We prove

    E_config |ker_Fp(A-I)| = 2p+o_p(1).                        (3)

At a coordinate let A=x_i, D=z_i, and write B,C and E,F for the two
ordered neighbor labels in the first and second blocks. Then

    B+C=A+D=E+F.

Thus a local profile is specified by (A,D,B,E) in Fp^4. Its two
directed stub tables are

    W1[a,b]=1_(A=a)(1_(B=b)+1_(A+D-B=b)),
    W2[d,e]=1_(D=d)(1_(E=e)+1_(A+D-E=e)).

For N profiles let m1,m2 be their sums. Pairing is possible exactly
when each table is symmetric with even diagonal. For a valid table set

    P(m)=product_(a<b) m_ab! product_a (m_aa-1)!!,

and set P(m)=0 otherwise; (-1)!!=1. With iid uniform profiles the exact
distinguished-stub pairing count gives

    E_config |ker(A-I)|
      =p^(4N) E[P(m1)P(m2)] / ((2N-1)!!)^2.                  (4)

## Entropy: only uniformity and planted constants can contribute

The exact ordered-star type enumeration and its entropy identity are
proved in [entropy-types.md](entropy-types.md). In ungauged coordinates
let pi=law(A,B) be the central pair law, q1,q2 the ordered-star laws,
and rho1,rho2 their normalized directed edge tables. Every type summand
has logarithm

    N F(q1,q2)+O_p(log(N+1)),
    F=H(q1)+H(q2)-H(pi)-H(rho1)-H(rho2).

Let sj symmetrize the two neighbor slots in qj. An exact chain-rule
identity is

    F = -I(A;B)-I_s1(B;U|A)-I_s2(A;C|B)
        -D(q1||s1)-D(q2||s2) <= 0.                           (5)

Equality holds precisely at the completely uniform type and the p
planted constant types. Indeed conditional independence and the two
slot reflections force uniform neighbor laws whenever one central
law is nonconstant: the difference of two support values generates
the additive group of Fp. Edge symmetry then forces both central
laws uniform. If one is constant, edge symmetry and the equations
force a planted constant.

For fixed p, compactness supplies a strictly negative entropy gap
outside any neighborhoods of those p+1 types. There are at most
(N+1)^(2p^3) ordered-star type pairs, so this region contributes
exponentially little, including all Stirling prefactors. The two
zero-exponent sectors require the estimates below.

## The uniform neighborhood contributes exactly p

[central-types.md](central-types.md) evaluates (4) when both edge
tables lie in a sufficiently small fixed neighborhood of (2N/p^2)J.
All Gaussian, lattice and polynomial factors are retained.

Put d=p(p-1)/2, s=d+p-1, r=p^2-1=d+s. On the real space of
total-zero tables the one-block covariance and determinant are

    Sigma=(2/p^2)(I+R),
    det Sigma=(4/p^2)^(p-1)(2/p^2)^(2d),

where R is row-constant orthogonal projection. The two blocks have
zero cross-covariance. The full joint support-difference lattice has

    covol(L)=p^5 2^(2p-2).

Its index in all integer fixed-total table pairs is 2^(2p-2)p^3:
even row sums and three independent field congruences. After imposing
symmetry AND even diagonals, the valid difference lattice has

    covol(K)=p^4 2^(d+4p-4),
    covol(L)/covol(K)=p 2^(-d-2p+2).

Only two field congruences survive symmetry. The valid affine lattice
is nonempty for every N, with no residue-class exception when p divides N.

For m=(2N/p^2)J+sqrt(N)X, uniformly on ||X||<=log N,

    P(m)/(2N-1)!!
      =p^(-2N)(4 pi N/p^2)^(d/2)2^((p-1)/2)
       *exp[(p^2/8)||X||^2](1+o_p(1)).

A relative lattice local CLT follows from exponential tilting and
Fourier inversion; its proof is included in the companion note.
On symmetric tables the pairing weight modifies the Gaussian
precision to p^2/8 with multiplicity p-1 and p^2/4 with multiplicity d.
Its one-block integral is

    I=(2 pi)^(s/2)(8/p^2)^((p-1)/2)(4/p^2)^(d/2).

The resulting coefficient is

    (4 pi/p^2)^d 2^(p-1)(2 pi)^(-r)(det Sigma)^(-1)
      *[covol(L)/covol(K)] I^2 = p.                           (6)

The powers of N cancel since d-r+s=0. The positive resulting
precision bounds the rest of the fixed uniform neighborhood by a
polynomial times exp(-c_p log^2 N). Its total contribution is p+o_p(1).

## All planted neighborhoods contribute p+o_p(1)

[near-constant.md](near-constant.md) allows arbitrary field cancellations.
Let Z_k count kernel vectors supported on exactly k individual coordinates
after subtracting a planted constant. With an absolute D=12288 exp(2),
for every k<=N/4,

    E Z_k <= 2k(Dp)^k(k/N)^(k/2).                             (7)

The certificate consists of every internal edge incident to the support.
Collapse each cross-matching pair. If k coordinates are occupied, the
certificate satisfies E-V>=k/2. A zero coordinate matched to an occupied
one needs at least one internal support neighbor. A zero coordinate
in an untouched pair needs two whenever it has any. This proves the
excess inequality even when neighbor values cancel.

Counting support locations, labels, stubs and pairing probabilities
gives (7). Support one is impossible. For a sufficiently small fixed
epsilon_p, its terms decrease geometrically for
2<=k<=epsilon_p N, so

    sum_(2<=k<=epsilon_p N) E Z_k=O_p(N^-1).

Translation by each planted vector is a kernel bijection, and the p
neighborhoods are disjoint. Their contribution is p+O_p(N^-1).
Every sufficiently small constant type neighborhood is included in
one of these support neighborhoods.

Choose these constant central-pair neighborhoods and the uniform
edge-table neighborhood disjoint. Their complement in the feasible
type space is compact and contains no zero of (5), so it contributes
exponentially little. Combining the estimates proves (3).

## Direct conditioning to uniform simple graphs

For a degree-two configuration, simplicity probability tends to
exp(-3/4). A direct labeled enumeration uses

    G(z)=exp(sum_(j>=3) z^j/(2j))
        =(1-z)^(-1/2) exp(-z/2-z^2/4).

Every labeled simple degree-two graph has exactly 2^N distinguished
stub pairings. Thus simplicity probability is the coefficient ratio
of G(z) and (1-z)^(-1/2). The ratio tends to exp(-3/4): convolve the
entire factor with [z^N](1-z)^(-1/2)~1/sqrt(pi N); its exponentially
small coefficient tails justify the limit for all N.

The two blocks are jointly simple with probability s_N→exp(-3/2).
Conditional on this event they are exactly independent uniform simple
degree-two graphs. The planted p vectors occur deterministically.
Subtracting their contribution before conditioning gives

    E_simple |ker(A-I)|
      <=p+[E_config |ker(A-I)|-p]/s_N,

which proves (1). No contiguity or substitution of a different
degree-two ensemble is used.

## Real corank and polynomial exact recovery

For an integer realization, real nullity at least two forces nullity
at least two over every Fp: all minors of order 2N-1 vanish as integers.
The planted line supplies at least p field solutions. Thus (1) gives

    limsup_N P(dim_R ker(A-I)>=2) <= exp(3/2)/(p-1).

Let fixed odd primes tend to infinity AFTER the limit superior in N.
This proves (2). Exact rational nullspace computation then recovers
the planted line, hence the two communities up to exchange, with high
probability in polynomial bit complexity. This implication requires
no spectral separation.

## Independent checks

The sparse certificate, covariance, Stirling constants, lattice
covolumes, and Gaussian cancellation were independently audited.
[audit-nearconstant-review.md](audit-nearconstant-review.md) records
the audit. An explicit even-diagonal condition was added to K's
definition; the covolume calculation already included that condition.

[lattice-check.js](lattice-check.js) checks covariance and the full
support-difference lattice index by exact integer arithmetic for
p=3,5,7. These finite checks supplement the character proof for every
odd prime in [central-types.md](central-types.md).

The independent obstruction-session team subsequently audited the entire
assembly and reported no substantive gap. That review explicitly checked
the compact complementary type region, the conversion from constant
pair types to individual-coordinate support, disjointness from the
uniform edge neighborhood, agreement of the two exact type enumerations,
conditioning after subtracting the planted p vectors, the Markov bound,
and the absence of an N-residue restriction. This remains a derived
theorem with historical novelty unasserted.
