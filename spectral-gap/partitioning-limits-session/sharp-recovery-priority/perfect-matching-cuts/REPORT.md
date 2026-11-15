# Formula-specific primary-literature audit: cubic (2,1) recovery

2026-11-15. Scope: the claimed ambiguity constant `4/N^2` and Bayes-error
constant `2/N^2`, with **block** size N, in the independent uniform-simple
two-class RSBM. Comparison input:
`spectral-gap/rsbm-exact-ambiguity-asymptotic.txt`, SHA256
`c1c4bf4e5e6411ce6fb58e5745da7f1590a07590d89d39111649090413e67af5`.
The general coefficient in that file and the complete-base random-lift
note were read as context; this report is not a fresh proof audit of them.

**Finding:** no inspected primary theorem states these two constants or
directly supplies their relative-order counting refinement. However, both
the cubic solution object and multiple-decomposition enumeration have
substantial prior work. The strongest concrete overlaps are the current
cycle-permutation enumeration and an older annealed metastable-state count.
This is a limited priority search, not a firstness certification.

## Exact terminology and the statistic that must be compared

In a cubic graph, an equitable (2,1) partition is exactly a **perfect
matching-cut bipartition**: every vertex has one crossing edge, so the
crossing edges form a perfect matching and the induced graphs on the two
sides are 2-regular. The sides automatically have equal size, because the
cross matching saturates both. Thus the old combinatorial object is
precisely relevant, not merely an analogy.

The terminology has traps. A perfect matching *whose deletion disconnects
the graph* need not itself be an entire edge cut; modern papers call this
a disconnected perfect matching. Counting all 2-factors or perfect
matchings is also insufficient. Finally, “stable cut” in the recent
NAC-colouring literature means an **independent vertex separator**, a
different object. Local single-spin stability is the relevant Ising
connection below.

The definitions and the distinction between perfect matching cuts and
disconnected perfect matchings are explicit in Le–Telle, *The Perfect
Matching Cut Problem Revisited*, Section 1, PDF pp. 1–2. Its results are
decision complexity and exact branching algorithms, rather than random
planted error constants. [Primary author PDF](https://jatelle.github.io/bib/BT21.pdf),
[published paper](https://doi.org/10.1016/j.tcs.2022.07.035).

## Closest finite enumeration: alternative cycle-permutation decompositions

Goedgebeur–Renders–Van Overberghe, *Generation of Cycle Permutation Graphs
and Permutation Snarks*, **v4, 7 May 2026**, Theorem 1 (Section 2.1.3),
proves that their strong generator outputs every unlabelled cycle
permutation graph once. Section 2.1.2 explicitly maintains all alternative
permutation 2-factors. Section 2.2 describes a weaker generator that keeps
the starting factor; duplicates arise from alternative factors. Appendix D,
Table 4, printed p. 26, reports:

| Total vertices | Strong count | Weak count |
|---:|---:|---:|
| 16 | 123 | 127 |
| 20 | 4,815 | 4,975 |
| 28 | 54,828,142 | 55,670,332 |
| 32 | 10,118,035,593 | 10,217,376,792 |
| 34 | 152,626,831,184 | 153,848,448,652 |

These are genuine earlier finite counts reflecting multiple
decompositions. They are neither a random planted probability nor an
asymptotic error formula. The full current text contains no asymptotic
probability theorem. [Current primary PDF](https://arxiv.org/pdf/2411.12606v4),
[version history](https://arxiv.org/abs/2411.12606).

**Why its strong/weak ratio is not the ambiguity or Bayes error.** This is
our comparison, not a claim made by that paper. A permutation 2-factor
requires precisely two induced Hamilton cycles. Uniform-simple 2-regular
RSBM internals may each contain many cycles. Even after conditioning both
internals to be Hamilton cycles, unlabelled graph counts and factor orbits
under automorphisms differ from labeled planted-partition counts.

In particular, multiple factors in the same automorphism orbit need not
produce an additional weakly canonical graph. The cube Q3 has three
coordinate perfect-matching cuts, permuted by its automorphisms. A count
modulo such symmetries can retain one representation while there are three
distinct vertex bipartitions. Therefore neither `1-strong/weak` nor twice
that number is the requested RSBM statistic. The table supplies close prior
enumeration, but extracting sharp statistical constants requires additional
weights, multiplicities, and a model comparison.

## Earlier graph-cover and natural-isomorphism formulas

Stueckle, *On natural isomorphisms of cycle permutation graphs* (1988),
explicitly restricts to isomorphisms preserving the two designated cycles,
possibly swapping them. The publisher abstract states counting results for
permutations producing such naturally isomorphic representations; the full
subscription text was not inspected. [Primary publisher page](https://doi.org/10.1007/BF01864155).

Kwak–Lee, *Isomorphism classes of cycle permutation graphs* (1992), views
the graphs as dumbbell covers and counts positive natural-isomorphism
classes via dihedral double cosets. Only its primary publisher abstract was
available. [Primary publisher page](https://doi.org/10.1016/0012-365X(92)90137-5).

Their 1998 paper *Isomorphism classes of bipartite cycle permutation
graphs* reproduces the earlier characterization as **Theorem 1, printed
p. 141**. With rho an N-cycle and Gamma generated by dihedral conjugation
and inversion on N-cycles, positive natural isomorphism is equivalent to

`beta^{-1} rho beta` belonging to the Gamma-orbit of
`alpha^{-1} rho alpha`.

It also gives positive-natural-class counts for the bipartite subclass:
N = 2,4,6,8,10,12 yields 1,1,3,11,104,1952 (printed p. 147).
The designated-cycle-preserving restriction is explicit on p. 140. These
formulas do not count all alternate planted vertex partitions.
[Primary scanned PDF](https://combinatorialpress.com/article/ars/Volume%20050/volume-50-paper-10.pdf).

This older cover language is a genuine precedent. It does not establish
the exact planted ambiguity asymptotic, since a covering representation
with specified fibers and the underlying graph with all possible fibers
are different counting objects.

## Closest analytical count: ferromagnetic metastable states

Lefevre–Dean, *Metastable states of a ferromagnet on random thin graphs*
(2000; published 2001), studies fixed-degree random graphs. Its equation
(4) defines the ensemble by conditioning independent edges on all degrees
being c, hence a uniform simple c-regular graph. Equation (18) counts
single-spin-stable configurations at fixed energy; equation (19) gives
their annealed logarithmic complexity by a saddle-point expression.
Section 3 also fixes magnetization. [Primary preprint](https://arxiv.org/pdf/cond-mat/0011265).

**Exact connection, inferred here:** for cubic ferromagnetic graphs the
stable local field at each spin is 1 or 3. Energy per vertex -1/2 forces
every local field to equal 1. Those configurations are exactly the (2,1)
sign partitions, with their two global orientations counted separately.
Thus this is old analytical counting of the same cubic solution object.
It supplies a first moment at exponential scale, not the planted number
of alternatives, a two-solution rare-event probability, or the constants
4 and 2.

## Why an annealed first moment cannot supply the claimed constants

The following identities are elementary comparisons derived here. Let U
be the uniform labeled simple cubic graph on 2N vertices. Let K(G) count
unordered perfect-matching-cut bipartitions. Write g_r(m) for the number
of labeled simple r-regular graphs on m vertices. Counting graph/partition
pairs gives the exact finite identity

`E_U K = [binom(2N,N)/2] g_2(N)^2 N! / g_3(2N)`.

With a uniformly hidden planted partition and the RSBM sampling law, the
observed graph distribution is exactly K-size-biased relative to U:

`P_planted(G) = [K(G)/E_U K] P_U(G)`.

Consequently

`P_planted(K>=2) = E_U[K 1_{K>=2}] / E_U K`,

`R_N = 1 - P_U(K>=1)/(E_U K)`.

The second identity follows from the uniform posterior over the K valid
partitions. It is not a special property of the Ising saddle point.

Thus Bayes error `2/N^2` asks for a relative second-order refinement

`P_U(K>=1) / E_U K = 1 - 2/N^2 + o(N^-2)`.

An exponential-scale annealed mean does not provide this. A primary
enumeration of cubic graphs admitting a perfect matching cut to this
relative precision, or an equivalent planted factorial-moment result,
would be directly relevant prior art. No inspected source supplies it.
Similarly, ordinary 2-factor counts do not distinguish whether the
complementary matching is an entire cut.

## Defensible novelty boundary

The cubic partition object, its cover interpretation, natural-isomorphism
formulas, and finite enumeration of alternative two-cycle decompositions
all predate this session. Annealed fixed-energy counting also predates it.
The candidate narrower advance is the **sharp labeled planted rare-event
coefficient**, including exclusion of larger alternatives and the
posterior conversion to Bayes error. Among the primary sources inspected
here, none states the `4/N^2` and `2/N^2` formulas or the general coefficient
under the exact uniform-simple RSBM law. This supports describing the
formula as a derived sharp refinement whose historical priority remains
unverified; it does not justify a firstness or field-scale claim.

Searches covered exact phrases for perfect matching cuts, their counting,
uniqueness and probabilities; cycle-permutation representations and
natural/unnatural isomorphisms; cubic 2-factor decompositions; and
ferromagnetic blocked-state counts. Generic recovery thresholds were not
used as substitutes for a formula comparison.

Local source copies and selected page renders are retained in `sources/`.
The 1998 definition/theorem/table and the current 2026 Table 4 were
visually checked. Coverage is confined to the statements, definitions,
equations and sections cited above; it is not a claim to have verified
every proof in all source papers.
