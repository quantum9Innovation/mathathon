# Adaptive cross matching: a valid ambiguity construction for (3,1)

Independent construction check, 2026-11-15.

**Verdict: the construction is correct.** It concerns an adaptive cross
matching chosen after seeing the internal graphs. It is therefore outside
the prescribed/independent-cross-graph model of
`partitioning-rsbm-kernel-session/rsbm-kernel-even-blocks.tex`.

## Deterministic lemma

Let C and D be simple cubic graphs on disjoint labelled vertex sets P,M,
each of size N. Suppose X subset P and Y subset M are induced cycles of
the same length ell. Suppose the third neighbours of the vertices of X
are all distinct and lie outside X; let their set be U. Make the same
assumption for Y, with third-neighbour set V outside Y. Thus

    |X|=|U|=|Y|=|V|=ell,
    X cap U = Y cap V = empty,
    N >= 2ell.

Choose a cross perfect matching B consisting of arbitrary bijections

    X <-> V,
    U <-> Y,
    P minus (X union U) <-> M minus (Y union V).

The original blocks P,M give every vertex three same-block neighbours
and one opposite-block neighbour. Define new blocks by flipping X and Y:

    P' = (P minus X) union Y,
    M' = (M minus Y) union X.

Then P',M' also form a balanced (3,1) partition.

**Proof.** Balance follows from |X|=|Y|. A vertex of X retains its two
cycle neighbours as same-block neighbours. Its third C-neighbour in U
becomes opposite-block, while its matching neighbour in V becomes
same-block. A vertex of U has exactly one C-neighbour in X: distinctness
of the third neighbours guarantees this exact count. That neighbour
becomes opposite-block, while the matching neighbour in Y becomes
same-block. The same argument applies to Y and V with roles reversed.
A vertex in either remainder has no internal neighbour in X or Y,
respectively, and its cross partner remains in the opposite remainder.
All its neighbour statuses stay fixed. Thus every vertex still has
three same-block neighbours and one opposite-block neighbour.

The two partitions are different modulo complementation: a vertex in X
flips, while a vertex in U does not, and both sets are nonempty.

Let sigma=1_P-1_M and sigma'=1_P'-1_M'. For the full adjacency matrix A,

    A sigma=2 sigma,     A sigma'=2 sigma'.

Consequently nullity_R(A-2I)>=2. Equivalently the additional eigenvector

    tau=1_X-1_Y = (sigma-sigma')/2

satisfies A tau=2 tau. This can also be checked directly: a vertex in X
sees two +1 values, a vertex in Y sees two -1 values, and values cancel
at U and V. The remaining vertices see zero.

No relation between the two cycle orderings is needed: the three cross
bijections can be arbitrary. The essential clean-cycle condition is
that every outside neighbour has exactly one neighbour on the cycle.

## Explicit twelve-vertex witness

Take N=6 and ell=3. Both C and D are triangular prisms:

    X={0,1,2}, U={3,4,5},
    Y={6,7,8}, V={9,10,11}.

The internal edges are the four triangles on X,U,Y,V together with

    0-3, 1-4, 2-5, 6-9, 7-10, 8-11.

The adaptive cross matching is

    0-9, 1-10, 2-11, 3-6, 4-7, 5-8.

The original plus block is {0,...,5}; the new plus block is {3,...,8}.
Both induce triangular prisms internally and have cross degree one.
Their sign vectors are orthogonal: exactly six of the twelve vertices
flip. The graph is the Cartesian product K_3 square C_4, is simple and
four-regular, and has exact adjacency spectrum

    4 (multiplicity1),
    2 (multiplicity2),
    1 (multiplicity2),
    0 (multiplicity1),
   -1 (multiplicity4),
   -3 (multiplicity2).

In particular the planted eigenvalue 2 has multiplicity exactly two.
The spectrum follows by adding the spectra {2,-1,-1} of K_3 and
{2,0,0,-2} of C_4. The accompanying `adaptive_witness.py` reconstructs the
adjacency, checks both partitions, computes rational nullity, and verifies
the characteristic polynomial using exact integer traces and Newton's
identities.

## Probability quantifiers and scope

If independent random internal graphs C_N,D_N contain such clean cycles
of a common length with probability 1-o(1), choose the cycles and their
cross bijections deterministically from the labelled graphs whenever
possible (and use any perfect matching otherwise). This defines an
adaptive cross-matching rule B_N(C_N,D_N) under which

    P(nullity_R(A-2I)>=2) -> 1.

The clean-cycle probability is a separate input, not proved in this note.

There is no contradiction with

    sup over deterministic B_N  P_{C_N,D_N}(failure with B_N) -> 0.

That statement does not permit moving the supremum inside the
probability. The adaptive countermodel concerns P(exists B causing
failure), with B depending on the random internal graphs. Likewise,
adjoining a common **independent** B-distribution preserves contiguity;
an adaptive kernel B(C,D) need not preserve it.

## Uniform marginal and even pairwise independence do not repair the model

The adaptive countermodel can preserve the usual marginal law of every
factor. In fact it can make C,D,B pairwise independent while retaining
the dependence of B on the pair (C,D).

Let F(C,D) be any deterministic adaptive matching rule, with an arbitrary
fallback when the clean-cycle event fails. Start with independent uniform
simple cubic C,D. Independently sample uniform permutations pi,rho of
their respective N-element blocks. Set

    C' = pi C pi^{-1},   D' = rho D rho^{-1},
    m' = F(C',D'),
    m  = rho^{-1} m' pi.

Relabelling invariance implies that the pair (C',D') is independent of
(pi,rho). Therefore m' is independent of the two permutations, and m is
a uniform bijection between the two original blocks. For each fixed m'
and candidate m there are exactly N! pairs (pi,rho) with
rho^{-1}m'pi=m, out of (N!)^2 possibilities.

There is a stronger conditional argument. Given C,pi,D', the matching
m'=F(pi C pi^{-1},D') is fixed and rho is still uniform: D' is independent
of rho, and the original C and pi are independent of both. Hence m is
uniform conditional on C, so B is independent of C. By conditioning on
D,rho,C' instead, B is also independent of D. C and D were independent
at the start. Thus all three factors are pairwise independent and have
their standard uniform marginals.

Finally, the graph (C,D,m) is isomorphic, via pi on one block and rho on
the other, to (C',D',F(C',D')). The additional-partition event is invariant
under this relabelling. Any 1-o(1) adaptive failure probability therefore
survives the symmetrization unchanged.

This is a joint-dependence countermodel, not the independent RSBM: the
cross matching is not independent of the **pair** of internal graphs.
The prescribed/independent-B theorem is unaffected. Statements of model
assumptions must retain that joint independence, rather than just listing
three uniform marginals or pairwise independences.

The existence of a second admissible partition establishes deterministic
ambiguity from the degree constraints and failure of eigenvalue
simplicity. By itself it does not prove a statistical impossibility
theorem for every possible adaptive generative law: such a claim would
need a separate comparison of the probabilities of the two latent
partitions.
