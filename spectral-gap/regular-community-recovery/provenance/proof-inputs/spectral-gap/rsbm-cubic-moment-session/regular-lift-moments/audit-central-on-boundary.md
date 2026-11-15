# Independent audit of regular-lift boundary control and zero phases

Audit prepared 2026-11-15 by the central-prefactor worker. Files read: `sparse-lift-common-subspace.md` (including its two-space appendix) and `zero-phases.md` (including its vertex-dependent two-space appendix). This audit concerns their mathematical arguments, not novelty or literature priority.

**Verdict: PASS.** I found no unresolved mathematical gap in the finite phase classification, the weighted sparse-certificate estimate, or closure of the dimension induction. The central prefactor input is supplied separately by `central-lift-uniform.md`, including its unequal-alphabet appendix.

## Finite-group and entropy zero phases

The conditional finite-group lemma is correct. Fixing the other d-2 coordinates is a positive-probability conditioning because each retained d-1 set has product law. Each of the two remaining one-coordinate conditional marginals remains its original marginal, since the coordinate together with the conditioned d-2 coordinates is such a retained set. Their fixed-sum relation therefore identifies the two marginals by reflection and identifies their support-difference subspaces. Varying one of the conditioned coordinates supplies all translation generators of that common difference subspace. This gives the asserted uniform coset law; no unproved support-size or entropy equality theorem is needed.

At zero all-slot entropy, vanishing edge mutual information makes the neighbor marginals independent of the chosen root value, while each vanished conditional total correlation gives every retained d-1 product law conditional on that root. Thus applying the lemma conditionally is justified. Edge compatibility identifies each neighbor marginal with the root law at its old neighbor type.

The resulting constraints are precisely the map inclusions and quotient-coset equations stated in the notes. Neighbor difference subspaces coincide at every old vertex. Even-walk connectivity then leaves one subspace on a connected nonbipartite base and one per side on a connected bipartite base. This argument uses regularity only in the all-slot identity, not in the finite-group lemma.

The converse law is also valid and unique: root plus any retained d-1 neighbors give independent uniform coordinates on their specified cosets; the omitted value is determined. Its conditional marginal is uniform on the omitted coset, including the one-point case. Therefore every edge pair is a product and every retained tuple has the required law. The condition on representatives is exactly what keeps the omitted value in that coset.

The classification does include the mixed bipartite phases. The vertex-dependent two-space appendix correctly allows unequal subspaces and dimensions zero; it does not silently identify the two alphabets.

## Affine fibers require no lifting of quotient point maps

For a quotient-coset phase, the chosen old-type representatives need not solve the exact original equation. Subtraction is done in the quotient, where the coset condition does make the fiber-constant assignment an exact solution on every lift. Thus the quotient defect satisfies a homogeneous equation and its support is exactly the number of vertices outside the prescribed cosets.

For a fixed quotient defect assignment and a fixed graph, the original lifts are an affine solution set with the stated smaller-dimensional homogeneous kernel. This set is either empty or a translate of that kernel. Hence its cardinality is at most the homogeneous kernel size. This correctly proves the zero-defect estimate even when the representative affine system is inconsistent.

The same reasoning works for unequal spaces: left equations are projected modulo the right subspace and right equations modulo the left subspace. The map inclusions make the quotient maps and restricted homogeneous maps well-defined. Vertex-dependent maps remain vertex-dependent under restriction, which is why the enlarged theorem class closes.

## Certificate and switching coupling

For a quotient defect support S of size k, a zero vertex outside S cannot see exactly one nonzero defect: its equation lies in one opposite-side quotient vector space and would be a single nonzero vector equal to zero. This assertion needs neither injectivity of the on-site map nor any condition at nonzero vertices.

With e edges inside S and b=dk-2e boundary edges, the number ell of outside vertices is at most b/2. The full incident-edge certificate has E=dk-e edges and v=k+ell vertices, so E-v>=(d-2)k/2. Both the upper bounds E<=dk and v<=(1+d/2)k used in enumeration follow. A one-vertex defect is impossible because the lift of a simple base is loopless and every incident neighbor would see its single nonzero value.

The image-swap forcing map produces exactly the conditional uniform permutation. After t earlier pairs, every output with the next pair forced has exactly n-t preimages: choose the former preimage of its new target among unused domains and undo the swap. The no-swap choice is included. Earlier prescribed pairs cannot be altered because both the new domain and target were unused. Forcing independently in the independent base-edge permutations therefore gives the complete jointly conditional law, not just a marginal with the right prescribed edges.

One image swap changes only four vertex equations. In the common-subspace problem its rank perturbation is at most 4 dim(H). In the unequal-space problem it is at most 2 dim(H_L)+2 dim(H_R); the larger 4(r_L+r_R) bound used in the note is valid. Rank perturbation controls nullity for rectangular as well as square operators, so unequal dimensions introduce no exception. Summing over at most E swaps and taking expectation proves the conditional moment factor as stated. This is the step that handles correlation between sparse defects and bulk solution multiplicity.

## Uniform weighted enumeration

For k<=n/(2d), every prescribed edge-matching event has probability at most (2/n)^E. The support and outside-set choices are bounded by (hn)^(k+ell)/(k!ell!). The partial matching count used in the note follows from choosing 2E stubs among at most d(1+d/2)k and pairing them; discarding bad colors can only lower the actual count. Every valid certificate uses at most one prescribed edge per stub, so the forcing lemma applies to each retained term.

After multiplying by the conditional kernel bound, the extra p^(4sE) is at most p^(4rdk). The remaining exponent manipulation is exact:

    (4dk)^E n^(v-E)
      =(4d)^E (k/n)^(E-v) k^v
      <=(4d)^(dk) (k/n)^((d-2)k/2) k^(k+ell).

Summing k^ell/ell! and bounding k^k/k! each costs at most exp(k). There are at most dk possible E. Thus the explicit geometric support bound contains no hidden n-dependent factor. Its ratio estimate is valid for the displayed sufficiently small epsilon. Since k=1 is impossible, summation begins at two and gives n^(-(d-2)), exactly as claimed.

For the two-space problem quotient labels have at most p^(r_L+r_R) possibilities, and the same exponent and geometric sum apply. Constants may be uniform in the maps and phase centers because the parameters are fixed and all such choices are finite; in fact the displayed estimates already avoid most dependence on those choices.

## Induction and zero-dimensional sides

A proper common invariant subspace strictly lowers dimension. A proper bipartite pair lowers dim(H_L)+dim(H_R), even if one of the original spaces has dimension zero. The restricted system remains the same random-lift model with the same base and fixed on-site linear maps; the switching argument never replaces it by a different random graph law. Both dimensions zero give exactly one assignment. If only one is zero, the remaining equations and certificate argument still have their stated meanings, and the central calculation has the corresponding absent modes of dimension zero.

Consequently the full theorem can be organized by ordinary dimension on nonbipartite bases and total two-side dimension on bipartite bases. Finite phase count and compactness remove the residual entropy-negative region; each proper-phase neighborhood is bounded by a smaller-dimensional moment times 1+O(n^(-(d-2))). The full-support phase has a separate prefactor bound. No step in this induction requires inference of boundedness from entropy alone.

I also checked the optional interior Hessian calculation in `zero-phases.md`: the orthogonal decompositions, averaging over omissions, and the bound c_d=(d-2)/[4(2d+1)(d-1)] are consistent. The boundary proof does not need this estimate, but it is a valid additional check on degeneracy inside a fixed support.
