# Independent audit: irreducible assembly and rational-to-modular transfer

Prepared 2026-11-15 by the cyclic-lattice worker. Read in full: `module-transfer.md` and `irreducible-moment-assembly.md`. This record supplies an independent mathematical cross-audit; it makes no claim about historical priority.

**Verdict: PASS.** The now-proved cyclic uniform coefficient completes the exact irreducible moment, and the transfer from those moments to old/new spectral disjointness is valid. No condition p not dividing the lift size is needed. No lifted modular semisimplicity is needed.

## Exact moment assembly

An irreducible companion of degree r acts on an r-dimensional simple module, so its only invariant subspaces are zero and full. The nonbipartite zero-phase classification therefore leaves exactly the full uniform phase and the old point maps BX=XR. This is true in the row-action convention of the entropy proof, independently of a companion orientation.

The point-map count is exactly p^h_old. Every one embeds as a deterministic fiber-constant solution for every lift. The sparse estimate with H=0 gives its support neighborhood contribution 1+O(n^(-(d-2))). Distinct point maps differ throughout at least one whole fiber, so radii below n/2 make these neighborhoods disjoint. They can also be chosen disjoint from the full-uniform table neighborhood, since their root and edge laws have a fixed positive distance from uniform for the fixed alphabet.

The compact remainder contains no entropy zero. Uniform factorial bounds, including zero cells, and the polynomial type count make its contribution exponentially small. The exact uniform term proved in `cyclic-lattice.md` is p^h_old+o(1). Thus the assembled total is indeed 2p^h_old+o(1), with all n allowed. It is not merely a bounded moment and does not suppress any proper phase for the irreducible target.

## Hom spaces and modular dimensions

For a degree-r irreducible g and companion R, evaluation at a cyclic column v gives an isomorphism

    {Y:MY=YR} -> ker g(M).

The inverse sends R^j v to M^j w; the last basis relation is consistent precisely when g(M)w=0. This proof works for every M, including nonsemisimple matrices. The kernel is a vector space over F_p[t]/(g), so its F_p dimension is a multiple of r. Consequently the next possible dimension above the old baseline is h_old+r, exactly the gap used in shifted Markov.

The distinction between geometric module dimension and characteristic-polynomial exponent is handled correctly. The formula r times the algebraic exponent is used only for the fixed base at good primes. No such formula is used for A_n modulo p.

## One finite bad-prime set

For the fixed integer symmetric B, the product F of its distinct monic irreducible characteristic factors annihilates B exactly over the integers. Since F is squarefree in characteristic zero, Disc(F) is a nonzero integer. At any odd prime not dividing this discriminant, all reduced factors remain squarefree and pairwise coprime. The identity F(B)=0 then makes B modulo p a semisimple F_p[t]-module. Thus, if f occurs to old exponent t and f mod p=product g_j, its old g_j kernel dimension is deg(g_j)t.

This excludes only finitely many primes, independently of n. No irreducible reduction of f, positive-density splitting result, or n-dependent rank-minor choice is being assumed.

## Real collision to modular geometric excess

Over the rationals, the fiber-constant embedding J and fiber-sum map S satisfy AJ=JB, SA=BS and SJ=nI. Hence the old rational representation and ker S give the ordinary invariant old/new direct sum. The new characteristic polynomial is rational; in fact it is integral, since each fiber all-one vector is primitive and the old lattice extends to an integer basis.

A new real root of the irreducible old factor f forces f to divide the new rational characteristic polynomial. Real symmetry then gives dim_Q ker f(A_n)>=ell(t+1), with ell=deg f. Since f(A_n) is integer, modular rank cannot increase, so the same nullity lower bound holds modulo every prime.

At a good prime the squarefree factorization f mod p=product g_j gives

    ker f(A_n)=direct-sum_j ker g_j(A_n)

by polynomial Bezout/CRT, for arbitrary A_n modulo p. This is a kernel decomposition for a squarefree annihilator, not an assertion that the entire modular matrix is semisimple. The dimension lower bound exceeds the summed old baseline ell t, so at least one g_j kernel has excess geometric dimension, hence increases by at least deg(g_j).

This is precisely why transferring ker f(A_n), rather than merely transferring characteristic-polynomial divisibility, avoids a Jordan-block counterexample.

## Lift sizes divisible by p

The repeated-coordinate map J remains injective modulo every p, including p|n, and AJ=JB still holds. Therefore the old companion Hom space always injects into the lifted one. The Markov baseline p^h_old is deterministic at every n.

When p|n, an old/new modular direct sum need not exist; the notes do not use one. All excess events concern the full modular kernel above the injected old baseline. The rational splitting is used solely to interpret the original characteristic-zero new spectrum.

## Limits and probability bound

For each fixed good prime and each fixed factor g_j, the exact moment and deterministic baseline yield

    limsup_n P(excess g_j geometric module)
      <=1/(p^deg(g_j)-1).

A union bound over the at most ell reduced factors bounds a real f-collision by ell/(p-1). Only after taking the lift-size limsup are arbitrarily large fixed good primes allowed to tend to infinity. Thus no uniformity of the o(1) error in a growing prime is needed. A final union bound over the finitely many old rational factors gives complete old/new real spectral disjointness in the stated scope.

All uses of symmetry, semisimplicity, field extensions, lattice convention and quantifier order are consistent across the two files and the cyclic central proof. The stated scope remains connected simple nonbipartite regular bases of degree at least three; this audit does not assert the additional analysis needed for bipartite bases.
