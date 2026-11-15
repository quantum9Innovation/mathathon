# Independent audit of bipartite mixed phases and zero-target transfer

Prepared 2026-11-15 by the finite-field/forms worker. Read in full: `mixed-phases.md`, `zero-target-transfer.md`, and the frozen bounded-moment theorem to check the exact induction class used. This is a mathematical cross-audit, not a priority assessment.

**Verdict: PASS.** The mixed-phase coefficients, zero-target moment, narrow-neighborhood assembly and subsequent spectral transfer are correct. The separately proved full-uniform coefficients in `bipartite-lattice-forms.md` supply the remaining stated input.

## Even irreducibles and all proper mixed subspaces

For an even irreducible target of degree 2s, the field K=F_p[lambda^2] has size p^s and E=F_p[lambda] has K-dimension two. The inclusions lambda H_L subset H_R and lambda H_R subset H_L imply equal dimensions because lambda is invertible, hence H_R=lambda H_L and lambda^2 H_L=H_L. Thus H_L is a K-subspace, and its only proper nonzero possibility is a K-line. There are p^s+1 such lines. No additional unequal-dimension or non-K-linear mixed phase is omitted.

For H_L=uK, coordinates xu on the left and y lambda u on the right give maps I,C, with C multiplication by c=lambda^2. A complementary K-line H_L' gives H_R'=lambda H_L'; these are compatible direct complements on both sides. Both pairs carry the same maps I,C. Therefore the full equation operator splits as two identical restricted operators for the base and for every lift, without any base or lift semisimplicity assumption. In particular h=2h_H.

The complement is an actual linear section commuting with the two local maps. Every quotient old point map consequently has an exact old-base lift in that complement, and its fiber-constant pullback solves every lift. This removes the affine forcing by an exact translation; it does not merely assert that quotient representatives can be chosen consistently. The p^h_H quotient point maps and the h=2h_H count are correct.

## Restricted mixed prefactor

The I,C congruence dependency calculation is consistent with the row/column conventions. Interaction slopes are M on one side and -M^T on the other. The I root condition makes M skew. The C root condition makes CM skew, equivalently CM=MC^T. Since the action of c on K is cyclic, the alternating form is zero. The remaining constant dependencies are the Frobenius adjoint of the square restricted old operator, so their dimension is h_H.

The local maximal-lattice index p^(k Q s), the compatible rank k Q s-h_H and the Gaussian compatible fraction retain all finite periods. The explicit integer free-margin/free-interior parameterization makes reduction onto the field-compatible space surjective. The resulting restricted uniform coefficient p^h_H is therefore exact. Its translation to the affine phases is a literal relabeling by the exact complement old solution, so no lift-size residue obstruction remains.

These conclusions independently agree with Section 7 of `bipartite-lattice-forms.md` and with direct compatible-rank checks.

## Why the narrower neighborhoods are essential and sufficient

Both assembly files explicitly restrict a mixed phase to small outside-coset root mass **and** edge laws close to its particular uniform-coset edge law. For zero outside mass, translation gives exactly the full-uniform neighborhood of the restricted problem. It would be incorrect to use its entire restricted moment as the leading coefficient, because that would also include restricted point or proper-subspace phases. The files avoid this overcounting.

For positive outside mass, the narrow neighborhood is a subset of the broad root-coset neighborhood. The weighted sparse estimate therefore bounds its leakage by O(n^(-(d-2))) times the complete smaller-dimensional homogeneous moment. That moment is bounded by the frozen two-space theorem: the I,C class has equal s-dimensional sides and the one-sided zero case has dimensions 1,0. The map restrictions are exactly within that theorem's class. Consequently the leakage is o(1) without assuming independence between defects and the bulk solution count.

The number of centers is finite for each fixed field/base. Their edge laws distinguish them: at a zero phase every edge law is the product of its endpoint uniform-coset root laws, and these root laws determine the cosets/subspaces. Thus neighborhoods can be chosen pairwise disjoint and disjoint from point and original full-uniform phases. Their complement contains no entropy zero and is compact, giving the stated exponentially small remainder via exact counting and uniform Stirling estimates.

For each K-line pair, the p^h_H quotient maps each have central contribution p^h_H, for total p^h. Across p^s+1 pairs this yields (p^s+1)p^h. Together with point p^h and original uniform p^(h+s), the complete even-target coefficient is exactly 2(p^s+1)p^h.

## Zero target and singleton-side lattices

For B=[[0,T],[T^T,0]], T is square because a positive-degree regular bipartite base has equal part sizes. Put s0=nullity(T)=nullity(T^T), h=2s0. The four subspace pairs are all possibilities in the scalar alphabet. The two mixed families have p^s0 centers each.

For the left-uniform/right-point family, the right point a_R lies in ker T. Its fiber-constant lift satisfies X J a_R=J T a_R=0 at every lift size. Hence the remaining left labels solve exactly X^T z_L=0; translation is exact, without an affine congruence assumption.

In that restricted system the left alphabet is F_p and the right is the singleton zero space. There is one independent legal neighbor-sum period at each right old vertex, so the full legal index is p^m. Compatible integer tables are freely parameterized by zero-total left root margins. Their first label moments give an arbitrary vector w in F_p^m; the compatible congruence map is T^T w. Its rank m-s0 therefore gives exact coefficient p^s0. This matches the separate direct calculation in the forms note. The singleton-side covariance and absent interaction modes are handled by the frozen unequal-alphabet Gaussian proof, so no unexamined flat mode or power of n remains.

Both affine lattice hulls contain the zero compatible star at every n, and translation by a_R is exact. Thus p dividing n or d changes none of these indices or coefficients. Each mixed family contributes p^h; with the point and full uniform terms the complete zero moment is (p+3)p^h+o(1).

## Even nullity, Markov and rational transfer

The identity nullity([[0,X],[X^T,0]])=2 nullity(X) holds over every field because X is square. The same applies to the base T. Thus a lifted zero-kernel dimension above its injected old baseline increases by at least two, not merely one. Subtracting p^h before Markov gives exactly (p+2)/(p^2-1). This is the necessary improvement that makes the zero coefficient useful.

The deterministic rational-to-modular transfer never required nonbipartiteness. It transfers the nullity of integer f(A), uses squarefree good-prime factors and kernel CRT, and compares with the old module embedded by repeated coordinates. This is valid when p divides n and when the full lifted matrix is nonsemisimple modulo p. A zero factor uses the even-nullity threshold; a nonzero factor uses its irreducible-degree dimension increment.

The nonzero Markov constants and zero bound are all at most 2/(p-1) for p>=3. The fixed-prime lift-size limsup precedes passage through arbitrarily large good primes. Thus the aggregate old-factor union bound tends to zero, with no growing-prime uniformity assumption.

No mathematical gap remains in the two audited files. The claim stays within fixed connected simple regular bases of degree at least three, and historical novelty remains unasserted.
