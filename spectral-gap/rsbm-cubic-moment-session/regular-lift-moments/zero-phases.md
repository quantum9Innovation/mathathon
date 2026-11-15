# Zero phases and their interior Hessians for regular lifts

Prepared 2026-11-15. Direct finite-group and entropy calculations. No external theorem is used. This note classifies every zero of the all-slot entropy exponent for a fixed connected simple regular base, and proves a quantitative positive Hessian within each phase's support. It does **not** infer a bounded moment merely from the entropy inequality.

## Model and normalization

Let `B` be a fixed connected simple `d`-regular base, `d>=3`, with vertex set `{1,...,k}`. Consider its independent uniform `N`-lift. Fix the alphabet `V=Fp^r`, with row-vector action by an arbitrary matrix `R`. Candidate intertwiners obey `AY=YR`.

At base vertex `i`, a legal ordered star has root `X_i in V` and one neighbor label `Z_ij in V` for each `j~i`, with

`sum_(j~i) Z_ij = X_i R`.                                  (1)

Let its law be `P_i`, root law `mu_i`, and edge pair law `nu_ij=law(X_i,Z_ij)`. Feasibility requires `nu_ij(x,z)=nu_ji(z,x)`. Normalize the exponent per lift-fiber size `N`:

`Phi(P)=sum_i H(P_i)-sum_(edges ij) H(nu_ij)`.

There are no repeated neighbor-type slots in a simple base, so no slot symmetrization loss is needed. The already audited all-slot identity reads

`Phi=-(d-2)/d sum_(edges ij) I_nuij(X_i;Z_ij)`

`    -(1/d) sum_i sum_(t~i) J_it`,                           (2)

where `J_it` is the conditional total correlation of all neighbor slots except `t`, given the root. Every term on the right is nonnegative.

## A finite-group lemma

Let `Z_1,...,Z_d` take values in a finite vector space, and suppose their sum is a fixed `s`. Suppose every `d-1` of them are mutually independent, with fixed one-coordinate marginals `mu_1,...,mu_d`. If `d>=3`, then all `mu_j` are uniform on cosets of one common linear subspace `H`.

Proof: define `H_j` to be the span of all differences of points in the support of `mu_j`. Fix distinct indices `j,t` and condition all other `d-2` variables to values in their supports. The conditioning event has positive probability by the retained-product assumption. The conditional marginals of `Z_j,Z_t` remain `mu_j,mu_t`, and they obey `Z_j+Z_t=c`. Thus `mu_t(z)=mu_j(c-z)` and `H_j=H_t`. All these subspaces are therefore one common `H`.

There is at least one conditioned variable, since `d>=3`. Varying its value within its support changes `c` by all generators of `H`. The same reflection identity shows that `mu_t` is invariant under every translation in `H`. Its support is contained in a single coset of `H` by the definition of its difference space. Translation invariance then makes it uniform on that entire coset. This holds for every `t`.

Conversely, given cosets `a_j+H`, the uniform law on `sum Z_j=s` has all retained `d-1` marginals equal to their product exactly when `s-sum_j a_j in H`.

## Complete zero-phase classification

At equality in (2), every edge root and neighbor are independent. For each `i` and each root value `x` in its support, all retained `d-1` neighbor labels are independent with marginals `mu_j`, independent of `x`. Apply the lemma conditionally on this root value. Every neighbor law is uniform on a coset of one common subspace. Since every base vertex has a neighbor, it follows that

`mu_i = Uniform(a_i+H_i)`

for some subspace `H_i<=V` and coset representative `a_i`. At each base vertex `i`, all the subspaces `H_j` with `j~i` coincide; denote this common neighbor subspace by `K_i`.

The exact remaining requirements are

`H_i R subseteq K_i`,

`a_i R - sum_(j~i) a_j in K_i`.                            (3)

Indeed the root image `xR` must lie in `sum_j a_j+K_i` for every `x in a_i+H_i`, which is equivalent to (3).

For every such collection, the star law is uniquely determined:

* choose `X_i` uniformly on `a_i+H_i`;
* given the root, choose any `d-1` neighbor labels independently and uniformly on their cosets;
* obtain the omitted neighbor from (1).

The result does not depend on the omitted slot: it is uniform on the affine legal-star support. Every retained neighbor tuple has the required product law, every edge law is `mu_i x mu_j`, and (2) vanishes. This proves both necessity and sufficiency, including uniqueness of the star laws after their cosets have been fixed.

Changing representatives `a_i` within their cosets preserves (3), since `H_iR subseteq K_i` and each neighbor subspace equals `K_i`.

### Connected nonbipartite base

The relation “joined by an even-length walk” has a single class. Therefore every `H_i` is one common `H`, and (3) becomes

`HR subseteq H`,

`a_i R = sum_(j~i) a_j mod H`.                             (4)

Thus phases are exactly an `R`-invariant subspace `H` and an old-base intertwiner with values in the quotient module `V/H`. There are finitely many for each fixed `p,r,k,R`.

The point phases are `H=0`: ordinary base intertwiners. The full uniform phase is `H=V`. Intermediate invariant subspaces give additional genuine phases for vector labels; they cannot be omitted from a matrix-valued moment argument.

### Connected bipartite base

Let the bipartition be `L,Rbase`. Even walks have exactly these two classes. There can be two subspaces, `H_L,H_R`, with

`H_L R subseteq H_R`, `H_R R subseteq H_L`.

At a left vertex the coset equation is taken modulo `H_R`; at a right vertex it is taken modulo `H_L`. These data again classify every zero phase. Unequal subspaces are a genuine extra possibility; for example a zero matrix `R` permits it whenever the corresponding coset equations hold.

A crude finite bound is `(r+1)^2 p^(2r^2+rk)` phases: count subspaces by spanning matrices and then count all coset choices. This is only a count of phase centers, not a moment estimate.

## Scalar special cases and `K4`

For `r=1`, the only subspaces are `0` and `Fp`.

On any connected nonbipartite base, the zero phases are precisely the full uniform phase and the point phases `a` satisfying

`B a = lambda a` over `Fp`.

For a connected bipartite base and `lambda!=0`, the two inclusions force the same subspace on both sides, giving this same description. For `lambda=0`, mixed phases can occur: one side's root laws uniform and the other's point masses, with the appropriate opposite-side sum equations. These are additional finite phases, not a continuum or a Hessian degeneracy.

For `K4`, `B=J_4-I_4`. For odd `p`, the number of scalar zero phases is

* `1+p` if `lambda=3`;
* `1+p^3` if `lambda=-1`;
* `2` otherwise (the uniform phase and the all-zero point phase).

The first two cases are disjoint for odd `p`. At `p=2`, the values `3,-1` coincide: for `lambda=1` the point space is `sum_i a_i=0`, of dimension three; for `lambda=0` only the zero point remains.

## Quantitative Hessian on each fixed support

Fix any phase just classified. Let `P_i^0` be its uniform legal-star law and perturb only inside this same support:

`P_i=P_i^0(1+g_i)`, `E_0 g_i=0`.

All norms below are `L2(P_i^0)` norms or their uniform marginal norms. Different supports and dimensions cause no problem: conditional on the root, every retained `d-1` tuple is a product of uniform coset laws. In particular any two distinct neighbors are independent, and each neighbor is independent of the root.

Let

`f_i(X_i)=E_0(g_i|X_i)`,

`h_ij(X_i,Z_ij)=E_0(g_i|X_i,Z_ij)`,

`e_ij=h_ij-f_i-f_j`.

Feasibility identifies the two orientations of the edge perturbation, so `e_ji` is `e_ij` with coordinates reversed and has the same norm. Each `e_ij` has zero conditional mean on either one of its coordinates. For an omitted slot `t`, put

`k_it=g_i-f_i-sum_(j~i,j!=t)(h_ij-f_i)`.

This is the interaction residual for the retained product tuple. It is orthogonal to every function of `(X_i,Z_ij)` for retained `j`, and to every function of the root. Standard entropy Taylor expansion, or direct expansion of `(1+u)log(1+u)`, gives the exact quadratic loss

`Q := -Phi_2 = (d-2)/(2d) sum_(edges ij)||e_ij||^2`

`                  +1/(2d) sum_(i,t)||k_it||^2`.             (5)

Here is an explicit nondegeneracy estimate with no dependence on `p,r,k,R` or the chosen phase. Write

`E=sum_edges||e_ij||^2`, `K=sum_(i,t)||k_it||^2`,

`F=sum_i||f_i||^2`, `S=sum_i||g_i||^2`.

For each omission, decompose

`g_i=f_i+sum_(j!=t)f_j + r_it`,

`r_it=sum_(j!=t)e_ij+k_it`.

All terms within the expanded decomposition are orthogonal. Comparing omissions `t,u` gives

`f_t(Z_it)-f_u(Z_iu)=r_it-r_iu`.

The two variables on the left are independent, with mean-zero functions. Summing the squared-norm inequality over unordered `t,u` yields

`sum_(j~i)||f_j||^2 <=2 sum_t||r_it||^2`

`  =2[(d-1)sum_(j~i)||e_ij||^2+sum_t||k_it||^2]`.

Summing over the regular base gives

`dF <=4(d-1)E+2K`.                                        (6)

The orthogonal decomposition, averaged over omitted slots and summed over vertices, also gives the identity

`S=dF+2(d-1)E/d+K/d`.

Combine it with (6):

`S <=(2+1/d)[2(d-1)E+K]`.

Comparing with (5) proves

`Q >= c_d S`,

`c_d=(d-2)/[4(2d+1)(d-1)] >0`.                            (7)

Thus there are **no nonzero Hessian-null directions within any fixed phase support**, even for singular `R`, bipartite mixed phases, or characteristics dividing `d`. For `d=3`, the explicit constant is `1/56`.

This also gives a true neighborhood bound. Every relative edge perturbation is a conditional expectation of a star perturbation. Hence the sum of squared relative norms over all star and edge laws is at most `(1+d/2)S`, and their relative suprema are at most `max_i||g_i||_infinity`. Taylor's remainder is bounded by

`delta/[6(1-delta)^2] * (1+d/2)S`.

Choose, for example, `delta_d=min{1/4,c_d/[10(d+2)]}`. Then

`Phi(P) <= -(c_d/2) sum_i||g_i||^2`

whenever `max_i||g_i||_infinity<=delta_d` and the supports remain fixed. This is uniform in the field, vector dimension and phase.

## Remaining issue before a bounded moment

For a full-support phase, the neighborhood coercivity directly removes entropy tails and permits a local Gaussian/lattice calculation. For a proper-coset phase, (7) controls perturbations **inside** its support. It does not control small positive mass outside that support, where Shannon entropy has a boundary singularity and the appropriate integer tables change support.

Thus the finite phase classification and positive interior Hessians reduce, but do not finish, the bounded-moment problem. One still needs the exact prefactors/lattices at each phase and a rigorous estimate for neighborhoods that leak outside proper affine supports. No bounded expectation, shifted nonsingularity, new-spectrum exclusion or recovery theorem is claimed from this note alone.

## Appendix: two vector spaces and arbitrary vertex maps on a bipartite base

This appendix supplies a class closed under the proper-phase induction needed for bipartite bases. Let the fixed connected simple `d`-regular base have bipartition `L,Rbase`. Put

`V_L=Fp^(r_L)`, `V_R=Fp^(r_R)`,

allowing either dimension to be zero. For every base vertex `i`, fix an arbitrary linear map

`T_i: V_L -> V_R` if `i in L`,

`T_i: V_R -> V_L` if `i in Rbase`.

The maps may vary with `i`. A lift vertex over `i` carries a variable in its side's vector space. Its equation is

`sum_(j~i) Z_ij = T_i X_i`,                                (9)

an equality in the opposite side's vector space. In particular the root and neighbor alphabets need not have the same size. The original setting is recovered by `V_L=V_R=V` and every `T_i=R`.

For feasible star and edge laws define `Phi` as before. The all-slot entropy proof is unchanged: the omitted neighbor is determined with coefficient one, edge entropy is `H(mu_i)+H(mu_j)-I_ij` even when its two alphabets differ, and regularity cancels the root entropy terms. Thus (2) holds exactly in this class as well.

### Complete classification in the two-space class

Every zero phase is specified by subspaces

`H_L<=V_L`, `H_R<=V_R`,

and cosets `a_i+H_L` for left vertices, `a_i+H_R` for right vertices, satisfying **all** of the following:

`T_i H_L subseteq H_R` for each left `i`,

`T_i H_R subseteq H_L` for each right `i`,

`T_i a_i-sum_(j~i)a_j in H_R` for each left `i`,

`T_i a_i-sum_(j~i)a_j in H_L` for each right `i`.             (10)

The root laws are uniform on these cosets, and each star law is uniform on its entire legal affine support. There are no other zero phases.

Proof: at zero entropy, condition on the root. The neighbor variables all lie in the *same* opposite-side vector space, so the finite-group lemma applies without alteration. Consequently each root law, viewed as a neighbor law at another vertex, is uniform on a coset of a subspace. At every base vertex its neighbors' subspaces coincide. Connectivity by even walks makes the common subspace `H_L` on the left and `H_R` on the right. Requiring (9) for every root value gives exactly (10). Conversely (10) permits a uniform root and `d-1` independent uniform neighbor labels with the omitted neighbor determined; this produces feasible product edge laws and zero conditional total correlations. It is the unique compatible zero-entropy star law for the specified cosets.

Zero-dimensional vector spaces cause no exception: their only law and subspace are the point mass and zero space. Any remaining nontrivial root law is still seen among the neighbors of an opposite-side vertex, so the same lemma forces it to be uniform on a coset.

The number of phases is finite, with the crude upper bound

`(r_L+1)(r_R+1) p^[r_L^2+r_R^2+|L|r_L+|Rbase|r_R]`.

Representatives of a coset give the same phase. The inclusions in (10) ensure that the coset conditions are well-defined after changing representatives.

### Interior Hessian and dimensional closure

At a fixed phase, the local support has cardinality

`|H_L| |H_R|^(d-1)` for a left root,

`|H_R| |H_L|^(d-1)` for a right root.

It is uniform under the root plus any retained `d-1` neighbor coordinates. Thus every projection, orthogonality argument, omission comparison and entropy Taylor estimate in (5)--(7) remains valid. In particular

`-Phi_2 >= c_d sum_i||g_i||^2`,

with the **same** `c_d=(d-2)/[4(2d+1)(d-1)]`, independent of both alphabet dimensions and all maps `T_i`. Full relative neighborhoods inside the fixed support have the same true quadratic entropy bound.

A phase is proper when `(H_L,H_R)!=(V_L,V_R)`. Its homogeneous restricted problem has variable spaces `H_L,H_R` and maps

`T_i|_(H_L):H_L -> H_R`,

`T_i|_(H_R):H_R -> H_L`.

These are well-defined by (10), and the total dimension strictly decreases:

`dim H_L+dim H_R < r_L+r_R`.

The class is therefore closed under homogeneous proper-phase restriction, including vertex-dependent maps and zero-dimensional sides. The unique dimension-zero system has exactly one assignment.

Subtracting the coset representatives from a solution introduces fixed affine terms

`sum_(j~i) h_j = T_i h_i + b_i`,

`b_i=T_i a_i-sum_(j~i)a_j` in the opposite subspace.

The representatives need not be exact base solutions. For each fixed lift, this affine fiber is either empty or a translate of the homogeneous restricted kernel. Its size is therefore at most that homogeneous kernel size. This explains precisely why the same smaller-dimensional homogeneous class suffices for the induction; no unproved lifting of quotient cosets to exact point maps is required.

This appendix proves phase classification, finite phase count, interior nondegeneracy and closure of the class under restriction. The separate central prefactor and sparse-boundary estimates are still the inputs that turn this structure into a bounded-moment theorem.
