# Mixed bipartite phases for an even irreducible target

Prepared 2026-11-15. This is a direct algebraic and lattice calculation. It proves the mixed-phase classification, exact quotient lifting and the mixed uniform prefactors requested in `regular-lift-bipartite-old-new-root.txt`. The full-uniform coefficient of the original even irreducible representation is a separate input; it is not inferred here from entropy.

Throughout, the base is fixed, connected, simple, bipartite and `d`-regular, `d>=3`, with `m` vertices in each part. Its adjacency is `B=[[0,T],[T^T,0]]`. The prime `p` is odd. Every limit fixes the base and field and allows every positive lift size `N`.

## 1. Field model and all mixed zero phases

Let `g` be a monic even irreducible polynomial of degree `2s>=2`, and let the irreducible right action be multiplication by `lambda` on

`V=Fp[lambda] ~= F_(p^(2s))`.

Write `g(t)=f(t^2)`. Irreducibility of `g` forces `f` irreducible: a factorization of `f` would give one of `g` after substitution. Thus, for `c=lambda^2`,

`K=Fp[c] ~= F_(p^s)`.

The element `lambda` is not in `K`, since its degree over `Fp` is `2s`. Hence `V` is two-dimensional over `K`, `lambda` is invertible, and `c` is nonzero.

The established zero-phase classification gives subspaces `H_L,H_R<=V` with

`lambda H_L subseteq H_R`, `lambda H_R subseteq H_L`.

Invertibility and dimensions turn the first inclusion into `H_R=lambda H_L`, and give `c H_L=H_L`. Stability under `c`, hence under `Fp[c]=K`, makes `H_L` a `K`-subspace of `V`. Its only possible `K`-dimensions are zero, one and two.

The zero-dimensional pair is the point family. The two-dimensional pair is full uniformity. Every remaining pair is

`H_L=uK`, `H_R=lambda uK`                                 (1)

for a one-dimensional `K`-line. Their number is

`(p^(2s)-1)/(p^s-1)=p^s+1`.                              (2)

This is a classification of all mixed proper nonzero subspace pairs, not merely a supply of examples.

## 2. Restricted and quotient representations split compatibly

Fix the line (1). Coordinates `xu` on the left and `y lambda u` on the right turn multiplication by `lambda` into the two maps

`T_L=I:K->K`, `T_R=C:K->K`,                              (3)

where `C` is multiplication by `c=lambda^2`. The local equations are

`sum right-neighbor coordinates = left-root coordinate`,

`sum left-neighbor coordinates = c * right-root coordinate`.

Let `h_H` be the `Fp` dimension of their old-base solution space. The operator `C` is cyclic: the coordinates `1,c,...,c^(s-1)` form a basis of `K` over `Fp`.

Choose any different `K`-line `H_L'=u'K` as a complement, and put `H_R'=lambda H_L'`. Then

`V=H_L direct-sum H_L'` on the left,

`V=H_R direct-sum H_R'` on the right.

Multiplication by `lambda` maps each left summand into its corresponding right summand and each right summand back into the corresponding left summand, because `lambda^2=c in K`. Both restricted representations have exactly the maps (3). In particular, for **every lift**, its full equation operator splits as the direct sum of two identical restricted operators.

For the base this proves

`h := dim_Fp {Y:BY=Y R_g} = 2h_H`.                       (4)

The quotient by `(H_L,H_R)` is isomorphic to the complementary restriction, hence to (3). Its old-base solution space also has dimension `h_H`, so the number of quotient point maps is exactly

`p^h_H`.                                                (5)

No semisimplicity of the base is used here; the decomposition is an explicit direct sum of the actual operators.

### Exact lifts remove the potential affine residue problem

The complement defines a fixed linear section of the quotient, compatible with both local maps. Apply it to a quotient old-base solution. The result is an **exact** old-base solution `a_i` in the complementary summands, not just a family of representatives satisfying equations modulo `H_side`.

Its fiber-constant lift is exact in every `N`-lift. Thus, for every quotient point map, the entire zero-defect coset fiber is obtained by translating the homogeneous restricted problem (3). Arbitrary alternative representatives differ by an `H_side`-valued old assignment; their affine terms are removed by the same translation to the exact complement lift.

This is why the relevant affine uniform phases have no possible `N mod p` obstruction. The claim does **not** assert that an unrelated arbitrary affine forcing on the restricted system has the same coefficient for every `N`.

## 3. Exact uniform prefactor for the restricted maps `I,C`

Put `Q=|K|=p^s`, and retain the row-vector convention. Let the restricted root map be `I` at each left base vertex and `C` at each right base vertex.

The exact matching count, two uniform-star models and weighted Gaussian calculation from the central lift packet apply with these vertex-dependent maps. They depend only on the local condition that a root and any `d-1` neighbors determine the last neighbor. In particular:

* the independent-neighbor lattice has the same common-root-row constraints;
* the legal maximal lattice is the kernel of the `K`-valued sum congruence in every root-label row;
* its unrestricted index is `p^(k Q s)`, where `k=2m`;
* the two real covariances coincide, and the compatible weighted Gaussian has positive precision;
* the compatible integer lattice is parameterized by arbitrary zero-total root margins and arbitrary interior edge entries, so reduction modulo `p` is onto the full compatible direction space.

It remains to calculate the rank of the congruences **after compatibility**, rather than merely asserting boundedness.

### Dependency calculation with all transposes

Write a dependency coefficient at a root label `a` as a column `h_i(a)`. The 2-by-2 interaction transfers force

`h_i(a)=M_i a^T+k_i`, `M_j=-M_i^T` on every edge.

Connectivity gives one matrix `M` on the left and `-M^T` on the right. At a left vertex the root map is `I`, so the quadratic root coefficient is `-aM a^T`. Its vanishing in odd characteristic forces

`M^T=-M`.                                               (6)

At a right vertex the root map is `C`, and its matrix slope is `-M^T`. The quadratic coefficient is `+b C M^T b^T`; using (6), its vanishing says that `CM` is skew-symmetric, equivalently

`CM=MC^T`.                                              (7)

The alternating form `beta(a,b)=aM b^T` therefore makes the right action `C` self-adjoint. Since `C` is cyclic, the cyclic alternating-form lemma forces `M=0`, including for degenerate forms. There is no residual alternating dependency.

The remaining constant columns obey

`sum_(j~i) k_j = T_i k_i`,                               (8)

where `T_i=I` on the left and `T_i=C` on the right. With rows `k_i^T`, these are the Frobenius-adjoint old-base equations. The original restricted operator and its adjoint are square on the same `ks`-dimensional matrix space, so their kernel dimensions agree. Therefore (8) has dimension `h_H`.

This classifies every dependency, not just a subfamily: arbitrary dependency functions were forced affine-linear by the interaction transfers, and the independent root-margin directions gave exactly the quadratic and linear conditions above. Hence

`rho=k Q s-h_H`                                        (9)

is the rank of the compatible congruence map.

### Lattice fraction and exact normalization

The legal/independent relative local CLT ratio is the unrestricted index `p^(k Q s)`. On compatible tables, the legal sublattice has index `p^rho`. Their weighted Gaussian sums therefore have ratio `p^(-rho)`. The common matching weight has exact independent-model normalizer one, and its central window has mass `1-o(1)`. Thus the restricted full-uniform contribution is

`p^(k Q s-rho)+o(1)=p^h_H+o(1)`.                         (10)

All normalization constants, compatibility codimensions and finite periods are retained in this argument. The zero legal star is compatible at every `N`. Its translate by the exact old lift from Section 2 is also compatible at every `N`; the affine lattice translates are obtained by a literal relabeling. The Gaussian sublattice fraction is uniform in those translates. Hence (10) holds for the affine coset phases needed here, with no parity or `p|N` exception.

The fixed-neighborhood tails are removed by the same analytic weighted rate function and positive compatible Gaussian precision as in the central packet. Thus (10) is a genuine fixed-neighborhood prefactor, not an inference from entropy zero.

## 4. Turning the coefficient into a mixed-phase contribution

For a fixed subspace pair (1), there are `p^h_H` quotient old point maps, by (5). Each has a distinct uniform-coset zero phase. In a neighborhood of one such phase:

* the zero-defect assignments, after translating its exact old lift, have the restricted full-uniform contribution (10);
* assignments with a positive but sufficiently small number of outside-coset vertices have expected count `o(1)`, by the weighted sparse proposition and the already proved bounded smaller-dimensional moment.

The neighborhood must require both small outside-coset root mass and near-uniform **within-coset edge tables**. Taking the entire broad root-coset neighborhood would also include its point subphases and overcount their leading contribution. The exact uniform calculation applies to these narrower edge neighborhoods, and the sparse bound controls their leakage.

There are finitely many phase centers for fixed data, so choose these neighborhoods disjoint from each other, from the point phases and from original full uniformity. Their complement has a strict entropy gap. Consequently each fixed subspace pair contributes

`p^h_H * p^h_H +o(1)=p^h+o(1)`,                         (11)

using (4). Across all mixed pairs the contribution is

`(p^s+1)p^h+o(1)`.

If the separately computed original full-uniform coefficient is `p^(h+s)`, the point phases contribute `p^h`, and these mixed coefficients give the total

`[p^s+1+(p^s+1)]p^h+o(1)`

`=2(p^s+1)p^h+o(1)`.                                   (12)

This final assembly uses the exact central prefactors and sparse leakage control in addition to entropy classification.

## 5. The zero target `g=t`: one-sided mixed phases

For the scalar zero map, the two root subspaces can independently be `0` or `Fp`, giving four subspace pairs. Put

`s0=dim_Fp ker T=dim_Fp ker T^T`, `h=2s0`.

Consider `H_L=Fp,H_R=0`. The homogeneous restricted equations have free left labels `x`, zero right labels, and

`X^T x=0`

in a lift. Their old dimension is `s0`. The quotient problem is the opposite one-sided system `T y=0`, also with old dimension `s0`. Original zero-map equations split into these two one-sided problems, so every quotient point map lifts exactly by setting the other side to zero. There are `p^s0` quotient point maps.

### Exact one-sided uniform coefficient

Every compatible edge table is `p`-by-`1` or its transpose, determined by the root-label counts at its left endpoint. Only right old types have nontrivial legal congruences: their root alphabet has one point, and each supplies the scalar neighbor-sum congruence. The full independent-to-legal lattice index is therefore `p^m`.

In the compatible integer direction lattice, choose arbitrary zero-total root margins `u_i(a)` for left old vertices. Put

`z_i=sum_a a u_i(a)`.

Every `z_i in Fp` is available independently, using `u_i(1)=z_i,u_i(0)=-z_i`. The right congruences are exactly

`T^T z=0`.

Their rank is `m-s0`. The compatible legal index is `p^(m-s0)`, so the exact uniform coefficient is

`p^m / p^(m-s0)=p^s0`.                                  (13)

This again uses the relative LLT, its full index and the exact independent matching normalizer. The two-space central calculation covers alphabet sizes `p` and `1`; the remaining root-margin Gaussian has positive precision, and all absent interaction modes have dimension zero. The zero star supplies a compatible point at every `N`. Translation by each exact quotient old lift removes the affine terms, so there is no `N` residue restriction.

Thus this mixed pair contributes `p^s0 * p^s0=p^h`; the opposite pair contributes the same. Point phases contribute `p^h`. If the original full-uniform coefficient is `p^(h+1)`, the complete zero-target moment is therefore

`(p+3)p^h+o(1)`.                                        (14)

The same separated-neighborhood and sparse-leakage argument justifies the exact sum. Characteristics dividing the degree merely affect the actual value of `s0`; none of the calculation divides by the degree or by `N`.

Finally, every square bipartite matrix `[[0,X],[X^T,0]]` has nullity `2 nullity(X)` over any field, since its rank is `2 rank(X)`. Thus old and lifted zero-target nullities are even. This is the additional two-dimensional increment used by the zero-target probability estimate; it does not need semisimplicity modulo `p`.

## Verdict and scope

The mixed-phase claims in the candidate pass. The quotient/restriction isomorphism and exact sections are valid for every even irreducible nonzero target. They imply `h=2h_H` and eliminate affine-residue issues. The mixed uniform coefficient is `p^h_H` because the restricted maps `I,C` leave no alternating lattice dependency. The zero-target mixed coefficient is also exact.

The remaining inputs to the full bipartite spectral conclusion are the original full-uniform coefficients, the non-even irreducible case, and the already separated good-prime rational-to-modular transfer. None of those is inferred merely from the finite zero-phase classification here.
