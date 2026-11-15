# Induction-ready bound near a common invariant-subspace phase

Prepared 2026-11-15. This proposition is self-contained. It specializes
the more general family-of-spaces bound in `sparse-lift-pointmaps.md`
to a single proper invariant subspace, so its right side is exactly a
lower-dimensional instance of the original intertwiner moment.

## Proposition

Let `B` be a fixed simple `d`-regular base graph on `h` vertices, `d>=3`,
and let `G_N` be its random `N`-lift with independent uniform edge
matchings. Connectivity and nonbipartiteness are not needed for this
proposition. Fix `V=Fp^r`, a linear endomorphism `R`, and an invariant
subspace `H<V`, of dimension `s<r`.

Let `a_i+H`, one affine coset per base vertex, satisfy the quotient
intertwiner equation

```
a_i R -sum_(j~i) a_j in H,       for every i.              (1)
```

The representatives `a_i` need **not** satisfy the exact equation in
`V`. Define

```
Z_H(G)=#{h in H^V(G): Ah=h R|_H},
M_H(N)=E Z_H(G_N),
D_a(Y)=#{v: Y_v notin a_type(v)+H}.
```

There are constants `epsilon>0`, `C<infinity`, depending only on
`B,p,r`, such that for all sufficiently large `N`, uniformly in `H`,
`R`, and all cosets satisfying (1),

```
E #{Y: AY=YR, D_a(Y)=0} <= M_H(N),                         (2)

E #{Y: AY=YR, 0<D_a(Y)<=epsilon N}
       <= C N^(-(d-2)) M_H(N).                            (3)
```

Consequently, if `M_H(N)` is bounded by the induction hypothesis,
the entire neighborhood of this phase has bounded expected size and
its nonzero-defect contribution tends to zero.

There is no requirement on `N` modulo `p`, or on its parity.

## Quotient variables and affine fibers

Let `bar R` be the endomorphism induced on `V/H`. For a candidate
intertwiner set

```
q_v=Y_v mod H -a_type(v) mod H.
```

Condition (1) makes the fiber-constant quotient `a mod H` an exact
quotient intertwiner for every lift. Thus

```
Aq=q bar R,        |supp q|=D_a(Y).                        (4)
```

For any fixed quotient assignment `q`, choose arbitrary representatives
`f_v` in `V`. Every possible lift is `Y_v=a_type(v)+f_v+h_v` with
`h_v in H`. Its equations are an affine system with homogeneous
operator

```
L_(G,H): h -> Ah-h R|_H.
```

Every nonempty affine solution set has cardinality exactly
`Z_H(G)`. In particular the number of lifts of `q` is at most `Z_H(G)`.
For `q=0`, this proves (2) even when the affine equation is insoluble.

## Dense certificate for a nonzero quotient support

Let `S=supp q`, `|S|=k`. At a zero quotient vertex, the equation in (4)
is a sum of its nonzero quotient-neighbor values equal to zero. It
cannot have exactly one such neighbor.

Take all edges incident to `S` as a certificate, and let `e` be the
edges internal to `S`, `b=dk-2e` the boundary edges, and `ell` the outside
vertices. Then

```
ell<=b/2,
E=dk-e,
v=k+ell,
E-v>=(d-2)k/2,      E<=dk,      v<=(1+d/2)k.                (5)
```

This uses neither injectivity of `bar R` nor nonzero equations inside
the support.

## Forcing a certificate preserves uniform conditional law

Let `C` be a valid prescribed certificate with `E` matching edges.
Orient each base edge once, so its lift matching is a permutation.
Start with independent uniform permutations, and process the prescribed
pairs for each permutation in any deterministic order.

To force a new pair `u->v`, let `w` be the current preimage of `v`, and
swap the images of `u` and `w`. This uses at most one transposition.
It preserves every earlier prescribed pair: `u` is a previously unused
domain point and `v` is a previously unused target, so neither can
conflict with an earlier forced pair.

The output is exactly uniform conditional on the prescribed pairs.
Indeed, when `t` pairs have already been forced, every permissible
output permutation after the next forcing step has exactly `N-t`
preimages in the uniform prior set: choose the former preimage `w` of
the new target among the `N-t` unused domain points; the preimage
permutation is then uniquely determined by undoing the image swap.
This also includes the no-swap case `w=u`. Equal fiber sizes give
uniformity at each step. Performing this separately for independent
base-edge permutations gives the correct jointly conditional law.

At most `E` transpositions are used. One transposition replaces two
lift edges by two others and changes at most four vertex rows of
`L_(G,H)`. Every such row has `s` scalar coordinates, so its rank changes
by at most `4s`. Therefore, for every coupled pair `G,G^C`,

```
rank(L_(G^C,H)-L_(G,H))<=4sE,
Z_H(G^C)<=p^(4sE) Z_H(G).
```

Taking expectation under this explicit coupling gives

```
E[Z_H(G_N) | C occurs] <=p^(4sE) M_H(N).                   (6)
```

This step controls the correlation between rare sparse defects and
the number of possible assignments in the bulk. It does not assume
independence of these quantities.

## Weighted support enumeration

For `k<=N/(2d)`, the probability of a prescribed certificate is

```
P(C occurs)=prod_(base edges e) 1/(N)_(s_e) <=(2/N)^E,
```

since `s_e<=E<=dk<=N/2`. Choose the support and its `ell` outside
vertices in at most `(hN)^(k+ell)/(k!ell!)` ways, quotient values in at
most `p^(rk)` ways, and certificate pairings in at most

```
2^(d(1+d/2)k)(2dk)^E
```

ways. Invalid colors can be discarded; all overcounting is harmless.
By (6), replace the probability bound by the weighted bound

```
E[Z_H(G_N) 1_C] <= (2/N)^E p^(4sE) M_H(N).
```

Using `E<=dk`, absorb the extra factor into the support-label constant.
With `alpha=(d-2)/2` and, for example,

```
C0=h^(1+d/2) 2^(d(1+d/2)) (4d)^d exp(2),
L=C0 p^(r+4rd),
```

the full enumeration gives

```
E #{Y: AY=YR, D_a(Y)=k}
 <= M_H(N) dk L^k (k/N)^(alpha k).                        (7)
```

To see that no exponential factor is hidden here, use

```
(4dk)^E N^(v-E)/(k!ell!)
 <=(4d)^(dk)(k/N)^(alpha k) k^k/k! *k^ell/ell!,
```

sum `ell` with `sum k^ell/ell!<=exp(k)`, use
`k^k/k!<=exp(k)`, and count at most `dk` choices for `E`.
All factors in (7) are explicit and independent of `N`.

Choose

```
epsilon=min{1/(4d), (1/2)(8 exp(alpha)L)^(-1/alpha)}.
```

Then successive terms `dk L^k(k/N)^(alpha k)` have ratio at most `1/2`
throughout `k<epsilon N` for all sufficiently large `N`. A quotient
support of size one is impossible because a lift of a simple base has
no loops and every neighbor of that support vertex sees exactly one
nonzero quotient value. Summing (7) from `k=2` therefore proves (3).

## Use in induction on dimension

For a common proper invariant `H`, the quantity `M_H(N)` is precisely
the original moment with alphabet `Fp^s` and endomorphism `R|_H`, after
choosing a basis of `H`. No new model or conditional random graph
appears on its right side. The zero-dimensional base case has
`M_{0}(N)=1`.

Thus, when a separate entropy classification says that all boundary
phases on a nonbipartite base are common invariant-subspace cosets,
and a separate calculation bounds the full uniform phase, (2)-(3)
provide the required inductive control of **all** proper-subspace
neighborhoods. Since there are only finitely many subspaces and coset
maps for fixed `p,r,h`, summing their bounds is legitimate. Overlaps
only improve an upper bound.

## Bipartite appendix: two ambient spaces and maps

Let the fixed simple regular base be bipartite with parts `Lbase,Rbase`.
Use vector spaces `V_L=Fp^(r_L)`, `V_R=Fp^(r_R)` and linear maps

```
T_L: V_L -> V_R,         T_R: V_R -> V_L.
```

Assignments satisfy the well-defined equations

```
sum_(u~v) Y_u = T_L(Y_v),   v of left type,
sum_(u~v) Y_u = T_R(Y_v),   v of right type.                (8)
```

The original single-alphabet matrix problem is the special case
`V_L=V_R=V`, `T_L=T_R=R`. Allowing the spaces to differ makes induction
closed under restriction to mixed zero phases.

Choose subspaces `H_L<=V_L`, `H_R<=V_R` such that

```
T_L(H_L) subseteq H_R,       T_R(H_R) subseteq H_L.          (9)
```

Choose affine offsets `a_i+H_L` at left base types and `a_i+H_R` at
right base types, with

```
T_L(a_i)-sum_(j~i) a_j in H_R,     i left,
T_R(a_i)-sum_(j~i) a_j in H_L,     i right.                 (10)
```

Again no exact equality for the representatives is needed.

Let `Z_(H_L,H_R)(G)` be the size of the homogeneous solution space of
(8) restricted to `H_L,H_R` with the restricted maps. Put its moment
equal to `M_(H_L,H_R)(N)`. Let `D_a(Y)` count vertices outside their
respective affine cosets.

There are `epsilon>0` and `C<infinity`, depending only on the base,
`p`, and `r_L+r_R`, such that

```
E #{Y satisfying (8): D_a(Y)=0} <=M_(H_L,H_R)(N),

E #{Y satisfying (8): 0<D_a(Y)<=epsilon N}
 <= C N^(-(d-2)) M_(H_L,H_R)(N).                           (11)
```

All constants can be uniform over the maps, subspaces, and valid
offsets with these fixed ambient dimensions.

Proof: quotient (8) by `H_R` in left equations and by `H_L` in right
equations. By (9)-(10), the quotient defects solve a homogeneous system
with the induced two maps. An outside-zero vertex has all its neighbor
defect values in the same opposite-side quotient space. Exactly one
nonzero such neighbor is impossible. Thus the same certificate bound
`E-v>=(d-2)k/2` holds.

For every fixed quotient assignment, its full lifts form an affine
system with homogeneous kernel counted by `Z_(H_L,H_R)(G)`. Its size is
therefore at most that kernel size. The explicit forcing coupling above
works without modification. One image swap changes at most two left
rows, with target space `H_R`, and two right rows, with target space
`H_L`. Thus its rank perturbation is at most

```
2 dim H_R +2 dim H_L <=4(r_L+r_R).
```

Consequently a prescribed certificate of `E` edges obeys

```
E[Z_(H_L,H_R)(G) | certificate]
 <=p^(4(r_L+r_R)E) M_(H_L,H_R)(N).                        (12)
```

Every quotient-defect label has at most `p^(r_L+r_R)` possibilities.
Repeating (7) with

```
L=C0 p^((r_L+r_R)(1+4d))
```

gives the same geometric support sum and proves (11).
This reasoning also allows one ambient space to have dimension zero.

If at least one of `H_L,H_R` is proper, then

```
dim H_L +dim H_R < r_L+r_R.
```

Hence `M_(H_L,H_R)` is precisely a lower-total-dimension instance of
the same two-space problem. The induction base `r_L+r_R=0` has exactly
one solution. A theorem for bipartite bases should therefore be stated
for arbitrary two spaces and two maps, and proved by induction on
their total dimension. Together with a separate bounded full-support
phase calculation and the entropy zero-phase classification, (11)
then controls every proper mixed-subspace phase. A single-space
formulation alone would not be closed under this induction.

The same appendix remains valid if each base vertex has its own map
`T_i:V_side(i)->V_opposite(i)`: use its map in the local coset condition
and require `T_i(H_side(i)) subseteq H_opposite(i)` for every `i`.
All operators still have fixed on-site maps and the switching changes
only adjacency rows. The restricted problem retains these
vertex-dependent maps, so induction is closed in this version as well.

