# Sparse defects in regular random lifts

Prepared 2026-11-15. This note treats a random `N`-lift of a fixed
connected **simple** `d`-regular graph `B`, with `h=|V(B)|` and `d>=3`.
For each base edge the lift matching is independently uniform. Every
lift vertex has one distinguished stub for each neighboring base type.
All constants below may depend on `B`, the fixed prime `p`, and the
fixed vector dimension `r`, but not on `N`.

Let `V=Fp^r` and let `R:V->V` be any fixed linear map. We count row-vector
assignments `Y` satisfying `AY=YR`. No invertibility or semisimplicity
assumption on `R` is used.

## 1. Point-map neighborhoods

Suppose `a_i in V`, one value per base vertex, obeys

```
sum_(j~i) a_j = a_i R.
```

Its fiber-constant lift `Y0` is a deterministic intertwiner. There is a
fixed `epsilon>0` such that

```
E #{Y: AY=YR, 0<|supp(Y-Y0)|<=epsilon N}
       = O_(B,p,r)(N^(-(d-2))).                         (1)
```

Thus a neighborhood of one such point map contributes
`1+O_(B,p,r)(N^(-(d-2)))` to the moment. The union of the neighborhoods
of all point maps contributes their finite deterministic number plus
the same kind of vanishing correction. Distinct point maps differ on
at least one complete fiber of size `N`; choosing `epsilon<1/2` makes
these neighborhoods disjoint.

The result holds for every `N`; it has no parity or divisibility
restriction.

## 2. A no-unique-neighbor certificate for arbitrary R

Write `w=Y-Y0`. It satisfies `Aw=wR`. Let `S=supp(w)`, `|S|=k`.
At every vertex outside `S`, the right side is zero. If that vertex has
exactly one neighbor in `S`, its equation is a single nonzero vector
equal to zero, impossible. Hence every outside vertex touching `S`
has at least two neighbors in `S`.

Let `H` contain all edges incident to `S`, including their outside
endpoints. Let `e` be its edges internal to `S`, `b` its boundary edges,
and `ell` its outside vertices. Then

```
dk=2e+b,       E:=|E(H)|=e+b=dk-e,
ell<=b/2,     v:=|V(H)|=k+ell,
E-v>=dk-e-k-(dk-2e)/2=(d-2)k/2.                         (2)
```

Also `ell<=dk/2`, `v<=(1+d/2)k`, and `E<=dk`.
There is no condition on nonzero vertices in this proof: in particular
it remains valid when `R` has a nontrivial kernel or is zero.

## 3. Uniform small-support enumeration

Let `Z_k` count solutions `w` with support exactly `k`.
For `k<=N/(2d)`, a prescribed valid lift certificate with `E` edges has
probability at most `(2/N)^E`. Indeed, if it prescribes `s_e` pairs in
the permutation for base edge `e`, its exact probability is

```
prod_(e in E(B)) 1/(N)_(s_e),
```

and `s_e<=E<=dk<=N/2`.

For each `ell,E`, choose the support and additional outside vertices
in at most

```
(hN)^(k+ell)/(k! ell!)
```

ways, and assign the nonzero support labels in at most `Q^k` ways,
where `Q=p^r`. Among the selected `v=k+ell` vertices there are `dv`
distinguished stubs. The number of partial pairings with `E` edges is
at most

```
binom(dv,2E)(2E-1)!!
 <=2^(dv)(2E)^E
 <=2^(d(1+d/2)k)(2dk)^E.
```

This counts many invalid base-color pairings; discard them when
evaluating probabilities. It also counts graphs that are not the
full incident-edge certificate. Both overcounts are harmless.

Put `alpha=(d-2)/2` and, for example,

```
C_(h,d)=h^(1+d/2) 2^(d(1+d/2)) (4d)^d exp(2).
```

Using (2), `E-v>=alpha k`, and `k/N<=1`, factor each summand as

```
(4dk)^E N^(v-E)/(k!ell!)
 <=(4d)^(dk) (k/N)^(alpha k) k^k/k! * k^ell/ell!.
```

There are at most `dk` choices for `E`; summing `ell` and using
`k^k/k!<=exp(k)`, `sum_ell k^ell/ell!<=exp(k)` proves

```
E Z_k <= dk(C_(h,d) Q)^k (k/N)^(alpha k),
                    1<=k<=N/(2d).                       (3)
```

This controls the whole range up to a field-dependent linear fraction,
not merely fixed `k` or logarithmic supports.

To sum it, set `L=C_(h,d)Q` and choose

```
epsilon=min{1/(4d), (1/2)(8 exp(alpha)L)^(-1/alpha)}.
```

For `b_k=dk L^k(k/N)^(alpha k)`,

```
b_(k+1)/b_k
 <=2 exp(alpha)L ((k+1)/N)^alpha <=1/2
```

throughout `k<epsilon N` for all sufficiently large `N`.
Since the base and lift are simple, a nonzero support-one vector is
impossible: each of its neighbors would violate its outside equation.
Consequently the sum starts at `k=2`, and is `O(L² N^(-2alpha))`, proving
(1).

## 4. Conditional moment bound by forcing permutation pairs

The following useful refinement avoids assuming that a rare defect
event is independent of a potentially large number of bulk solutions.

Let `T_G` be any linear operator built from the lift adjacency, with
fixed vector spaces of dimension at most `r` at vertices, fixed on-site
maps, and neighbor maps unaffected by changing lift matchings. Suppose
changing a matching pair can affect at most its endpoint rows, as it
does for all the intertwiner and subspace-restricted operators here.
Write

```
K(G)=|ker T_G|,         M(N)=E K(G).
```

For a valid prescribed partial matching certificate `H` of `E` edges,

```
E[K(G) | H occurs] <= p^(4rE) M(N).                      (4)
```

Proof: start with independent uniform permutations for the base edges.
Force their prescribed pairs one at a time by swapping images. For a
new pair `u->v`, exchange the images of `u` and the current preimage
of `v`. Previous prescribed pairs remain fixed. The output permutation
is uniform conditional on all pairs forced so far: at a step with `t`
previous pairs, every permitted output has exactly `N-t` preimages
under the forcing map. Apply independently for the different base
edges.

There are at most `E` image swaps. A swap replaces two matching edges,
and thus changes at most four vertex rows of `T_G`. Hence the operator
rank changes by at most `4r` per swap, so deterministically

```
|ker T_(forced G)| <= p^(4rE) |ker T_G|.
```

Taking expectation proves (4). This bound is deliberately generous.

## 5. A general coset-boundary reduction, conditional on a smaller moment

Consider subspaces `H_i<=V` and cosets `a_i+H_i` for base types `i`.
Assume the following compatibility conditions:

* For every `i`, all its neighbors `j` have the **same** subspace;
  denote that common subspace by `K_i`.
* `H_i R` is contained in `K_i`.
* `a_i R - sum_(j~i) a_j` belongs to `K_i`.

These conditions permit a quotient defect variable at a lift vertex
of type `i`,

```
z_v = (Y_v-a_i) mod H_i in V/H_i.
```

Its local equation is well-defined in `V/K_i`:

```
sum_(u~v) z_u = induced_R_i(z_v).                       (5)
```

Each neighboring variable lies in the same target quotient because
`H_j=K_i`. A zero quotient variable on the right again forces every
outside touched vertex to have at least two nonzero quotient neighbors.
Thus the dense certificate (2) and enumeration (3) apply to these
quotient supports, with at most `p^r` labels per defect.

Define the homogeneous restricted solution space

```
mathcal K_H(G) = {h: h_v in H_type(v), sum_(u~v) h_u=h_v R},
M_H(N)=E|mathcal K_H(G)|.
```

For a fixed quotient assignment `z`, every full assignment over it is
obtained by choosing representatives and solving an affine system in
the variables `h_v in H_type(v)`. Its nonempty solution fiber has
cardinality exactly `|mathcal K_H(G)|`; otherwise its cardinality is
zero. In particular the number of lifts is at most that kernel size.

Apply (4) to this restricted operator. Both its domain and row target
spaces have dimension at most `r`, so the same rank bound applies.
For a support-`k` defect certificate, `E<=dk`, and the conditional
bulk-kernel factor is at most `p^(4rdk) M_H(N)`. Repeating the entire
enumeration with

```
L_H=C_(h,d) p^(r+4rd)
```

therefore proves

```
E #{Y: AY=YR, 0<# {v:Y_v notin a_type(v)+H_type(v)}<=epsilon_H N}
 <= M_H(N) O_(B,p,r)(N^(-(d-2))).                       (6)
```

Here `epsilon_H>0` is a sufficiently small fixed number, obtained from
the explicit choice in Section 3 with `L_H` in place of `L`.

The all-in-coset sector has at most `M_H(N)` solutions in expectation,
since it is one affine system with homogeneous kernel
`mathcal K_H(G)`. Hence the whole phase neighborhood satisfies

```
expected phase contribution <= M_H(N)[1+O_(B,p,r)(N^(-(d-2)))].   (7)
```

If a smaller-dimensional moment theorem supplies `sup_N M_H(N)<infinity`,
(6) makes all nonzero sparse defects vanish and (7) gives a bounded
nearby-phase contribution. This is a genuine moment bound, not just a
high-probability exclusion of defects.

## What this does not settle

The coset reduction assumes the three compatibility conditions above;
their derivation from equality in the lifted star entropy belongs to
the entropy worker. For a connected nonbipartite base, equality is
expected to force one common subspace `H`; on a bipartite base two
alternating subspaces may occur. The reduction allows either situation
once the displayed conditions hold.

When some `H_i` is proper, the restricted system has smaller total
fiber dimension `sum_i dim H_i` than the original `hr`, suggesting
induction. But it may have different variable spaces on the two parts
of a bipartite base. An induction theorem must therefore be formulated
for such compatible families of spaces and maps, not only for one
common alphabet `Fp^r` and a single endomorphism.

This note does not establish a central Gaussian bound for that more
general restricted family, nor boundedness of `M_H(N)` by itself.
Without such a bound, a sparse-support probability estimate alone
would be insufficient to control the expected number of full
intertwiners near a nontrivial subspace phase. Inequality (6) isolates
exactly the additional input and shows how it enters.
