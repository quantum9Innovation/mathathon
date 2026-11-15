# Zero phases and sparse-boundary induction for regular configuration frames

Prepared 2026-11-15. This note proves the phase and sparse-boundary inputs for a bounded intertwiner-moment theorem. It handles internal pairings, repeated physical slots, unequal fixed class sizes, loops, and parallel edges in the configuration model. It does **not** infer a bounded full moment from an entropy inequality: the full-uniform contribution is a separate central input.

## 1. Model and the induction class

Fix a finite set of old types `1,...,k`, positive rational proportions `w_i` with `sum_i w_i=1`, and nonnegative integers `q_ij` satisfying

```
sum_j q_ij=d>=3 for every i,
w_i q_ij=w_j q_ji.
```

Assume the undirected old-type support is connected; it has an edge `ij` when `q_ij>0` and a loop at `i` when `q_ii>0`. On an admissible size `n`, type `i` contains `n_i=w_i n` vertices. A vertex of type `i` has `q_ij` labeled physical stubs targeted at type `j`. Independently for every `i<j`, match its `n_i q_ij=n_j q_ji` cross stubs by a uniform bijection; independently for each `q_ii>0`, pair its `n_i q_ii` internal stubs uniformly. Admissibility includes even internal stub counts. Loops count twice on the adjacency diagonal, so every physical vertex has degree exactly `d` with multiplicity.

For a nonbipartite type support use one finite vector alphabet `V=F_p^r`, and allow a fixed linear on-site map `T_i:V->V` at each old type. An assignment obeys

```
sum_(incident stubs vu) Y_u=T_i Y_v,   type(v)=i.          (1)
```

The requested equation `AY=YR` is the special case in which every `T_i` is the same row-vector map `x->xR`.

For a bipartite old-type support with sides `L,R`, use two alphabets `V_L=F_p^(r_L)`, `V_R=F_p^(r_R)` and maps `T_i:V_side(i)->V_opposite(i)`. Equation (1) is then in the opposite-side space. This two-space class is needed for closure under proper-subspace restriction. Common degree and reversibility imply equal **total physical sizes** on the sides:

```
d sum_(i in L) n_i = sum_(i in L,j in R) n_i q_ij
                  = d sum_(j in R) n_j.
```

Individual old class sizes need not agree. Either alphabet may have dimension zero.

Write `Z_T(G)` for the number of assignments satisfying (1). All moments below are for the unconditioned independent configuration factors.

## 2. Repeated-slot entropy and every zero phase

At old type `i`, a star law `P_i` records its root and all `d` ordered physical neighbor labels, supported on (1). Its root law is `mu_i`. For each target type `j`, let `nu_ij` be the **pooled** root-neighbor law, averaged over the `q_ij` physical slots. Matching feasibility is

```
nu_ji=nu_ij^T   (i!=j),      nu_ii=nu_ii^T.
```

The exact pairing/bijection type exponent per total size `n` is

```
Phi(P)=sum_i w_i H(P_i)
       -sum_(i<j) w_i q_ij H(nu_ij)
       -sum_i (w_i q_ii/2) H(nu_ii).                    (2)
```

The root-label multinomial is already included in `H(P_i)`; it must not be added again.

Symmetrize `P_i` by all permutations of physical slots with the same target old type. This preserves the legal local equation and all pooled tables, and increases `H(P_i)`. Consequently `Phi(P)<=Phi(P_sym)`. Equality in this symmetrization requires the original law to equal its symmetrization, by strict concavity of Shannon entropy (equivalently, the entropy gain is an average of nonnegative relative entropies).

For symmetrized laws every physical slot to `j` has pair law `nu_ij`. Let `I_ij` be its mutual information, and let `J_it` be the conditional total correlation of all neighbor slots except physical slot `t`, conditional on the root. The omitted slot is uniquely determined by (1), with coefficient one, in every characteristic. Averaging the chain-rule identity over all omissions and using common degree and reversibility gives exactly

```
Phi=-(d-2)/d [sum_(i<j) w_i q_ij I_ij
                    +sum_i (w_i q_ii/2) I_ii]
     -(1/d) sum_i w_i sum_(physical slots t) J_it.        (3)
```

All terms on the right are nonnegative. Positive weights and `d>=3` imply that `Phi=0` forces every present pair law to be a product and every omission defect to vanish. Conversely these conditions give equality. The same conclusion classifies zeroes of the unsymmetrized exponent: a zero must have zero symmetrization loss and then satisfy (3).

### Finite-group lemma

Suppose `Z_1,...,Z_d` take values in one finite vector space, their sum is fixed, and every retained `d-1` tuple has its product marginal law. For `d>=3`, every one-coordinate law is uniform on a coset of one common subspace.

To prove this, fix two coordinates and condition all other `d-2` to support values. Each conditional one-coordinate marginal remains its original law, while the two conditioned coordinates sum to a constant. Their laws are reflected translates of each other, hence have the same support-difference space. All such spaces are therefore a common `H`. Vary a third conditioned coordinate through support differences; composing the two reflection identities makes either selected law invariant under all those differences, which generate `H`. Its support lies in one coset of `H` by definition, and invariance makes it uniform on the entire coset. Conditioning events used here have positive probability because all retained tuples have product law.

### Application with repetitions and internal slots

At a zero of (2), condition on the root at type `i`. The neighbor laws are root-independent, and the finite-group lemma applies to the `d` **physical slots**, even if several slots target the same old type. Thus all old neighbor laws of `i` are uniform cosets of one common neighbor subspace `K_i`. Every old type occurs as a neighbor, so write

```
mu_i=Uniform(a_i+H_i).
```

Whenever old types `j` and `ell` are both neighbors of `i`, `H_j=H_ell=K_i`. Hence `H_i` is constant on old-type even-walk components. Repeated slots introduce no extra component. An old internal factor supplies a self-incidence, hence an odd closed walk; it is treated exactly like a loop in this parity graph.

The remaining necessary and sufficient conditions are

```
T_i H_i subseteq K_i,
T_i a_i-sum_j q_ij a_j in K_i.                           (4)
```

For sufficiency, choose the root uniformly on its coset, choose any `d-1` neighbor labels independently uniformly on their cosets, and obtain the last from (1). The conditions in (4) place that last value in its required coset. The resulting star is uniform on its entire legal affine support, every physical pair law is the product of the root and neighbor laws, and every omission defect vanishes. This star law is unique for its cosets, since the root and any retained `d-1` coordinates determine it.

For a connected nonbipartite support, the even-walk relation has one class, including when nonbipartiteness comes from an internal factor. Thus every `H_i` is one common `H`, preserved by every `T_i`, and the quotient point-map conditions are

```
T_i a_i=sum_j q_ij a_j  modulo H.                       (5)
```

For a connected bipartite support there are two even-walk classes. The subspaces are one `H_L<=V_L` and one `H_R<=V_R`, with

```
T_i H_side(i) subseteq H_opposite(i),
T_i a_i-sum_j q_ij a_j in H_opposite(i).                 (6)
```

These classify all zero phases, including mixed phases and zero-dimensional sides. There are finitely many phases for fixed alphabets, frame, and maps. A phase is proper unless its common subspace, or both side subspaces, equal the ambient alphabets. Every proper restriction reduces `r`, or reduces `r_L+r_R` in the bipartite class. The restricted on-site maps remain in exactly the induction class stated above.

## 3. Quotient defects and affine fibers

Fix a proper phase. Denote its root subspace at type `i` by `H_i` and its coset representative by `a_i`. In the nonbipartite case all `H_i=H`; in the bipartite case they depend only on the side. Let `Z_H(G)` count the homogeneous assignments with values in these subspaces and the restricted maps, and put

```
M_H(n)=E Z_H(G_n),
D_a(Y)=#{v:Y_v notin a_type(v)+H_type(v)}.
```

There are constants `epsilon>0`, `C<infinity`, depending only on the fixed frame, field, and ambient dimensions, such that

```
E #{Y satisfies (1):D_a(Y)=0} <= M_H(n),

E #{Y satisfies (1):0<D_a(Y)<=epsilon n}
   <= C n^(-(d-2)/2) M_H(n).                            (7)
```

The constants may be chosen uniformly over the finitely many maps, proper phase subspaces, and valid coset choices at these fixed dimensions.

Define the quotient defect at a vertex by

```
z_v=Y_v mod H_type(v)-a_type(v) mod H_type(v).
```

Equations (5) or (6) make the fiber-constant quotient `a` an exact solution for **every** configuration, including loops and parallel edges. The defect `z` therefore satisfies the homogeneous quotient system and has support size `D_a(Y)`.

For any fixed quotient assignment, choose arbitrary representatives. Its lifts form an affine linear system in the subspace variables. Each nonempty affine fiber is a translate of the homogeneous restricted kernel, and hence has cardinality exactly `Z_H(G)`. Empty fibers contribute zero. In particular the zero-defect contribution is at most `Z_H(G)`, whether or not the representatives `a_i` form an exact solution before quotienting.

## 4. Dense certificates with loops and multiple edges

Let `S` be the support of a nonzero quotient defect, of size `s`. At an exterior zero vertex, exactly one **incident edge counted with multiplicity** from `S` would contribute one nonzero quotient value and cannot sum to zero. Hence every exterior vertex adjacent to `S` receives at least two incident edges from `S`. Distinct neighbors are not required; repeated edges can cancel in the field, and are included.

Take as certificate all edges incident to `S`, retaining their actual labeled stubs. Let `i` count edges with both ends in `S` (loops count as one such edge), let `j` count boundary edges, and let `t` be the number of exterior vertices reached. Then

```
ds=2i+j,       t<=j/2,
E=i+j<=ds,     V=s+t,
E-V>=((d-2)/2)s.                                        (8)
```

The certificate includes every stub at `S`, so forcing its edges automatically ensures that there are no additional edges incident to `S`. It requires no separate absent-edge conditioning.

Support size one must be retained. It is not ruled out in the multigraph configuration law: loops and repeated edges may create such quotient supports. The bound below begins at `s=1`; its positive power `n^{-(d-2)/2}` still tends to zero.

## 5. Exact forcing couplings for each factor

### Cross-stub bijection

To force unused domain stub `u` to unused target stub `v`, let `w` be the current preimage of `v` and swap the images of `u,w`. Earlier forced pairs are preserved. If `m` domain stubs remain before this step, every permitted output has exactly `m` preimages: choose the previous preimage `w` of `v`, then undo the swap. Thus a uniform conditional input becomes exactly uniform conditional on this new pair. This uses at most one image-transposition.

### Internal perfect pairing

Suppose `m` stubs remain outside all earlier forced pairs, and the next prescribed pair is `{u,v}`. If they are already paired, do nothing. Otherwise their current partners are `x,y`; replace `{u,x},{v,y}` by `{u,v},{x,y}`. Earlier forced pairs cannot involve `u,v,x,y` and are preserved.

For a fixed permitted output matching containing `{u,v}`, its preimages are the output itself, and the two inverse orientations for each other pair `{x,y}` among the remaining stubs. There are exactly

```
1+2*(m-2)/2=m-1
```

preimages, independent of the output. Therefore the new output is exactly uniform conditional on the new prescribed pair. It uses at most one two-edge switch. This proof treats stubs as distinct and is unchanged when some of them belong to the same physical vertex, so loops cause no exception.

Perform these procedures for every prescribed certificate edge within its factor, in any deterministic order. The original factors are independent, and the conditioning event factors across them. The resulting `G^C` therefore has exactly the original configuration law conditional on the certificate `C`. At most `E` switches are used.

Each switch changes adjacency rows only at the owners of its at most four affected stubs, hence at most four physical vertex rows, even in the presence of loops or repeated edges. The on-site maps are unchanged. In the one-space restricted system a row has `dim H` scalar equations; in the two-space system its target dimension is the opposite-side subspace dimension. In either case, with `r_*` equal to the ambient dimension or the sum of the two ambient dimensions,

```
rank(L_H(G^C)-L_H(G))<=4r_* E,
Z_H(G^C)<=p^(4r_* E) Z_H(G).                             (9)
```

This rank comparison is valid for rectangular operators as well. Taking expectation under the explicit coupling yields

```
E[Z_H(G_n) | C occurs] <= p^(4r_* E) M_H(n).             (10)
```

This is the needed correlation-safe bound. No independence between a rare certificate and the bulk kernel count has been assumed.

## 6. Weighted certificate enumeration

Let `lambda>0` be the smallest positive coefficient `w_i q_ij` among all present internal and cross stub pools. Each pool has at least `lambda n` stubs on its relevant side. For `s<=epsilon n` with `epsilon<=lambda/(4d)`, a valid prescribed certificate with `E<=ds` edges has probability at most

```
P(C)<= (C_frame/n)^E,       C_frame=2/lambda.            (11)
```

For cross factors this follows from reciprocal falling factorials; for internal factors the exact reciprocal factors are `1/(m-1),1/(m-3),...`. Since at most `E` pairs are exposed, every such denominator is at least `lambda n/2`.

For a fixed support size `s` and exterior count `t`, choose labeled support and exterior vertices in at most

```
n^(s+t)/(s!t!)
```

ways, and quotient labels in at most `p^(r_* s)` ways. Choose the exterior certificate stubs in at most `2^(dt)` ways. Together with all `ds` support stubs they form `2E<=2ds` selected stubs; there are at most `(2ds)^E` pairings. Invalid old-type colors, bijection directions, or duplicate incidences can simply be discarded. Thus this is a valid overcount also for internal loops.

Replace the ordinary certificate probability by its kernel-weighted probability, using (10)--(11):

```
E[Z_H(G_n) 1_C]
 <= (C_frame/n)^E p^(4r_* E) M_H(n).                    (12)
```

Let `alpha=(d-2)/2>0`. All fixed-degree, field, and dimension factors can be absorbed into `L^s`, since `E<=ds` and `t<=ds/2`. The powers of `s,n` satisfy

```
s^E n^(V-E)/(s!t!)
 =(s/n)^(E-V) [s^s/s!] [s^t/t!]
 <=(s/n)^(alpha s) [s^s/s!] [s^t/t!].
```

Use `s^s/s!<=exp(s)`, sum `s^t/t!` by `exp(s)`, and allow at most `ds` choices for `E`. One obtains, with a fixed finite `L`,

```
E #{Y satisfies (1):D_a(Y)=s}
 <= M_H(n) ds L^s (s/n)^(alpha s).                      (13)
```

For example, increasing constants harmlessly, one can take

```
L=exp(2) * 2^(d^2/2)
  * (2d C_frame p^(4r_*))^d * p^(r_*).
```

Choose

```
epsilon <= min{lambda/(4d), 1/2,
               (1/2)*(4 exp(alpha) L)^(-1/alpha)}.
```

The ratio of successive terms in (13) is at most
`2L exp(alpha)((s+1)/n)^alpha`, hence at most `1/2` for all `s<epsilon n` and all sufficiently large `n`. Summing from `s=1` gives

```
sum_(1<=s<=epsilon n) ds L^s(s/n)^(alpha s)
 =O(n^-alpha).
```

This proves (7), including the support-one configuration contribution.

## 7. Exact role in the full induction

Assume a separate central theorem bounds the full-uniform table neighborhood for the same frame and the same induction class. Induct on `r` in the nonbipartite class, or on `r_L+r_R` in the bipartite class. The dimension-zero system has one assignment. Every proper phase from Section 2 has a restricted homogeneous system of strictly lower dimension; its moment is bounded by induction, and (7) bounds its entire root-coset neighborhood. The number of such phases is finite.

Every entropy-zero phase is covered either by the central full-uniform table neighborhood or one of those root-coset neighborhoods: sufficiently near a proper phase, the proportion of vertices outside its cosets is arbitrarily small. The complementary feasible type region is compact and contains no zero of the continuous entropy exponent. The exact type formula, with its fixed polynomial Stirling/type-count prefactor, therefore bounds that complementary contribution by `poly(n) exp(-c n)`.

This supplies the complete boundary and phase part of a bounded-moment proof. It leaves no extra hypothesis on field characteristic, invertibility of the on-site maps, equal individual class sizes, absence of internal factors, or absence of repeated target types. It does still require the separate **bounded central contribution with all lattice and tail prefactors**, not merely `Phi<=0`.

Once a full configuration-model moment bound is established, conditioning the finitely many independent fixed-degree factors on simplicity costs a bounded factor. The resulting laws are exactly the independent uniform simple internal regular graphs and cross biregular graphs of the frame, since each simple graph has the same number of labeled-stub representations. This last step needs no contiguity claim. The positive limiting probability of factor simplicity applies along every admissible fixed-proportion size sequence; loops and repeated edges were retained until this step.
