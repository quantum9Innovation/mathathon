# Sparse quotient certificates with zero omission weights

Prepared 2026-11-15. This module proves the boundary estimate for the heterogeneous channel class in `../zero-omission-channel-moment-root.txt`. It does not assume injectivity of an inactive quotient channel. The entropy-zero classification and the central full-uniform estimate are separate inputs.

## 1. Model and the boundary statement

Let `i=1,...,k` be finitely many old types, with fixed positive proportions `alpha_i`, `sum_i alpha_i=1`. Write `n_i=alpha_i n` on admissible size sequences. Each vertex of type `i` has `d_ij` labeled stubs targeted at type `j`, where

```
alpha_i d_ij=alpha_j d_ji,       D=max_i sum_j d_ij<infinity.
```

Independently, use a uniform cross-stub bijection in every present factor `i<j` and a uniform internal pairing in every present factor `ii`. Internal stub counts are even. A loop contributes two incidences. Fix symmetric omission weights

```
q_ij=q_ji,   0<=q_ij<1/2,   sum_j d_ij q_ij=1.
```

A stub/edge is called **active** when its old-type factor has `q_ij>0`. Symmetry makes this an undirected property. There are at least three active stubs at every vertex: one or two numbers each strictly below `1/2` cannot sum to one.

For each old type fix finite `F_p` spaces `V_i,U_i`, maps `T_i:V_i->U_i`, and channels `L_ij:V_j->U_i`. The ambient channels are injective; active channels are isomorphisms. A solution is a choice `Y_v in V_i` satisfying

```
sum_(stubs vu at v) L_ij(Y_u)=T_i(Y_v),      type(v)=i.       (1)
```

Fix subspaces `H_i<=V_i`, `K_i<=U_i` and representatives `a_i in V_i` such that

```
L_ij(H_j) subseteq K_i                 on every present factor,
L_ij(H_j)=K_i                          on every active factor,
T_i(H_i) subseteq K_i,
T_i(a_i)-sum_j d_ij L_ij(a_j) in K_i.                       (2)
```

The active restrictions are isomorphisms. Let `Z_H(G)` count the homogeneous restricted solutions with roots in `H_i`, outputs in `K_i`, channels `L_ij|H_j`, and on-site maps `T_i|H_i`. Put `M_H(n)=E Z_H(G_n)` and

```
D_a(Y)=#{v:Y_v notin a_type(v)+H_type(v)}.
```

**Boundary theorem.** There are constants `epsilon>0` and `C<infinity`, depending only on the fixed frame, spaces, channels, and field, such that

```
E #{Y solves (1):D_a(Y)=0} <= M_H(n),
E #{Y solves (1):1<=D_a(Y)<=epsilon n} <= C n^(-1/2) M_H(n). (3)
```

The constants can be maximized over any finite collection of maps, subspaces, and phase cosets on these fixed finite spaces. No assumption on equal total old-type degrees or on positivity of all omission weights appears in this statement.

## 2. Quotients and affine fibers

By (2), define quotient maps

```
Lbar_ij:V_j/H_j -> U_i/K_i,      Tbar_i:V_i/H_i -> U_i/K_i.
```

An inactive `Lbar_ij` may have a kernel. An active quotient channel is an isomorphism: both the ambient map `L_ij:V_j->U_i` and the restricted map `L_ij:H_j->K_i` are isomorphisms.

For a full assignment define its quotient defect

```
z_v=(Y_v+H_i)-(a_i+H_i),       type(v)=i.
```

The final condition in (2) says that the type-constant quotient assignment `a` is a solution for every configuration, including configurations with loops and multiple edges. Thus a solution of (1) has a defect satisfying the homogeneous quotient equations

```
sum_(stubs vu at v) Lbar_ij(z_u)=Tbar_i(z_v).               (4)
```

For any fixed quotient assignment `z`, its lifts satisfying (1) form an empty affine fiber or a translate of the restricted homogeneous kernel. Indeed two lifts differ by an element of `H_i` at every vertex, and their difference satisfies exactly the restricted homogeneous equations; conversely adding such a solution preserves the fiber. Every nonempty fiber therefore has cardinality `Z_H(G)`. In particular the zero-defect contribution is at most `Z_H(G)`. This proves the first part of (3) without requiring the chosen `a_i` to solve the unquotiented equations.

## 3. The selected certificate

Let `S={v:z_v!=0}`, `s=|S|>=1`, for a quotient solution of (4). Start the certificate with **all active edges incident to S**, retaining their actual labeled stubs.

Let `w` be outside `S` and let `h(w)` count its active incidences from `S`, with multiplicity. If `h(w)=1`, the corresponding contribution in (4) is nonzero because the channel at `w` is an active quotient isomorphism. The on-site term is zero, as are contributions from outside `S`. Hence the equation at `w` forces at least one further incidence from `S` whose quotient-channel contribution is nonzero. That incidence is inactive, since the active incidence was unique. Add one such inactive edge to the certificate. A fixed ordering of physical stubs may be used to make the choice deterministic.

If `h(w)>=2`, add no cancellation edge at `w`. If `h(w)=0`, do not include `w`. Consequently every selected outside vertex is incident to at least two selected boundary edges. Every selected edge touches `S`. The certificate need not contain the other inactive edges incident to `S`, and no condition is imposed on those unselected edges.

Let `a` be the number of selected edges with both endpoints in `S`, including loops as one edge; let `b` be the number of selected boundary edges; and let `t` be the number of selected outside vertices. With `E=a+b`, `V=s+t`,

```
2a+b >= 3s,       b>=2t,
E<=D s,           t<=D s/2,
E-V=a+b-s-t >= a+b/2-s >= s/2.                            (5)
```

The first inequality counts the at least three active physical stubs at every vertex in `S`. A loop contributes two of those stubs and one to `a`; parallel edges count individually. The bound `E<=Ds` holds because every selected edge touches `S`. These observations include `s=1` and fields of every characteristic.

This replaces the invalid assertion that an outside vertex with one *total* support neighbor is impossible under arbitrary inactive quotient maps. Only the unique **active** incidence is used to force a cancellation edge.

## 4. Uniform forcing and correlation control

A certificate `C` is a finite list of prescribed distinct stub pairs, with no stub repeated, respecting old-type factors. Its occurrence means just that those pairs appear. Unselected stubs have no prescribed or forbidden partners.

For a cross factor, force a new pair `u->v` by swapping the current images of `u` and the current preimage of `v`. If `m` stubs remain on each side after earlier prescriptions, each permitted output bijection has exactly `m` preimages under this operation: choose the earlier preimage of `v` and undo the image swap. Thus a uniform input conditional on earlier prescriptions becomes exactly uniform conditional on the new one. Earlier forced pairs are unchanged.

For an internal factor, if `u,v` are not currently paired, let their partners be `x,y` and replace `{u,x},{v,y}` by `{u,v},{x,y}`. If already paired, make no change. With `m` unprescribed stubs remaining, every permitted output has exactly

```
1+2*(m-2)/2=m-1
```

preimages: itself, and the two inverse orientations for each other output pair. This is therefore exactly uniform conditional forcing as well. Distinct stubs can have the same physical owner; the proof still applies to loops and parallel edges.

Apply these operations sequentially to all `E` prescribed pairs within their independent factors. The coupled output `G^C` has precisely the configuration law conditional on `C`; at most `E` switches were used. Every switch changes equations only at the physical owners of at most four stubs. Set

```
r_out=max_i dim U_i,       r_root=max_i dim V_i.
```

The restricted operator has the fixed rectangular domain `directsum_v H_type(v)` and codomain `directsum_v K_type(v)`. Hence

```
rank(A_H(G^C)-A_H(G)) <= 4 r_out E,
Z_H(G^C) <= p^(4 r_out E) Z_H(G).
```

The second inequality is the rank-nullity inequality for two linear maps with the same domain and codomain; square matrices are not required. Taking expectation under the coupling gives

```
E[Z_H(G_n) | C] <= p^(4 r_out E) M_H(n).                 (6)
```

There is no independence assumption between a rare certificate and the restricted kernel.

Let

```
lambda=min_{d_ij>0} alpha_i d_ij>0.
```

Every factor stub pool has at least `lambda n` stubs. If `s<=epsilon n`, `E<=Ds`, and `epsilon<=lambda/(4D)`, every denominator in the exact prescribed-pair probability is at least `lambda n/2`. Cross factors use reciprocal falling factorials; internal factors use reciprocals of `m-1,m-3,...`. Thus, with `c_0=2/lambda`,

```
P(C) <= (c_0/n)^E,
E[Z_H(G_n) 1_C] <= M_H(n) (c_0 p^(4 r_out)/n)^E.         (7)
```

## 5. Enumeration without saturation of inactive stubs

Fix support size `s`, selected exterior count `t`, and selected edge count `E`. The following bounds deliberately overcount:

* Choose support and exterior vertices in at most `n^(s+t)/(s!t!)` ways.
* Choose nonzero quotient labels on `S` in at most `p^(r_root s)` ways; all outside labels are zero.
* Choose the selected physical stubs at `S` and at the exterior vertices in at most `2^(D(s+t))` ways. In actual certificates all active stubs at `S` are selected; allowing arbitrary subsets is a harmless overcount. The factor `2^(Ds)` here is needed because inactive support stubs are not saturated.
* Pair the `2E` selected stubs in at most `(2E)^E<=(2Ds)^E` ways. Discard invalid old-type factors, mismatched cross directions, edges not touching `S`, or failures of the certificate degree conditions.

To justify the use of this count, associate to each quotient solution its selected certificate from Section 3. A full-solution fiber has at most `Z_H(G)` elements. Drop all additional quotient equations and all tests specifying which cancellation edge was selected. The sum over all quotient assignments and candidate certificates, weighted by `Z_H(G) 1_C`, still dominates the original count. In particular, no absence event for unselected inactive edges has entered (7).

Write `V=s+t`. The permitted certificates satisfy (5). After applying (7), all fixed parameters can be absorbed into `B^s`, because `E<=Ds` and `t<=Ds/2`. For `s<=n`, the remaining powers obey

```
s^E n^(V-E)/(s!t!)
  =(s/n)^(E-V) (s^s/s!) (s^t/t!)
 <=(s/n)^(s/2) (s^s/s!) (s^t/t!).                       (8)
```

The factorial bounds `s^s/s!<=e^s` and `sum_(t>=0) s^t/t!=e^s` apply. There are at most `Ds+1` choices of `E`, and `Ds+1<=(D+1)^s` for every `s>=1`. Therefore a fixed constant `B_1` gives the pointwise estimate

```
E #{Y solves (1):D_a(Y)=s}
 <= M_H(n) B_1^s (s/n)^(s/2),       1<=s<=epsilon n.     (9)
```

For concreteness it is enough to take

```
B_1=(D+1)e^2 p^r_root 2^(D(1+D/2))
    * max{1,2D c_0 p^(4 r_out)}^D,
```

though the size of this fixed constant has no significance.

For `f_s=B_1^s(s/n)^(s/2)`,

```
f_(s+1)/f_s
 =B_1 sqrt((s+1)/n) (1+1/s)^(s/2)
 <=B_1 sqrt(e(s+1)/n).
```

Choose

```
epsilon <= min{lambda/(4D), 1/2, 1/(16 e B_1^2)}.
```

For consecutive terms with `s+1<=epsilon n`, this ratio is at most `1/4`. Thus their sum is at most `(4/3)B_1 n^(-1/2)`. If there is no positive integer below `epsilon n`, the sum is empty. Summing (9) proves the second part of (3), with no discarded support-one case.

## 6. Exact implication for induction

Suppose the entropy analysis gives finitely many phases satisfying (2), and that every proper phase reduces `sum_i dim V_i` on restriction. If the central theorem bounds a neighborhood of the full-uniform phase, then (3) supplies a bounded contribution near every proper phase by induction on that total root dimension. The all-zero-dimensional system has exactly one assignment. A root-coset neighborhood of a proper phase is covered by `D_a(Y)<=epsilon n`, so no star-law convergence rate is needed at the boundary.

After taking finitely many neighborhoods, any remaining compact feasible-profile set has strictly negative entropy if the phase classification is complete. The exact type formula has only a fixed polynomial number of profiles and a fixed polynomial Stirling prefactor. Its contribution is then exponentially small. This completes the boundary part of the bounded-moment assembly, conditional on the separately proved exact phase classification and central estimate.

This module makes no claim about novelty, algorithmic recovery, or the sharp central constant. It proves the sparse estimate needed for forced-zero omission edges.
