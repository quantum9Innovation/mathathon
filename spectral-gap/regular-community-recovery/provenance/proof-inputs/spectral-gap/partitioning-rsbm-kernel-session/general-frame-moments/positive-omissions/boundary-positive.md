# Positive omission weights: phases, sparse boundaries, and dimension closure

Prepared 2026-11-15. This is a detailed extension of the phase/boundary part of the frozen regular-frame proof. It covers varying total degrees under the hypothesis that **every active factor has a symmetric omission weight strictly between zero and one half**. It does not cover an active factor with omission weight zero, and does not classify the heterogeneous phases of that broader setting.

The central full-uniform contribution remains a separately proved input. No bounded complete moment is inferred merely from the nonpositive entropy identity below.

## 1. Fixed frame, configuration law, and precise class

Fix a nonnegative integer degree matrix `D=(d_ij)` on old types `1,...,k`, positive fixed proportions `alpha_i` summing to one, and reversibility

```
alpha_i d_ij=alpha_j d_ji.
```

The old support is connected, with a loop at `i` exactly when `d_ii>0`. Let `d_i=sum_j d_ij` and `Dmax=max_i d_i`. Assume a fixed real certificate

```
q_ij=q_ji,
0<q_ij<1/2 on EVERY active factor,
sum_j d_ij q_ij=1 for every i.                           (P)
```

An absent factor has no weight or term. The internal weight `q_ii` is the weight of each internal **physical slot**, not half that weight. Since a vertex's `d_i` positive slot weights sum to one and each is below one half, (P) implies `d_i>2`. Thus

```
dmin:=min_i d_i>=3,       Dmax<infinity.
```

At admissible total size `n`, type `i` has `n_i=alpha_i n` vertices. Internal stub counts `n_i d_ii` must be even, and cross counts obey `n_i d_ij=n_j d_ji`. Pair each present internal pool uniformly and independently; match each cross pool by an independent uniform bijection. Stubs retain their labeled physical slot positions. Loops and parallel edges remain in the model, and each loop gives two adjacency incidences. Fixed integer multipliers `n_i=a_i N` are an equivalent scaling, with `n=(sum_i a_i)N`.

For one common vector alphabet `V=F_p^r`, allow fixed type-dependent linear maps `T_i:V->V` and equations

```
sum_(incident physical slots vu) Y_u=T_i(Y_v),
                                                   type(v)=i. (1)
```

The requested matrix equation `AY=YR` is the case `T_i(x)=xR` for every type. For a bipartite old support use the enlarged class with two vector spaces `V_L,V_R` and arbitrary maps `T_i:V_side(i)->V_opposite(i)`. Each sum in (1) is then in the opposite-side space. This enlarged class is necessary for induction and permits either side to have dimension zero.

### The bipartite raw population equality

Under (P), the total physical populations of the two parity sides are equal even though the `d_i` vary:

```
sum_(i in L) n_i
 =sum_(i in L,j in R) n_i d_ij q_ij
 =sum_(j in R,i in L) n_j d_ji q_ji
 =sum_(j in R) n_j.                                      (2)
```

This uses both reversibility and the symmetric unit omission rows. Ordinary degree balance alone would not give (2) for nonregular frames. The equal raw population property is inherited by every restricted two-space problem, since neither the frame nor the omission certificate changes under restriction.

## 2. Exact weighted entropy identity

At type `i`, let `P_i` be a law on legal ordered stars: its root plus its `d_i` neighbor labels satisfying (1). Its root marginal is `mu_i`. On each active `ij`, let `nu_ij` be the root-neighbor law pooled over the `d_ij` slots aimed at `j`. Pairing feasibility requires

```
nu_ji=nu_ij^T for cross factors,
nu_ii=nu_ii^T for internal factors.
```

Its two marginals are `mu_i,mu_j`. Set

```
w_ij=alpha_i d_ij              for i<j,
w_ii=alpha_i d_ii/2,

Phi(P)=sum_i alpha_i H(P_i)-sum_(i<=j,active) w_ij H(nu_ij). (3)
```

This is the actual configuration-model type exponent per total physical size. The root-label assignments are already included in the star entropy. They must not be added again.

Symmetrize each `P_i` over permutations of slots having the same old target type, yielding `Pbar_i`. This preserves the local equation, root marginals, and pooled tables and increases star entropy, so `Phi(P)<=Phi(Pbar)`. Equality holds only if the star law is already invariant under those permutations: the concavity gap is an average relative entropy and vanishes only when all permuted laws agree.

For a symmetric law, every physical slot toward `j` has pair law `nu_ij`. Write `I_ij` for its mutual information. For omission of physical slot `t`, define the conditional total correlation

```
J_it=sum_(s!=t) H(Z_is | X_i)
       -H((Z_is)_(s!=t) | X_i) >=0.
```

The omitted value is uniquely determined by the root and retained neighbors with coefficient one. Thus the omission is lossless in every field characteristic. Average that exact chain-rule identity with the physical weights `q_it=q_i,j(t)`, which sum to one:

```
H(Pbar_i)
 =H(mu_i)+sum_s(1-q_is)H(Z_is|X_i)-sum_t q_it J_it
 =(2-d_i)H(mu_i)
   +sum_j d_ij(1-q_ij)H(nu_ij)-sum_t q_it J_it.            (4)
```

Inserting into (3), cross reversal and the internal half-edge coefficient give `w_ij(1-2q_ij)` on each pooled pair entropy. Replace pair entropy by `H(mu_i)+H(mu_j)-I_ij`, with two copies of the root entropy for an internal factor. The coefficient on `H(mu_i)` becomes

```
alpha_i[(2-d_i)+sum_j d_ij(1-2q_ij)]
 =alpha_i[2-2 sum_j d_ij q_ij]=0.
```

Consequently the **exact** symmetric-law identity is

```
Phi(Pbar)
 =-sum_(i<=j,active) w_ij(1-2q_ij) I_ij
  -sum_i alpha_i sum_(physical slots t) q_it J_it <=0.     (5)
```

This is the weighted identity from the frozen frontier sources, rederived here to check both the internal factor and its use for finite-field/vector labels. It divides no field element by a degree or omission weight. It remains valid in the bipartite two-space class because the entropy of an edge law is the sum of its two possibly different root entropies minus mutual information.

Under (P), every coefficient displayed in (5) is strictly positive. Therefore `Phi(P)=0` implies zero symmetrization loss, **every** active pair mutual information zero, and **every** physical omission total correlation zero. Conversely those conditions give equality. This is exactly where positivity on every active factor is needed; an active weight `q_ij=0` would leave some omission terms uncontrolled, and the phase argument below is not asserted in that case.

## 3. Complete zero-phase classification with local degrees

### Finite-group fact

Let `m>=3` variables in a finite vector space have a fixed sum, and suppose every retained `m-1` tuple has its product marginal law. Then each marginal is uniform on a coset of one common linear subspace.

Proof: condition all but two coordinates to support values. Their one-coordinate conditional laws remain the original marginals by retained-product independence, while their sum is fixed, so the two laws are reflected translates and have the same support-difference subspace. This makes all difference spaces a common `H`. Vary a third conditioned coordinate through support differences. Comparing the reflected laws yields translation invariance by all generators of `H`. Each marginal support is contained in one coset of its difference space, so invariance makes it uniform on the entire coset. All conditioning events have positive probability because the retained laws are products. This also includes `H=0`.

### Applying it at zero entropy

At `Phi=0`, pair independence makes each neighbor marginal independent of the root. Conditional on any root support value at type `i`, every retained `d_i-1` neighbor tuple is a product by the vanishing of all its `J_it`. Since `d_i>=3`, apply the fact to its `d_i` physical neighbors. Every neighbor law is a uniform coset, and all neighbor subspaces at `i` coincide. Every old type occurs as a neighbor at some active slot, so write

```
mu_i=Uniform(c_i+H_i).
```

The relations are

```
H_j=H_ell whenever j and ell are old neighbors of i.
```

They make the subspaces constant on even-walk components of the old support. Repeated slots do not alter this relation. A positive internal factor is a self-incidence and supplies an odd walk. Thus connected nonbipartite support has one common subspace `H`; connected bipartite support has exactly its two parity classes `H_L,H_R`.

Let `K_i` denote the common subspace of the physical neighbors of `i`. The exact remaining conditions are

```
T_i(H_i) subseteq K_i,
T_i(c_i)-sum_j d_ij c_j in K_i.                          (6)
```

For every root in `c_i+H_i`, these are necessary and sufficient for its target sum to belong to the sum of the neighbor cosets. That sum is `sum_j d_ij c_j+K_i`; the sum of independently variable copies of a subspace is the same subspace, even if the degree is zero in the field. No division by `d_i` is involved.

Conversely, under (6), choose a uniform root on its coset, choose any `d_i-1` independent uniform neighbor labels on their cosets, and determine the omitted neighbor. Condition (6) puts it in its required coset. The star is uniform on its entire legal affine support, all pair laws are the root/neighbor product laws, and every omission defect vanishes. This is the unique zero star law for the specified cosets because root plus any retained tuple determines it.

The classification is therefore complete:

- **Connected nonbipartite support:** one common `H<=V`, preserved by every `T_i`, and quotient point maps `T_i(c_i)=sum_j d_ij c_j modulo H`.
- **Connected bipartite support:** `H_L<=V_L`, `H_R<=V_R`, maps `T_i(H_side(i)) subseteq H_opposite(i)`, and the corresponding quotient point equations modulo the opposite-side subspace.

There are finitely many phases at fixed field, dimensions, type count, and maps. Each proper phase strictly lowers the common dimension or the sum of the side dimensions; its homogeneous restrictions remain in the same one-space or two-space class. The frame and its strictly positive omission certificate are unchanged.

This conclusion is about finite-field/vector phases. It does not confuse them with the point-only zero phases of real one-hot laws in the frontier recovery argument. Intermediate subspaces and unequal bipartite side subspaces are real possibilities and are retained here.

## 4. Quotient defects and affine-fiber comparison

Fix a proper phase with root coset `c_i+H_i`. Let `Z_H(G)` count the homogeneous restricted system with values in the relevant `H_i` and restricted maps, and put `M_H(n)=E Z_H(G_n)`. Let

```
D_c(Y)=#{v:Y_v notin c_type(v)+H_type(v)}.
```

There exist fixed constants `epsilon>0,C<infinity` such that

```
E #{Y satisfies (1):D_c(Y)=0} <= M_H(n),

E #{Y satisfies (1):0<D_c(Y)<=epsilon n}
 <= C n^(-(dmin-2)/2) M_H(n).                            (7)
```

All constants can be chosen uniformly over the finite map/phase family at fixed ambient data.

Indeed, quotient by `H_i` in each variable space and by the corresponding neighbor subspace in each equation. Subtract the type-constant quotient point map `c`. It is exact on **every** configuration because the incidence counts toward old type `j` are deterministically `d_ij`, including both incidences of an internal loop. The remaining quotient defect satisfies a homogeneous linear system and has support size `D_c(Y)`.

For each fixed quotient assignment choose arbitrary representatives in the ambient spaces. Its lifts form an affine system with homogeneous kernel counted by `Z_H(G)`. Its cardinality is zero or exactly `Z_H(G)`. This handles nonexact representatives before quotienting and any solvability obstruction; no lift of a quotient map to an exact point map is presumed. In particular it proves the first inequality of (7).

## 5. Mixed-degree dense certificates

Let `S` be the support of a nonzero quotient defect, with `s` vertices, and expose every incident edge retaining the actual labeled stubs. A zero exterior vertex cannot receive exactly one edge incidence from `S`, because its equation would then contain exactly one nonzero quotient value. Every reached exterior vertex receives at least two incidences. Multiplicities, not distinct neighbors, are counted.

Let `i` count edges with both ends in `S` (a loop counts as one edge), `j` count boundary edges, and `t` the number of exterior vertices reached. Then

```
2i+j=sum_(v in S) degree(v) >= dmin s,
t<=j/2,
E=i+j<=Dmax s,
E-(s+t)>=((dmin-2)/2)s.                                 (8)
```

Also `t<=Dmax s/2`. Loops contribute twice to support degree and once to `E`. Since the certificate includes every support stub, forcing its edges requires no extra absent-edge condition. A certificate may have support size one in the configuration law; it must not be discarded.

## 6. Exact forcing and the conditional kernel charge

The forcing procedures do not use row regularity.

- **Cross bijection:** to force a prescribed unused domain stub `u` to an unused target stub `v`, swap the image of `u` with the current preimage of `v`. Each permitted output has exactly as many preimages as there are currently unused domain stubs, by choosing that former preimage. Earlier prescribed pairs are preserved.
- **Internal pairing:** with `m` currently free stubs, force the next prescribed pair `{u,v}`. If already paired, do nothing. Otherwise replace `{u,x},{v,y}` by `{u,v},{x,y}`, using their current partners `x,y`. For each permitted output there is its no-switch preimage, plus two inverse orientations for each of its other `(m-2)/2` pairs: exactly `m-1` preimages. Earlier forced pairs cannot involve these free stubs and remain intact.

Thus each step preserves exact uniformity conditional on the prescribed pairs. Treat independent factors separately. For a valid certificate of `E` stub pairs the final graph `G^C` has exactly the original configuration law conditional on that certificate, and at most `E` switches were used.

Every switch changes at most four physical vertex rows of the adjacency part, even when stubs share owners or create loops. It does not change the fixed on-site maps. With `r_*` the ambient dimension in the one-space class, or the sum of ambient side dimensions in the two-space class, the restricted operator therefore obeys

```
rank(L_H(G^C)-L_H(G))<=4r_* E,
Z_H(G^C)<=p^(4r_* E) Z_H(G).
```

The rank comparison applies to rectangular operators too. Taking expectations under this explicit coupling proves

```
E[Z_H(G_n) | certificate C] <= p^(4r_* E) M_H(n).        (9)
```

It controls the rare-certificate/bulk-kernel correlation rather than assuming those two quantities independent.

## 7. Summable weighted support enumeration

Let `lambda>0` be the smallest coefficient `alpha_i d_ij` among present internal and cross pools. Pool sizes are at least `lambda n` on each relevant side. For `s<=epsilon n`, with `epsilon<=lambda/(4Dmax)`, the probability of a valid certificate of `E<=Dmax s` stub pairs is at most

```
P(C)<=(C_frame/n)^E,       C_frame=2/lambda.             (10)
```

Cross factors have reciprocal falling-factorial probabilities. Internal factors have factors `1/(m-1),1/(m-3),...`; throughout the exposure every denominator is at least `lambda n/2`. No equality of total degrees or of individual class sizes enters this bound.

Choose support and exterior vertices in at most `n^(s+t)/(s!t!)` ways, quotient values in at most `p^(r_*s)` ways, exterior selected stubs in at most `2^(Dmax t)` ways, and a pairing of all selected stubs in at most `(2Dmax s)^E` ways. There are at most `Dmax s` choices for `E`. Invalid old-type colors and directions are simply discarded. This overcount includes all valid certificates, including loops.

Use (9) to weight the certificate probability by the homogeneous kernel count:

```
E[Z_H 1_C] <= (C_frame/n)^E p^(4r_* E) M_H(n).
```

Let `beta=(dmin-2)/2>0`. Since `E<=Dmax s`, `t<=Dmax s/2`, and `E-(s+t)>=beta s`, all fixed factors can be put into `B^s`, and

```
s^E n^(s+t-E)/(s!t!)
 <= (s/n)^(beta s) [s^s/s!] [s^t/t!].
```

Use `s^s/s!<=exp(s)` and `sum_t s^t/t!<=exp(s)`. One obtains a fixed finite `B` such that

```
E #{Y satisfies (1):D_c(Y)=s}
 <= M_H(n) Dmax s B^s(s/n)^(beta s).                    (11)
```

For example the conservative constant

```
B=exp(2) * 2^(Dmax^2/2)
  * (2Dmax C_frame p^(4r_*))^Dmax * p^(r_*)
```

is sufficient after harmless enlargements. Choose

```
epsilon <= min{lambda/(4Dmax), 1/2,
               (1/2)*(4 exp(beta) B)^(-1/beta)}.
```

The ratio of consecutive support terms is then at most
`2B exp(beta)((s+1)/n)^beta<=1/2` throughout the range for sufficiently large `n`. Summing (11) from **s=1** proves

```
sum_(1<=s<=epsilon n) Dmax s B^s(s/n)^(beta s)
 =O(n^-beta),
```

and hence the second inequality of (7).

## 8. Closing the dimension induction, conditional only on the central input

Assume the separately established full-uniform theorem for the same class: fixed frame satisfying (P), local degrees `d_i>=3`, arbitrary fixed on-site maps, and either one common vector alphabet or two parity-side alphabets with equal total physical populations. The equality required in the two-space central normalizer is supplied by (2), so it is not an additional unproved regularity assumption.

Induct on the ambient dimension for nonbipartite support, and on the sum of side dimensions for bipartite support. The zero-dimensional system has exactly one assignment. Every proper phase from Section 3 has lower-dimensional restricted homogeneous maps and the same frame and omission certificate; thus its `M_H(n)` is bounded by the induction hypothesis. The affine-fiber comparison and (7) bound its entire fixed root-coset neighborhood. All constants can be chosen uniformly over the finite phase family, and the number of phases is finite.

The full-uniform phase is controlled by the separate central theorem, which must retain its lattice index and tail prefactors. Every remaining feasible empirical star-law region outside these central and proper-coset neighborhoods has compact closure containing no entropy zero. The continuous exponent (3), with complete zero classification from (5)--(6), has a strictly negative maximum there. The exact finite-alphabet pairing/bijection type formula has a fixed polynomial Stirling/type-count prefactor, so the complementary contribution is `poly(n) exp(-c n)`.

This closes the bounded configuration-model moment once that central input is supplied. A finite limsup becomes a supremum by absorbing finitely many smaller admissible sizes. The finite number of linear maps at fixed field/dimensions permits a uniform maximum over target matrices `R`. Nothing in this induction assumes a zero-mass candidate class is absent from the feasible-type region.

## 9. Direct simplicity conditioning

Every present factor has fixed bounded degrees. Its simplicity probability tends to a positive constant along its admissible sizes; absent factors are omitted, and matching factors have probability one. A direct calculation counts loops and unordered pairs of parallel edges: disjoint fixed bad patterns give their Poisson factorial-moment limits, while consistent overlaps have positive edge excess and vanish as the relevant pool size grows. The internal mean is `(d_ii^2-1)/4` for `d_ii>=1`; the cross mean is `(d_ij-1)(d_ji-1)/2`. Their finite independent sum gives a positive zero-bad-event limit.

Thus conditioning all factors on simplicity costs a bounded factor in the **unconditional** moment. Each simple internal graph has `(d_ii!)^(n_i)` labeled-stub representations and each simple cross factor has `(d_ij!)^(n_i)(d_ji!)^(n_j)` representations, constant over that factor's simple graphs. The resulting factors are exactly the independent uniform simple regular/biregular factors, with no contiguity step for an unbounded statistic. Conditional statements are made only at sizes where all simple factors exist. Only the original balance and internal parity constraints are used; no new even-size requirement is imposed on an absent internal factor or a cross matching.

## 10. Scope barrier and read-only provenance

This proof requires (P) on **every active factor**. It does not replace that hypothesis by merely nonnegative weights or by strict mutual-information coefficients on some edges. Active zero weights remove some omission equalities and can permit heterogeneous finite-field phases outside the common-subspace/two-space class proved here. Those cases are excluded, not inferred from entropy compactness. A weight one half is excluded as well, since it removes a pair mutual-information coefficient.

The local weighted identity was freshly rederived above and checked against these actual frozen sources, which were read without edits:

```
60e40385f2d4236d4279e25da3101f64d1c143ed4238ab41acda739afe5891e0  positive-omission-bounded-moment-root.txt
9d5945efd705159729f60ef718073d853f7c6e6218ae4e6389c90ecc6e5cb786  weighted-entropy/omission-weights-and-nonregular-entropy.tex
3ad4038397fc6469344b29c0e96922dc17ab41deec48783ce0084c75748f5320  strict-q-recovery/entropy-audit/strict-weight-entropy-gap.tex
0042ca4067451330f955c9621bc741694369f4743ee4823c70f16f6a87d4c634  strict-q-recovery/strict-q-blind-frame-recovery.tex
```

The sparse-forcing and lattice-independent boundary reasoning is the local-degree extension of the frozen `general-frame-moments/boundary-frame.md`. Existing general-frame files and frontier packets were treated as read-only. All artifacts for this extension are confined to `general-frame-moments/positive-omissions/`.
