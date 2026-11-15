# Bounded finite-field channel moments, including forced zero omission weights

Derived November 15, 2026. This is a new proof packet. The regular-frame and positive-omission packets are read-only. Historical priority is not asserted. The three expanded proof modules in this directory establish the ingredients used here; their conclusions are not assumptions about a common alphabet.

## Model and result

Fix finitely many old types, positive integers `a_i`, and nonnegative integers `d_ij` with

```
a_i d_ij=a_j d_ji,             d_i=sum_j d_ij,
D=max_i d_i<infinity.
```

The type support may be connected as in the target application; the proof also permits disconnected support. A present factor means `d_ij>0`. At scale `N`, there are `n_i=a_i N` vertices of type `i`, and `n=sum_i n_i`. Every vertex of type `i` has `d_ij` labeled physical stubs directed at type `j`. Independently in each cross factor, choose a uniform bijection between the two stub sets. Independently in each internal factor, choose a uniform perfect pairing. Admissible scales have every internal pool `n_i d_ii` even. Loops contribute two incidences and parallel edges remain distinct.

Assume a symmetric omission certificate on the present factors:

```
q_ij=q_ji,       0<=q_ij<1/2,
sum_j d_ij q_ij=1                  at every type i.      (C)
```

Call a factor *active* when `q_ij>0`. Every physical vertex has at least three active stubs. A zero weight is allowed even when that zero is forced by all possible certificates.

Fix a prime `p`. For every old type choose finite `F_p` spaces `V_i,U_i`; zero-dimensional spaces are allowed. For each present directed factor choose an injective linear channel

`L_ij:V_j->U_i`,

which is an isomorphism when the factor is active. Opposite-direction channels need not be inverses or otherwise related. The map for a given directed type pair is used in every physical slot of that type pair. Choose arbitrary linear maps `T_i:V_i->U_i`. Count solutions to

```
sum_(stubs vu at v) L_ij(Y_u)=T_i(Y_v),    type(v)=i,
Y_v in V_i.                                            (1)
```

Write `Z_T(G_N)` for the number of solutions, including the zero solution.

**Theorem.** For every fixed set of the above data,

`sup_(N admissible) E Z_T(G_N)<infinity.`

The bound can be made uniform over the finitely many choices of channels and on-site maps on any fixed set of finite spaces satisfying the hypotheses. The same conclusion holds after conditioning every factor on simplicity, along sizes at which the required simple factors exist.

In particular, with `V_i=U_i=F_p^r`, `L_ij=Id`, and `T_i(x)=xR`,

```
sup_N E #{Y in F_p^(n by r): A_N Y=Y R}<infinity         (2)
```

for every fixed prime, dimension, and matrix `R`. The total degrees `d_i` may differ. This bounds the raw count, including deterministic planted solutions, without dividing by any subspace size or deleting exceptional configurations.

## Why the larger induction class is necessary

Consider `Dframe=[[0,3],[3,1]]` with equal type sizes. Its only omission certificate has `q_12=1/3` and `q_22=0`; thus its degrees are three and four, and an internal zero-weight factor is forced. In a common ambient vector space, a zero phase can have `H_2` properly contained in `H_1`. Its output spaces are `K_1=H_2` and `K_2=H_1`. The restricted inactive internal channel is the injection `H_2 -> H_1`. The full type support is nonbipartite but the root subspaces need not be equal.

More generally an inactive quotient channel may have a kernel even though its ambient channel and its restriction are injective. The proof below uses injectivity of active quotient channels only. This is the distinction that makes the selected certificate valid.

## Exact profiles and weighted entropy

A legal ordered star at type `i` consists of a root in `V_i` and one neighbor label in `V_j` for each of its `d_ij` slots, satisfying (1). Let `t_i(omega)` count its profiles. Let `m_ij(x,y)` pool the root-neighbor counts over slots aimed at `j`. Cross compatibility is `m_ji=m_ij^transpose`; internal compatibility means symmetry and even diagonal. On compatible arrays define

```
W_ij=product_(x,y) m_ij(x,y)!/(n_i d_ij)!          (i<j),
W_ii=[product_x (m_ii(x,x)-1)!!
      product_(x<y) m_ii(x,y)!]/(n_i d_ii-1)!!,
W=product_(present undirected factors) W_ij.            (3)
```

Set `W=0` for incompatible arrays and `(-1)!!=1`. Exactly,

`E Z_T=sum_t [product_i n_i!/product_omega t_i(omega)!] W(m).`

All roots are already assigned by these multinomials. With `alpha_i=n_i/n`, star laws `P_i=t_i/n_i`, and pooled pair laws `nu_ij=m_ij/(n_i d_ij)`, uniform factorial estimates give exponent

```
Phi=sum_i alpha_i H(P_i)
    -sum_(i<j) alpha_i d_ij H(nu_ij)
    -sum_i alpha_i d_ii H(nu_ii)/2.                    (4)
```

The log error and log number of profiles are `O(log(n+1))`, including boundary counts.

Symmetrize only slots aimed at the same old type, which have the same channel. This preserves legality and pooled pair laws. Let `G_i` be the entropy gain; it is nonnegative and zero exactly for an already symmetric star law. For the symmetric law, let `I_ij` be root-neighbor mutual information and `J_it` the conditional total correlation of all retained neighbors after omitting physical slot `t`, given the root. At every active omission the omitted label is uniquely determined. The weighted chain rule and (C) give

```
Phi = -sum_i alpha_i G_i
      -sum_(i<j) alpha_i d_ij (1-2q_ij) I_ij
      -sum_i alpha_i d_ii (1-2q_ii) I_ii/2
      -sum_i alpha_i sum_(physical slots t) q_it J_it
    <=0.                                               (5)
```

The explicit cancellation and equality proof are in [zero-phases.md](zero-phases.md). In particular every pair mutual information vanishes even at inactive factors, while `J_it=0` is required only at active omissions.

## All entropy zeros and closure

[zero-phases.md](zero-phases.md) proves that every zero, and only a zero, is specified by subspaces `H_i<=V_i`, `K_i<=U_i` and root cosets `c_i+H_i` such that

```
L_ij(H_j)=K_i                     on active factors,
L_ij(H_j) subseteq K_i             on all factors,
T_i(H_i) subseteq K_i,
T_i(c_i)-sum_j d_ij L_ij(c_j) in K_i.                 (6)
```

Each root law is uniform on its stated coset. The legal-star law is unique: take the root and all but one active neighbor independently uniformly in their cosets, then solve for the omitted label. The omitted label is uniformly distributed in its own coset, and every active omission has the required retained product law.

The proof uses three distinct active physical slots. The three corresponding retained-product identities force their image laws to be uniform cosets of one `K_i`, by an explicit fixed-sum reflection argument. Every old type occurs as an active neighbor by symmetry and unit rows, so every root law is a uniform coset. Conditioning at any active omission then forces every inactive image subspace into `K_i`. The remaining local equation gives the last two conditions in (6).

There are finitely many such phases. On restriction, root spaces become `H_i`, output spaces become `K_i`, channels become `L_ij|H_j`, and on-site maps become `T_i|H_i`. They remain in the theorem's class. If all `H_i=V_i`, any active channel forces `K_i=U_i`; this is the unique full-uniform phase. Every other phase strictly reduces `sum_i dim V_i`. In the zero-dimensional base case active isomorphisms also force all output spaces to be zero, and there is exactly one assignment.

## Central contribution with the exact normalizer

Keep separate tables for every physical slot; a table aimed at `j` has width `|V_j|`, even if other slot widths differ. Let `P` independently sample uniform legal stars, and let `Q` independently sample all roots and all neighbor slots uniformly without the local equation. One active isomorphism can absorb any other labels, so

`K_N=product_i [|V_i| product_j |V_j|^(d_ij)/|U_i|]^(n_i)`

is the number of legal-star choices. Exact counting gives `E Z_T=K_N E_P W` and

```
K_N E_Q W=product_i (|V_i|/|U_i|)^(n_i)=1.              (7)
```

Indeed, active isomorphisms give `log|U_i|=sum_j d_ij q_ij log|V_j|`. Reversibility, symmetry, and both unit-row budgets yield

`sum_i n_i log|U_i|=sum_j n_j log|V_j|`.

Thus `nu_N(m)=K_N Q(M=m)W(m)` is exactly the distribution of full physical-slot tables from a random configuration with iid uniform root labels. This is an identity, not an asymptotic normalization.

[central-channel.md](central-channel.md) proves the full heterogeneous local estimate. A third active slot can absorb the constraint after fixing any two neighbor labels; hence the means and covariance of full tables agree under `P,Q`. Conditional variance on the common-root-row table space proves positivity even with different slot widths. A complete circle-character argument gives the maximal legal support-difference lattice index

`I_*=product_i |U_i|^(|V_i|)`.

For the full-table deviation `Delta` from its independent mean, relative tilted Fourier inversion, with all lattice covolumes retained, gives on a fixed neighborhood

`P(M=m)/Q(M=m)<=C I_* exp(C ||Delta||^3/n^2)`.

The ratio is `I_*(1+o(1))` in the `sqrt(n)log n` window. Under the exactly normalized weighted law, permutation exposure and iid root-label exposure give `nu_N(||Delta||>=t)<=C exp(-ct^2/n)` for `t>=C0 sqrt(n)`. Internal-loop mean bias is `O(1)`. Choosing the fixed neighborhood small enough lets this tail integrate the cubic likelihood ratio outside the logarithmic window. Consequently the expected contribution from the full-uniform physical-table neighborhood has limsup at most `I_*`. No entropy-only central estimate or common-width determinant formula is used.

## Proper phases and the selected sparse certificate

Fix a proper phase (6), quotient its roots by `H_i` and its outputs by `K_i`, and subtract the type-constant quotient coset point. The resulting defect is a homogeneous quotient solution. Active quotient channels are isomorphisms; inactive quotient channels need not be injective.

For its nonzero support `S`, first select all active edges incident to `S`. At every outside vertex with exactly one active incidence from `S`, that incidence contributes nonzero, so its zero-root equation forces a further, inactive incidence from `S` with nonzero contribution. Select one such cancellation edge. No new outside vertex is added by this choice. Vertices with at least two active incidences need no extra edge. Every selected outside vertex now has at least two selected incidences, and every vertex of `S` has at least three selected incidences.

Writing `s=|S|`, `t` for the number of selected outside vertices, `a` for selected internal support edges and `b` for selected boundary edges, we have

```
2a+b>=3s,   b>=2t,   E=a+b<=Ds,
E-(s+t)>=s/2.                                         (8)
```

Loops count twice in the first degree inequality and once in `a`. Multiplicities are retained. Unselected inactive stubs are unrestricted; no absent-edge condition is asserted.

For a fixed quotient assignment its full lifts form an empty fiber or a translate of the homogeneous restricted kernel, counted by `Z_H(G)`. To control correlation, a prescribed cross pair is forced by one image swap, and an internal pair by one two-edge switch. Exact equal-preimage counts give the configuration law conditioned on the prescribed certificate after at most `E` switches. At most `4E` physical rows change. For `r_out=max_i dim U_i`,

`E[Z_H | certificate]<=p^(4 r_out E) E Z_H`.

The full proof and the weighted enumeration are in [boundary-channel.md](boundary-channel.md). Choosing support/exterior vertices, quotient labels, selected support and exterior stubs, and their pairings costs at most

`[n^(s+t)/(s!t!)] p^(r_root s) 2^(D(s+t)) (2Ds)^E`.

Every prescribed edge has conditional probability at most `C/n` for `s<=epsilon n`. The factor `2^(Ds)` explicitly counts unsaturated inactive support stubs. Absorb the rank charge and all fixed factors into `B^s`. By (8), summing over `t,E` gives

```
E #{solutions with s quotient defects}
 <= E Z_H * B^s (s/n)^(s/2),      1<=s<=epsilon n.      (9)
```

Choose fixed `epsilon` so successive terms decrease geometrically. Their sum, starting at `s=1`, is `O(n^-1/2) E Z_H`. The zero-defect contribution is at most `E Z_H` by the affine-fiber fact. Singleton supports are not omitted.

## Completing the proof and fixed powers

Induct on `sum_i dim V_i` within the stated channel class. The base case has one assignment. Every proper phase has lower root dimension and satisfies the same channel hypotheses, so its root-coset neighborhood is bounded by the induction hypothesis and (9). The full-uniform neighborhood is bounded by the central theorem. Choose strict smaller neighborhoods inside the proved bounds; these are open and cover every entropy zero. The complement in the compact feasible-profile space therefore has strictly negative maximum entropy. The exact type formula bounds it by `poly(n) exp(-c n)`.

This proves finite limsup for the fixed system, and then a finite supremum since each of the finitely many smaller admissible sizes has finite count. All parameters at fixed finite spaces have finitely many choices. Optional simplicity conditioning costs a bounded factor: the finitely many fixed-degree factors have a positive limiting joint simplicity probability and uniform simple projections. This uses no change-of-model inference for an unbounded observable.

Finally, `Z_T(G)^s` is the solution count in the direct sum of `s` copies of all spaces and maps. The hypotheses persist, so all fixed powers are bounded. For (2), this is equivalently the block-diagonal target with `s` copies of `R`.

The moment estimate can therefore supply the bounded exponential-nullity factor needed by a separately certified expected near-quadratic kernel/enumeration algorithm. The one-hot gap, identifiability, sparse right-kernel computation, and charged bit-work accounting are separate inputs; no new algorithmic claim is proved in this packet.
