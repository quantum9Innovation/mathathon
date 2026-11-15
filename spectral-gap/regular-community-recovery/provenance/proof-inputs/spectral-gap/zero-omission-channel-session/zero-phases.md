# Exact entropy zeros for heterogeneous channel systems with zero omission weights

Derived independently from the actual candidate on 2026-11-15. This module proves the entropy identity, the complete zero-phase classification, and closure of the induction class. It does not infer a bounded moment from entropy alone. The central physical-table estimate and the sparse boundary estimate are separate inputs.

## 1. Model and notation

Fix old types `i=1,...,k`, positive proportions `alpha_i`, and nonnegative integer incidence counts `d_ij`. Assume `alpha_i d_ij=alpha_j d_ji`, and put `d_i=sum_j d_ij`. The type support is allowed to have internal factors. Fix real omission weights on present factors satisfying

```
q_ij=q_ji,       0<=q_ij<1/2,
sum_j d_ij q_ij=1.                                      (1)
```

Call a factor or physical slot **active** when its `q` weight is positive. This use of “active” refers to the omission certificate; “present” means `d_ij>0`. Every vertex has at least three active physical slots: a sum of at most two numbers strictly below `1/2` is strictly below one. The active old-type support need not be connected.

For a fixed prime `p`, let `V_i,U_i` be finite-dimensional `F_p` vector spaces. At every present ordered factor fix an injective linear channel `L_ij:V_j->U_i`, the same on all slots with old target `j`. Require `L_ij` to be an isomorphism onto `U_i` on every active factor. Fix an arbitrary linear map `T_i:V_i->U_i`. A legal ordered star at old type `i` is

```
(X_i,(Y_is)_(s in S_i)),
X_i in V_i,   Y_is in V_j(s),
sum_(s in S_i) L_i,j(s)(Y_is)=T_i(X_i),                 (2)
```

where `S_i` is the set of its `d_i` labeled physical slots. Repeated old targets are repeated coordinates. Internal loops will have two physical incidences in the configuration model; they require no modification of (2).

Let `P_i` be a probability law on legal stars, and let `mu_i` be its root law. For a present ordered factor, let `nu_ij` be the root-neighbor pair law pooled over its `d_ij` slots. Feasibility means

```
nu_ji=nu_ij^transpose  for i!=j,
nu_ii=nu_ii^transpose  for an internal factor.           (3)
```

In particular, `nu_ij` has marginals `mu_i,mu_j`, including two copies of `mu_i` internally. Write

```
w_ij=alpha_i d_ij            (i<j),
w_ii=alpha_i d_ii/2,
Phi(P)=sum_i alpha_i H(P_i)
       -sum_(i<=j,present) w_ij H(nu_ij).               (4)
```

This is the finite-alphabet configuration type exponent; the root entropy is already in `H(P_i)`. All entropies use natural logarithms.

## 2. Repeated-slot symmetrization and the exact weighted identity

Average `P_i` over all permutations of slots with the same old target, obtaining `Pbar_i`. This preserves (2), since the channels agree on those slots, and preserves every pooled pair table. Define the nonnegative symmetrization loss

```
Delta_i=H(Pbar_i)-H(P_i)>=0.                            (5)
```

Strict concavity of entropy gives `Delta_i=0` exactly when `P_i=Pbar_i`. Thus

```
Phi(P)=Phi(Pbar)-sum_i alpha_i Delta_i.                 (6)
```

For `Pbar_i`, the pair law at each slot aimed at `j` is exactly `nu_ij`. Put `I_ij=I_nu_ij(X;Y)`. For omission of slot `t`, let

```
J_it=sum_(s!=t) H(Y_is|X_i)
      -H((Y_is)_(s!=t)|X_i)>=0.                        (7)
```

Because `L_i,j(t)` is injective, the root and all retained coordinates determine the omitted neighbor on legal stars. Therefore, for each omission `t`,

```
H(Pbar_i)=H(mu_i)+sum_(s!=t) H(Y_is|X_i)-J_it.
```

Averaging with weights `q_it=q_i,j(t)`, whose physical sum is one, gives

```
H(Pbar_i)
 =H(mu_i)+sum_s(1-q_is)H(Y_is|X_i)-sum_t q_it J_it
 =(2-d_i)H(mu_i)
   +sum_j d_ij(1-q_ij)H(nu_ij)-sum_t q_it J_it.         (8)
```

Only active omissions have positive averaging weight; no assertion is made that an inactive `J_it` vanishes.

Insert (8) in (4). On each cross factor the two directed star terms minus its matching entropy give `w_ij(1-2q_ij)H(nu_ij)`. Internally the one star term minus half the matching entropy gives `w_ii(1-2q_ii)H(nu_ii)`. Expand `H(nu_ij)=H(mu_i)+H(mu_j)-I_ij`, with both root-entropy copies retained internally. The coefficient at `H(mu_i)` is

```
alpha_i[(2-d_i)+sum_j d_ij(1-2q_ij)]
 =alpha_i[2-2 sum_j d_ij q_ij]=0.
```

Consequently the exact identity for arbitrary, possibly unsymmetrized feasible stars is

```
Phi(P)
 =-sum_i alpha_i Delta_i
  -sum_(i<=j,present) w_ij(1-2q_ij) I_ij
  -sum_i alpha_i sum_(physical t) q_it J_it <=0.        (9)
```

Here the `J_it` and `I_ij` are those of `Pbar`. All mutual-information coefficients are strictly positive, including when `q_ij=0`. Thus equality holds exactly when every star is symmetric, every present pair is a product `mu_i tensor mu_j`, and every **active** retained-neighbor tuple is a product conditional on the root. The proof divided no finite-field element by a degree, omission weight, or incidence multiplicity.

## 3. An elementary three-coordinate lemma

Let `A,B,C` take values in a finite `F_p` vector space `U`, with `A+B+C=b` almost surely. If each of the three pair marginals is the product of its one-coordinate marginals, then their laws are uniform on cosets of one common subspace `K<=U`.

For a support point `a` of `A`, pair independence gives the original one-coordinate laws for both `B` and `C` conditional on `A=a`. The deterministic sum then gives, for every `z in U`,

```
mu_B(z)=mu_C(b-a-z).                                   (10)
```

The analogous relations conditioning on support points of `B,C` show that all three support-difference spaces are equal; denote the common space by `K`. Comparing (10) for `a,a'` shows that `mu_C` is invariant under translation by `a-a'`. These differences span `K`, so `mu_C` is invariant under every element of `K`. Its support is contained in one coset of `K` by definition of support-difference space. Therefore it is uniform on that entire coset. The reflected translates in (10) make `mu_B` and then `mu_A` uniform on cosets of the same `K`. This includes `K=0`.

The span of support differences is exactly the additive subgroup they generate: every additive subgroup of an `F_p` vector space is an `F_p` subspace. No positivity assumption outside the supports is used.

## 4. Three active omissions determine all active image laws

Suppose now that `Phi=0`. At old type `i`, condition on any root support point `X_i=x`. Put `Z_s=L_i,j(s)(Y_is)`, regarded as a variable in `U_i`. Pair independence in (9) makes the one-coordinate law of `Y_is` equal to `mu_j(s)`, independently of `x`. Applying coordinatewise injective maps preserves all retained-product identities.

Choose three active physical slots `a,b,c`. Let `W` denote all other neighbor coordinates. By omitting `a`, `b`, or `c` in turn, the corresponding retained laws are products. For every `w` in the product support of `W`, its event has positive probability, and conditional on `W=w` the three pair laws `(Z_b,Z_c)`, `(Z_a,Z_c)`, `(Z_a,Z_b)` are their original product laws. Equation (2) fixes their sum to

```
T_i(x)-sum_(s notin {a,b,c}) Z_s(w).
```

The preceding lemma therefore shows that the three active image marginals are uniform on cosets of one common subspace. These are the original marginals, independent of both `x` and `w`.

Fix two active slots and apply this argument with each further active slot as the third. It follows that **every** active image law at old type `i` is uniform on a coset of one common subspace `K_i<=U_i`. The subspace is its uniquely determined support-difference space. This proof uses physical coordinates, so three active slots aimed at the same old type are fully sufficient.

Every old type `j` occurs as an active neighbor of some old type. Indeed, its unit row in (1) contains an active outgoing slot toward some `i`; reversibility makes the opposite incidence present, and symmetry makes its omission weight positive. Since that channel `L_ij` is an isomorphism, its uniform image law pulls back to a uniform root law. Hence there exist uniquely determined subspaces and cosets

```
H_j<=V_j,      C_j=a_j+H_j,
mu_j=Uniform(C_j),                                     (11)
```

and on every active ordered factor

```
L_ij(H_j)=K_i.                                         (12)
```

This argument does not require the active support to be connected.

## 5. Inactive inclusions and the on-site condition

All root laws are now known to be uniform cosets, so at any type `i` the image law at any physical slot `s`, active or inactive, is uniform on

```
L_i,j(s)(a_j(s))+L_i,j(s)(H_j(s)).
```

Fix one active omitted slot `t` and a root support point `x`. Its retained variables are independent by `J_it=0` and include at least one further active slot. The support of their sum is therefore a coset of

```
K_i+sum_(inactive physical s) L_i,j(s)(H_j(s)).          (13)
```

The local equation identifies that sum with `T_i(x)-Z_t`, whose support is a coset of `K_i`. Equality of these supports forces

```
L_ij(H_j) subseteq K_i   on every inactive factor.      (14)
```

Together with (12), all neighbor support differences lie in `K_i`. The local equation at every root support point then gives

```
T_i(H_i) subseteq K_i,
T_i(a_i)-sum_j d_ij L_ij(a_j) in K_i.                  (15)
```

The second expression is independent of the choice of representatives modulo `K_i`, by the first inclusion and (12)--(14). Incidences and scalars `d_ij` in (15) are interpreted inside the field; no assumption that any degree is nonzero modulo `p` is needed.

## 6. Converse, uniqueness, and finiteness

Conversely, fix subspaces `H_i<=V_i`, `K_i<=U_i`, and cosets `a_i+H_i` satisfying (12), (14), and (15). Choose the root uniformly on its coset. Choose the neighbors except one fixed active slot `t` independently uniformly on their root cosets. Solve (2) for the omitted coordinate using the active isomorphism. Conditions (12)--(15) put the result in its required coset.

The resulting star is uniform on its entire legal affine support, whose size is

```
|H_i| product_(physical s) |H_j(s)| / |K_i|.            (16)
```

For any active omission `u`, specifying the root and every neighbor except `u` gives exactly one legal star. The retained tuples are therefore product uniform for every active omission. For any physical slot `s`, choose a different active omission; then the root and that neighbor are independent. Thus all present pair laws are `Uniform(a_i+H_i) tensor Uniform(a_j+H_j)`, satisfy (3), and all entropy terms in (9) vanish. The star laws are symmetric under repeated-target slot permutations because their legal affine supports and uniform measures are invariant.

This star law is unique for the specified cosets and subspaces: at entropy zero the root and any active retained tuple already have the product uniform law, and determine the omitted coordinate. Conversely `H_i`, the root coset, and `K_i` are determined by the marginal laws of that star, so there is no continuous family hidden in the representation.

All choices are finite at fixed finite spaces. Therefore (11)--(15), together with their uniquely uniform legal-star laws, classify **every** feasible entropy-zero phase.

## 7. Closure and strict dimension descent

For a phase define

```
V_i'=H_i,       U_i'=K_i,
L_ij'=L_ij|_(H_j),       T_i'=T_i|_(H_i).               (17)
```

Equations (12)--(15) make these maps well-defined. Every restricted channel is injective, and every active restricted channel is an isomorphism onto `K_i`. The frame and omission weights do not change. Thus the homogeneous restricted problem lies in exactly the same heterogeneous channel class.

Use induction parameter `sum_i dim V_i`. If every `H_i=V_i`, any active isomorphism in row `i` gives `K_i=U_i`. Every root coset is then the whole `V_i`, and the unique star laws are the full uniform legal-star laws. This full phase is always valid: all remaining inclusions and offset conditions are automatic in their ambient spaces. Any other phase has at least one proper `H_i` and strictly decreases the parameter in (17).

At parameter zero every root space is zero. The existence of an active isomorphism in every row also makes every output space zero. There is exactly one global assignment, and the base moment is one.

These are phase and closure statements only. Bounds on neighborhoods of proper phases still require the separate sparse-certificate argument, in particular because an inactive induced map `V_j/H_j -> U_i/K_i` can have a kernel.

## Read-only provenance

The actual candidate and preceding regular proof were read without edits. Their SHA256 values when read were:

```
fbc5df08244c013a5e5102fc3af486047559d0b98319a70ff807b3d118925442  spectral-gap/zero-omission-channel-moment-root.txt
cbfd5c6c8372bbbb1a4e2ef01426bfd93225e54cc7842e9efadc7802fe07f5e4  spectral-gap/partitioning-rsbm-kernel-session/general-frame-moments/boundary-frame.md
6c6da08c6d944e1f9cd76706f08b660fb9be82579549fbae347404e8b99e7e0b  spectral-gap/partitioning-rsbm-kernel-session/general-frame-moments/bounded-frame-moment-theorem.md
```

All changes for this module are confined to `spectral-gap/zero-omission-channel-session/`.
