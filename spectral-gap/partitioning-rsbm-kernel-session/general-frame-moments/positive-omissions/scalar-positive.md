# Sharp scalar moments under a positive-omission certificate

This is a separate scalar corollary for the mixed-degree extension. The earlier regular-frame packet is frozen and is not edited. The proof below identifies exactly which central and integer-lattice steps survive, supplies the weighted scalar phase argument and point-neighborhood bound, and states the resulting real-multiplicity consequence. Historical novelty and a quantitative growing-prime estimate are not asserted.

## 1. Model and statements

Fix a connected reversible integer frame `D=(d_ij)` with positive integer size multipliers `a_i`:

```
a_i d_ij=a_j d_ji,
d_i=sum_j d_ij,
Dmax=max_i d_i.
```

At scale `N`, type `i` has `n_i=a_i N` vertices, each with `d_ij` labeled physical stubs aimed at `j`. Factors are independent uniform cross-stub bijections and internal stub pairings, with all internal pool sizes even. Loops and parallel edges are retained; a loop contributes two adjacency incidences. Assume the old support is **nonbipartite**, with a self-incidence whenever `d_ii>0`.

Assume symmetric weights on every active factor, including internal ones, satisfying

```
0<theta_ij=theta_ji<1/2,
sum_j d_ij theta_ij=1 for every i.                       (P)
```

In particular `dmin=min_i d_i>=3`. Fix an odd prime `p` and scalar `lambda in F_p`; write

`t_p=dim_Fp ker(D-lambda I)`.

**Sharp scalar theorem.** In the unconditioned configuration model, along every admissible scale,

`E |ker_Fp(A_N-lambda I)|=2p^{t_p}+o_(D,a,p)(1)`.         `(1)`

No avoidance condition on degrees or type-size multipliers is needed. The prime is fixed before `N` tends to infinity. The moment formula itself is not claimed unchanged after conditioning on simplicity.

**Real multiplicity corollary.** For every fixed integer `ell`, put

`t_R=dim_R ker(D-ell I)`.

Then

```
P(dim_R ker(A_N-ell I)=t_R)->1                           (2)
```

both in the configuration law and after direct conditioning of all factors on simplicity. This uses primes for which the old integer matrix has the same rank modulo the prime as over the rationals. The statement covers only frames satisfying `(P)` with nonbipartite old support; it is not an assertion for all minimum-degree-three frames or for certificates allowing zero weights.

## 2. Exact type entropy and the complete scalar zero phases

Record the root and every ordered physical neighbor label at a vertex. Let `P_i` be its empirical star law supported on `sum_s y_s=lambda x`, `mu_i` its root law, and `nu_ij` the pooled pair law over slots aimed at `j`. The exact pairing/bijection type contribution is the product of star multinomials with the cross factorial weights and internal double-factorial weights from `central-positive.md`. Uniform Stirling estimates give exponent

```
Phi=sum_i a_i H(P_i)
    -sum_(i<j) a_i d_ij H(nu_ij)
    -sum_i (a_i d_ii/2) H(nu_ii),                        (3)
```

with a uniform `O(log(N+1))` error in its logarithm and polynomially many types. Roots are counted exactly once by the star multinomials. These statements include zero entries, internal parity, loops, and multiple edges.

Symmetrize only slots with the same target old type; it preserves the local equation and pooled tables and increases star entropy. Its entropy gain vanishes only if the original law already equals its symmetrization. At a symmetrized star, let `I_ij` be root-neighbor mutual information for a slot aimed at `j`, and let `J_i,s` be the conditional total correlation of all retained neighbors given the root after slot `s` is omitted.

Average the omitted-slot chain-rule identity with the **physical-slot weights** `theta_i,s=theta_ij`. Their sum is one by `(P)`. The root coefficient before subtracting the edge entropies is

```
a_j + sum_i a_i d_ij(1-theta_ij)
 =a_j + a_j sum_i d_ji(1-theta_ji)
 =a_j d_j,
```

so it cancels exactly even though the `d_j` differ. The result is

```
Phi=-sum_(i<j) a_i d_ij(1-2theta_ij) I_ij
    -sum_i (a_i d_ii/2)(1-2theta_ii) I_ii
    -sum_i a_i sum_(physical slots s) theta_i,s J_i,s
 <=0.                                                  (4)
```

Every displayed coefficient at an active factor or slot is strictly positive. Therefore `Phi=0` forces all pair mutual informations and **all** omission defects to vanish, including slots on repeated old-type factors. The same is true before symmetrization because zero entropy leaves no symmetrization gain.

At such a zero, condition on a root. Every retained `d_i-1` neighbor tuple is its root-independent product law, and the full neighbor sum is fixed. Since `d_i>=3`, the finite-group lemma forces every one-coordinate law to be uniform on an affine coset of one common neighbor subspace. To recall its proof, condition the other `d_i-2` neighbors to support values. The remaining two marginals are unchanged and are reflected translates, so their support-difference spaces agree. Vary a third conditioned coordinate; composing the reflection identities gives invariance by all support differences. Invariance makes each law uniform on the full coset.

Matching feasibility makes the neighbor law at a slot aimed at `j` the root law at `j`. Thus the root support-difference subspaces agree along old even walks. Connected nonbipartite support, including self-incidences from internal factors, has one even-walk component. In the scalar alphabet `F_p` the common subspace is either zero or the whole field.

The full-field phase is the unique full-uniform legal star family. The zero-subspace phases are the type-constant maps `c=(c_i)` satisfying

`Dc=lambda c`.                                         `(5)`

There are exactly `p^{t_p}` of them. Their legal stars are deterministic. These are all zero phases; no regularity of the row totals was used in this classification.

## 3. The central input with local degrees

The actual central theorem is `central-positive.md`, not a regular-degree substitution. It proves the following needed facts for the full physical-slot tables `M`:

1. The exact paired/bijected weight `W` depends on pooled tables but retains all internal symmetries and even diagonal constraints.
2. If `P_N` samples uniform legal stars and `Q_N` samples root and all neighbors independently, then

   `E Z=K_N E_P W`, `K_N E_Q W=1`,

   where in this common scalar alphabet `K_N=p^{sum_i d_i n_i}`. This normalizer holds for any local degree sequence. The two-space version, needed for a full vector induction, is also proved there using the size balance implied by `(P)`.
3. The local covariance is the same under both laws and equals

   `Sigma_i=p^{-2}[Id+(d_i-1)Pi_row,i]`.

   It is positive on the common-row physical-table space because `d_i>=3`. The maximal legal local lattice index is `p^p`, independent of `d_i`; the global index is `I_*=p^{kp}`.
4. Uniform compact-tilt Fourier inversion gives a relative local limit estimate. The likelihood ratio equals `I_*(1+o(1))` on the legal affine lattice in the `sqrt(N)log N` window and is at most `C I_* exp(C||Delta||^3/N^2)` throughout a fixed small neighborhood.
5. The normalized weighted reference law

   `nu_N(m)=K_N Q_N(M=m)W(m)`

   is exactly configuration followed by iid uniform root labels. Its full-table deviations are subgaussian at scale `sqrt(N)`, using `Dmax` in the bounded-difference constants and an `O(1)` internal-loop bias. The cubic likelihood bound is integrable against that exact reference law. Its fixed-neighborhood annulus outside the logarithmic window contributes `o(1)`.

None of these facts needs a common total degree. The local means, positive covariance, maximal lattices, fixed-neighborhood relative estimate, and weighted reference tail have all been proved for the actual mixed-degree law in that note.

## 4. Actual compatible integer lattice and equal coset masses

Let `L0` be the unrestricted integer direction lattice: every physical-slot table has total zero and all slots at old type `i` share a common integer root-row direction `r_i` of total zero. For a full direction `z`, let `z_ij` be its pooled table. Define the compatible subgroup `K0` by

```
z_ji=z_ij^T,
z_ii=z_ii^T with even diagonal for internal pools.       (6)
```

The legal difference lattice is `L=ker C`, where

```
C_i,x(z)=sum_s sum_y y z_i,s(x,y)-lambda x r_i(x)
                                           in F_p.      (7)
```

The complete local character argument in `central-positive.md` proves `[L0:L]=p^{kp}=I_*`; `(7)` gives every period, not just necessary conditions.

At every admissible size the all-zero root/neighbor array `m0(N)` is both legal and pairing-compatible. Therefore the unrestricted compatible affine lattice is `m0(N)+K0`, while the legal one is `m0(N)+(K0 intersect L)`. Put

`J_*=[K0:K0 intersect L]=|C(K0)|`.

For every fixed `z in K0`, uniformly in the logarithmic central window,

`nu_N(m+z)/nu_N(m)=1+o(1)`.                             `(8)`

The unrestricted local probability ratio follows from the relative local limit estimate, since all type sizes are fixed positive multiples of `N` and the shift is bounded. For a cross weight, the factorial ratio has leading power

`(n_i d_ij/p^2)^{sum_(x,y) z_ij(x,y)}=1`.

For an internal weight, diagonal shifts are even and the double-factorial powers plus off-diagonal factorial powers have total exponent

`sum_x z_ii(x,x)/2+sum_(x<y)z_ii(x,y)
  =(sum_(x,y)z_ii(x,y))/2=0`.

Thus its weight ratio also tends uniformly to one. All physical and pooled entries in the window are positive of order `N`; fixed compatible translations preserve nonnegativity and parity for large sizes. Positive local masses on the relevant affine lattice points are part of the relative local estimate.

By weighted-reference concentration, `(8)` implies asymptotic total-variation invariance under every fixed `K0` translation, extending probabilities by zero off their actual finite support. A direct proof sums the uniform ratio error on an inner logarithmic window and bounds both complements by the subgaussian tail; a fixed translation changes its radius by only a fixed amount.

Translations by fixed representatives of the finite quotient `K0/(K0 intersect L)` consequently make all its affine coset masses equal up to `o(1)`. They sum to one, so the legal coset has mass `1/J_*+o(1)`. The legal/unrestricted central ratio and the vanishing annulus then give exact full-uniform expected contribution

`I_*/J_*+o(1)`.                                        `(9)`

This is equidistribution in the actual integer quotient. It does not assume that a pooled real constraint space is saturated modulo `p`, and it uses no common row degree.

## 5. Computing the scalar congruence image with arbitrary multiplicities

Pair `C(K0)` with functions `h_i:F_p->F_p`. For every positive cross factor, a pooled zero-margin two-by-two interaction and its transpose can be placed in one physical slot of each direction, with every other slot zero. Such directions belong to `K0` regardless of `d_ij mod p`. Annihilation forces

```
[h_i(x)-h_i(x')](y-y')
 +[h_j(y)-h_j(y')](x-x')=0.
```

Anchoring at zero and one yields `h_i(x)=s_i x+c_i`, with `s_i+s_j=0` along cross old edges.

For an internal factor, use twice the symmetric interaction with diagonal `+1` at `(x,x),(y,y)` and off-diagonal `-1` at `(x,y),(y,x)`. It has zero row margins and even diagonal, so it is a genuine `K0` direction in one physical slot. It gives

`2[h_i(x)-h_i(y)](x-y)=0`.

Odd characteristic forces `h_i` constant. An odd cross cycle similarly kills alternating slopes. Connected nonbipartite support therefore makes all annihilator functions constant: `h_i(x)=c_i`.

Their functional on a compatible direction is

`sum_i [(D-lambda I)c]_i sum_x x r_i(x)`.                `(10)`

The root margins in `(10)` are genuinely free modulo `p`. Here is an explicit integer construction, retaining every multiplicity and internal parity. Choose arbitrary integer zero-total vectors `r_i` and realize twice them. For a cross pool choose a table with row margins `2d_ij r_i` and column margins `2d_ji r_j`, using label zero as an anchor. For an internal pool take the diagonal table with entries `2d_ii r_i(x)`. It is symmetric with even diagonal. Split every pooled table into its `d_ij` physical-slot tables, each with row margin `2r_i`: use `d_ij-1` anchor-column tables and put the residual in the last slot. All slot totals are zero. Negative entries are permitted in a direction.

Doing this independently for every active factor gives an actual direction in `K0`. Because two is invertible modulo `p`, each root moment `sum_x x r_i(x)` can be varied independently over `F_p`. Thus `(10)` vanishes exactly when `(D-lambda I)c=0`. Conversely those coefficient vectors annihilate every compatible direction by the pooled column-margin identities.

The annihilator dimension is exactly `t_p`, so

```
J_*=p^{kp-t_p},
I_*/J_*=p^{t_p}.                                       (11)
```

The argument divided by no degree or size multiplier. Its only characteristic restriction is that `p` be odd. Combining `(9)` and `(11)` computes the full-uniform contribution as `p^{t_p}+o(1)`.

## 6. Point neighborhoods and the complementary entropy region

Each point phase `c` from `(5)` is an exact type-constant labeling of every configuration. Subtract it from any nearby solution. The difference is a homogeneous scalar solution supported on the set `S` of defect vertices. At an exterior zero vertex, a single incident support stub would contribute one nonzero value and cannot vanish, so every reached exterior vertex receives at least two support incidences, counted with multiplicity.

Write `s=|S|`, `i` for certificate edges within `S` (loops once), `j` for boundary edges, and `u` for distinct exterior vertices. The certificate includes every stub at `S`. Then

```
sum_(v in S) d_type(v)=2i+j,
u<=j/2,
E=i+j<=Dmax s,
E-(s+u)>=((dmin-2)/2)s=alpha s,      alpha>0.            (12)
```

Every positive stub pool has size at least a fixed positive multiple of `N`. For `s<=epsilon N`, forcing a valid certificate of `E` stub pairs therefore has probability at most `(C/N)^E`, directly from reciprocal pairing or bijection falling factorials.

For completeness, its first-moment enumeration chooses support and exterior vertices in at most `(C N)^{s+u}/(s!u!)` ways, nonzero support values in at most `p^s` ways, exterior stubs in at most `2^{Dmax u}` ways, and a pairing of the selected at most `2Dmax s` stubs in at most `(2Dmax s)^E` ways. Invalid directions or multiplicities can be discarded. Summing edge counts and absorbing fixed factors gives

```
E #{solutions with exactly s defects from c}
 <=Dmax s B^s (s/N)^{alpha s}.                          (13)
```

Indeed, the remaining powers are

`s^E N^{s+u-E}/(s!u!)
 =(s/N)^{E-s-u}(s^s/s!)(s^u/u!)`,

use `(12)`, `s^s/s!<=e^s`, and sum `s^u/u!<=e^s`. Choose `epsilon` sufficiently small that the terms decrease geometrically. Sum from `s=1`, retaining configuration singleton supports, to obtain `O(N^-alpha)` extra expected solutions near each point phase. The zero-defect contribution is exactly one. No correlation with a residual kernel is at issue here because a scalar point phase has zero-dimensional restricted alphabet; this is also the point specialization of the general boundary proof.

There are finitely many point phases. Take their root-defect neighborhoods disjoint, with radius less than one quarter of the smallest class-size coefficient, and shrink the central full-table neighborhood to be disjoint from them. The finite phase classification in Section 2 covers every zero of `(3)`. On the remaining compact feasible profile region the continuous entropy exponent is strictly negative. The exact type formula therefore bounds that complementary sum by `poly(N)exp(-cN)=o(1)`.

Adding the full-uniform contribution `p^{t_p}+o(1)`, the `p^{t_p}` point contributions `1+o(1)`, and the vanishing complement proves `(1)` for the actual mixed-degree configuration frame.

## 7. Real multiplicity at a fixed integer and direct simplicity conditioning

Fix an integer `ell` and let `rho=rank_Q(D-ell I)`, so `t_R=k-rho`. If `rho>0`, choose one nonzero integer minor of order `rho`; let its nonzero determinant be `M`. If `rho=0`, take `M=1`. Every larger minor vanishes identically as an integer. Therefore for every prime not dividing `M`,

`dim_Fp ker(D-ell I)=t_R`.

There are arbitrarily large odd such primes. Fix one before taking the size limit, and apply `(1)` at the reduction of `ell`.

The type-constant lift of an old real or modular solution is injective because every old type has at least one vertex. It intertwines `D` with `A_N` exactly: every physical vertex has the specified `d_ij` incidences, including loop incidences. Consequently real nullity is deterministically at least `t_R`, and over the selected prime the finite-field kernel contains a deterministic old subspace of `p^{t_R}` vectors.

Real nullity at least `t_R+1` forces modular nullity at least `t_R+1` by vanishing integer minors. Thus, subtracting the deterministic old modular subspace from the expectation,

```
P_config(real nullity>=t_R+1)
 <= [E |ker_Fp(A_N-ell I)|-p^{t_R}]
                      /[p^{t_R}(p-1)],

limsup_N P_config(real nullity>=t_R+1)<=1/(p-1).         (14)
```

Let these fixed primes tend to infinity. This proves `(2)` in the configuration law. The argument also covers `t_R=0`, when the deterministic old subspace consists only of the zero vector.

Each independent fixed-degree factor has a positive limiting probability of being simple along its admissible scales. Their finite product is bounded below by a positive constant depending only on the frame, not on the prime. Condition the already-proved vanishing real-failure event on this simplicity event. Each simple factor has a constant number of labeled-stub representations, so the conditional laws are exactly the intended independent uniform simple internal regular and cross biregular factors. This proves the uniform-simple version of `(2)`.

No exact fixed-prime moment is asserted after simplicity conditioning, no growing-prime uniformity has been used, and no polynomial real failure rate is obtained here. The certificate `(P)` remains part of the theorem; broader zero-weight omission classes and arbitrary minimum-degree-three frames are not silently included.
