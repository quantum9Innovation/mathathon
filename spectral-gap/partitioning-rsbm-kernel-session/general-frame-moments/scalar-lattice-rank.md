# Scalar compatible-lattice rank for nonbipartite regular frames

Prepared 2026-11-15. This note proves the scalar lattice-rank calculation directly for physical-slot tables in a general regular configuration frame. It includes internal pairings, repeated neighbor-type slots, unequal old-type sizes, and multiplicities divisible by the field characteristic. The final sharp-moment consequence uses the central relative local limit/concentration estimates and boundary estimate as separately identified inputs.

Throughout, `p` is an odd prime, the scalar target is `lambda in F_p`, and `Q=(q_ij)` is the fixed integer old-type matrix. Its row totals are a common `d>=3`. The support of `Q` is connected and nonbipartite, with an old loop whenever `q_ii>0`. Old sizes satisfy `n_i q_ij=n_j q_ji`, and every internal pool `n_i q_ii` is even. The type count `k` and all degrees are fixed.

## 1. Integer direction lattices and the legal congruences

For each physical slot `s` at old type `i`, use a `p by p` root-neighbor table `m_i,s(a,b)`. An integer direction array belongs to `L0` when every physical table has total zero and all tables at type `i` have one common row-margin vector `r_i(a)`, with `sum_a r_i(a)=0`.

This is the full difference lattice of the independent-star law `Q_ind`: within a fixed root row, change the neighbor label in one slot to generate all within-row transfers; changing the root with all neighbors equal to zero generates every common-row transfer. The old class sizes do not restrict these directions beyond the zero total.

Let `M_ij` be the sum of the physical-slot tables targeting type `j`. Define the compatible integer direction lattice `K0<=L0` by

```
M_ji=M_ij^T for i!=j,
M_ii=M_ii^T and every diagonal entry of M_ii is even.
```

The internal diagonal condition is necessary because each paired equal-label stub pair contributes two diagonal incidences. It must be retained over the integers even though `p` is odd.

The legal-star lattice `L<=L0` is the kernel of the `kp` congruences

```
C_i,a(m)=sum_s sum_b b m_i,s(a,b)-lambda a r_i(a) in F_p. (1)
```

Here integer labels are reduced modulo `p`; the coefficient `r_i(a)` is the common row-margin direction, not a sum over all slots. The index is

```
[L0:L]=p^(kp).                                          (2)
```

For completeness, these congruences give the entire maximal lattice, not just necessary conditions. A circle-valued character constant on the legal local support can be represented by row functions `theta_s(a,b)`. At a fixed root `a`, varying two neighbor labels while a third compensates in `sum_s b_s=lambda a` gives the additive Cauchy equation. Since `d>=3`, all slot functions have the form `alpha_s(a)+chi_a(b)` with a common additive character `chi_a` of `F_p`. Comparing different roots forces the remaining row constants to cancel `chi_a(lambda a)`, modulo a character already constant on `L0`. Thus every period character is a linear combination of (1). Conversely every such combination is constant on legal stars. There are `p` choices of `chi_a` for each root label and old type. They are distinct on `L0`, since changing one neighbor label in one root row changes exactly its congruence by any desired field value. Character duality therefore proves (2) and `L=ker C`.

The affine origin at any admissible size may be chosen as the table array `m^(0)` of all-zero stars: each physical table has only `m_i,s(0,0)=n_i`. It is compatible and legal, including the even pooled internal diagonal. Thus the compatible independent affine lattice is `m^(0)+K0`, and the compatible legal affine lattice is

```
m^(0)+(K0 intersect L).
```

There is no additional class-size or pool-size residue condition.

## 2. Cross interactions determine affine character coefficients

Consider an annihilator coefficient array `h_i(a) in F_p`, meaning

```
sum_(i,a) h_i(a) C_i,a(m)=0 for every m in K0.            (3)
```

For any cross factor `ij`, put a zero-row/zero-column two-by-two transfer into its pooled table and its transpose into the reverse pooled table:

```
T=e_(a,b)-e_(a,b')-e_(a',b)+e_(a',b').
```

This is realized in `K0` by placing the entire transfer in **one** physical slot in each direction and putting zero in the remaining slots. All common root margins are zero. Therefore no factor `q_ij` appears, and the argument is unchanged when that multiplicity is divisible by `p`.

Equation (3) gives

```
[h_i(a)-h_i(a')](b-b')
 +[h_j(b)-h_j(b')](a-a')=0.                              (4)
```

All secant slopes of `h_i` are consequently one constant `t_i`, all those of `h_j` are one constant `t_j`, and `t_i+t_j=0`. Hence along cross support edges

```
h_i(a)=t_i a+c_i,       t_i+t_j=0.                       (5)
```

## 3. Internal interactions force constants

If `q_ii>0`, take the pooled internal transfer

```
T=2(e_(a,a)+e_(b,b)-e_(a,b)-e_(b,a)).
```

It is symmetric, has zero row margins, and has even diagonal. It too can be placed in one physical internal slot, with all other slot tables zero, so it is in `K0` regardless of `q_ii mod p`. Its character value is

```
2(a-b)[h_i(a)-h_i(b)].
```

Since `p` is odd, annihilation forces `h_i(a)=h_i(b)` for every distinct pair. Thus an internal old-type loop forces that type's coefficient function to be constant.

If nonbipartiteness instead comes from a cross-support odd cycle, (5) gives `t_i=-t_j` around the cycle and hence `2t_i=0`; again every slope is zero. Connectivity propagates this conclusion to every old type. The single-old-type case is covered directly by its internal factor. We have proved that every annihilator has the form

```
h_i(a)=c_i, independent of a.                           (6)
```

## 4. Arbitrary independent integer root margins extend to K0

This extension is explicit, so no reduction-modulo-`p` saturation assumption is needed. Fix arbitrary integer vectors `r_i(a)` with zero total.

For a cross factor `ij`, a pooled integer table with rows `q_ij r_i` and columns `q_ji r_j` is obtained using the anchor label zero:

```
M_ij(a,0)=q_ij r_i(a)       for a!=0,
M_ij(0,b)=q_ji r_j(b)       for b!=0,
M_ij(0,0)=q_ij r_i(0)+q_ji r_j(0),
M_ij(a,b)=0                for a!=0,b!=0.
```

Set `M_ji=M_ij^T`. All entries here are directions and may be negative.

For an internal factor let `v(a)=q_ii r_i(a)`. Define a symmetric pooled direction table by

```
M_ii(a,0)=M_ii(0,a)=v(a)   for a!=0,
M_ii(0,0)=2v(0),
all other entries zero.
```

Its row margins are exactly `v`: the zero row sums to `sum_(a!=0)v(a)+2v(0)=v(0)`. Its diagonal is even.

Finally, any pooled table whose rows are `q_ij r_i` can be decomposed into its `q_ij` physical slots with row margin `r_i` in each. Put the anchor-column table `A(a,0)=r_i(a)` in the first `q_ij-1` slots and put the pooled table minus their sum in the last slot. Every slot has zero total and row margin `r_i`. This construction applies to internal groups too; symmetry and parity are required only of their pooled sum.

Doing this for every present factor constructs an element of `K0` with the prescribed root margins. In particular the field sums

```
S_i=sum_a a r_i(a) in F_p
```

can be varied independently: take `r_i(1)=1,r_i(0)=-1` and all other entries zero to make `S_i=1`, and scale or combine these choices. Neither reversibility weights nor divisibility of the multiplicities by `p` obstructs this construction.

## 5. Exact compatible rank and index

For the constant coefficient functions (6), pooled compatibility gives

```
sum_(i,a) c_i C_i,a(m)
 =sum_i [(Q-lambda I)c]_i S_i.                           (7)
```

Indeed, the column margins of `M_ji` contribute `q_ij r_i`, including the internal factor by symmetry. Because the `S_i` vary independently, (7) vanishes on `K0` if and only if

```
(Q-lambda I)c=0.
```

Conversely every such `c` annihilates all of `K0` by (7). Thus, writing

```
t=dim_(F_p) ker(Q-lambda I),
```

the annihilator of `C(K0)` has dimension exactly `t`, and

```
rank_(F_p) C(K0)=kp-t,
[K0:K0 intersect L]=p^(kp-t).                            (8)
```

This argument proves the image rank directly by explicit integer directions; it does not infer it from a potentially unsaturated reduction of integer pooled compatibility constraints.

## 6. Compatible cosets have equal weighted-Q mass asymptotically

This step requires only two central inputs, both separately proved by the central-frame argument:

1. The independent-star table law has a relative maximal-lattice local CLT uniformly on the `sqrt(n) log n` window, with positive covariance on its real span. The legal law's ratio to it is `p^(kp)(1+o(1))` on the legal affine lattice in that window.
2. Under the **normalized weighted independent law**, the full physical tables lie in that window with probability `1-o(1)`; this follows from its configuration-plus-iid-root-label interpretation and subgaussian concentration.

Let this normalized compatible weighted law be `mu_n(m)`, proportional to `P_Qind(M=m) W(m)`, with its exact normalizer. For every fixed direction `b in K0`, uniformly when both tables are in the logarithmic central window,

```
mu_n(m+b)/mu_n(m)=1+o(1).                                (9)
```

The probability ratio in (9) follows immediately from the relative local CLT, since the shift is bounded and `||m-E M||=O(sqrt(n)log n)`. The weight ratio follows directly from exact factorial ratios. In a cross pool, each bounded entry shift contributes its uniform pooled mean to the power of that shift; the powers cancel because the pool-total shift is zero. In an internal pool, diagonal shifts are even, and `(m+2z-1)!!/(m-1)!!` contributes the pooled mean to the power `z`; combining these with the off-diagonal factorials cancels the powers by the symmetric pool-total-zero identity. Errors are uniformly `O(log n/sqrt(n))` for a fixed shift. This proof retains the internal diagonal parity and does not require a pooled Gaussian precision calculation.

The finite quotient `K0/(K0 intersect L)` has the fixed size in (8). Choose bounded integer representatives once and for all. Translation by one representative bijects its affine cosets. Restrict a coset to the logarithmic central window, translate, and use (9). The image stays within a slightly enlarged logarithmic window, still covered by the same relative estimate. The discarded mass is `o(1)` by input 2. Applying the reverse translation gives the reverse inequality. Thus all cosets have asymptotically the same `mu_n` mass, namely

```
1/[K0:K0 intersect L] +o(1)=p^(-kp+t)+o(1).               (10)
```

The legal compatible affine lattice is one of these cosets. Combining (2), (10), and the relative legal/independent local comparison yields the sharp full-uniform contribution

```
Z_uniform=p^t+o(1).                                     (11)
```

No positivity assertion for a pooled precision matrix is being silently used: fixed-translation invariance in the central window plus concentration provides the required finite-coset equidistribution.

## 7. Sharp scalar moment and the RSBM consequence

For a scalar alphabet on a connected nonbipartite support, the only subspaces are `0` and `F_p`. The point phases are exactly the old-type maps `a` satisfying `Qa=lambda a`, so there are `p^t` of them. The zero-defect contribution at each point phase is exactly one for every configuration, and the boundary estimate in `boundary-frame.md` bounds its nonzero-defect contribution by `O(n^(-(d-2)/2))`.

Choose fixed small phase neighborhoods disjointly (different point phases differ on at least one fixed-positive-proportion class) and separate from a small full-uniform neighborhood. The entropy compact complement has a strictly negative maximum and contributes `poly(n) exp(-c n)`. With the central inputs above this proves

```
E |ker_(F_p)(A-lambda I)|=2 p^t+o(1)                    (12)
```

for the configuration frame along every admissible size sequence. This exact moment statement is not asserted after conditioning on simplicity; the high-probability real-nullity consequence transfers by bounded-cost conditioning.

For the two-block regular SBM, take

```
Q=[[d1,d2],[d2,d1]],       lambda=d1-d2.
```

Internal factors give nonbipartite old support even when `d1=2`. For any odd prime not dividing `d2`, the two quotient eigenvalues differ by `2d2`, so `t=1`. The planted integer vector is always in the kernel. If real nullity is at least two, the finite-field kernel has at least `p^2` vectors; subtracting the deterministic planted line of size `p` from (12) gives

```
limsup_n P(real nullity>=2) <=1/(p-1).
```

Sending fixed admissible primes to infinity proves one-dimensionality with high probability, **provided the two central inputs used in Section 6 have been completed and independently audited for the full frame configuration law**. Direct conditioning of the independent factors on simplicity then gives the requested uniform-simple RSBM. This includes `(d1,d2)=(2,1)` and odd block sizes with even internal degree. No effective failure rate follows from the fixed-prime argument alone.
