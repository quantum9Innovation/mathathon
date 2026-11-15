# Exact scalar central coefficient by lattice-coset equidistribution

This note proves the scalar sharpening suggested by root. It uses the fully proved central estimate in `central-frame.md`, but does not use a pooled Gaussian determinant. Throughout the frame has common degree `d>=3`, a connected **nonbipartite** old support (an internal factor is a self-incidence), and a common alphabet `F_p` with `p` odd. Fix scalar target `lambda in F_p`; the legal equation is `sum neighbors=lambda root`. Let `D=(d_ij)` be the old degree matrix and

`t=dim_Fp ker(D-lambda I)`.

The conclusion is that the full-uniform central contribution is

`p^t+o(1)`                                                     `(1)`

at every admissible size, including all internal pairing parities and all size residues. The phase and sparse-neighborhood arguments needed to turn `(1)` into a full moment are separate inputs, stated at the end.

## 1. The exact affine compatible lattice

Retain every physical-slot table. Let `L0` be the unrestricted integer direction lattice: each physical table has total zero, and all slots at old type `i` share a common integer root-row vector `r_i` with `sum_a r_i(a)=0`. For a direction `z`, write `z_ij` for its pooled table over slots aimed at `j`.

Define `K0` as the subgroup of `L0` satisfying

```
z_ji=z_ij^T                   for i!=j,
z_ii=z_ii^T, z_ii(a,a) even   for internal factors.          (2)
```

Thus `K0` preserves every pairing/bijection reversal and parity constraint. This is an actual integer subgroup, not a reduction of a real vector space with an assumed saturation property.

Let `m0(N)` be the full array from assigning label zero at every vertex: every physical table has its `n_i` entries in cell `(0,0)`. This array is pairing-compatible for every admissible size. Every unrestricted compatible integer array lies in

`A_N=m0(N)+K0`.

Conversely this affine lattice describes exactly the integer equality and parity conditions; nonnegativity is the only additional restriction on the tables. Near the uniform mean every entry is positive. Such unrestricted tables are realizable: for each root row, assign its vertices the slot-neighbor labels independently with the prescribed marginal counts. The exact pooled weight then counts the compatible pairings.

The scalar legal local difference lattice is

```
L=ker C <= L0,
C_i,a(z)=sum_s sum_b b z_i,s(a,b)-lambda a r_i(a)
                                           in F_p.       (3)
```

The maximal-lattice calculation in `central-frame.md` proves that these are all periods and that

`I=[L0:L]=p^{kp}`.

Since `m0(N)` is itself legal, the legal compatible affine arrays are exactly

`m0(N)+(K0 intersect L)`.

Put

`J=[K0:K0 intersect L]=|C(K0)|`.

This is finite, independent of size, and at most `I`.

## 2. Fixed compatible translations preserve the weighted reference law

Let `nu_N(m)=K_N Q_N(M=m) W(m)` be the exact normalized weighted reference probability law from `central-frame.md`. It is the configuration-plus-iid-root-label law and is supported on `A_N`. Write `Delta=m-mu_N`, and fix any `z in K0`.

On the logarithmic central window `||Delta||<=sqrt(N)log N`, the unrestricted full-table local CLT gives

`Q_N(m+z)/Q_N(m)=1+o(1)`                                  `(4)`

uniformly. Indeed, both arrays lie in the same unrestricted affine lattice, all type sizes are fixed positive multiples of `N`, and the change in the Gaussian exponent is `O(log N/sqrt(N))`. The relative local error is uniform. Equivalently one may use the smooth tilted local formula. Every denominator is positive for sufficiently large `N` in this window.

The exact weight ratio also obeys

`W(m+z)/W(m)=1+o(1)`                                     `(5)`

uniformly on the same window. Here are the internal and cross calculations, including their parity factors.

For a cross factor, all pooled entries are
`m_ij(a,b)=n_i d_ij/p^2+O(sqrt(N)log N)`. Its fixed integer pooled shift `u=z_ij` has total zero. Therefore

```
log product_ab (m_ab+u_ab)!/m_ab!
 =sum_ab u_ab log(n_i d_ij/p^2)+O(log N/sqrt(N))
 =o(1).
```

The factor's denominator does not change. Negative shifts are handled by taking reciprocal finite products; all entries remain positive.

For an internal factor, `u` is symmetric and each `u_aa` is even. A diagonal double-factorial ratio has logarithm

`(u_aa/2)log(n_i d_ii/p^2)+O(log N/sqrt(N))`,

while each off-diagonal factorial ratio has logarithm

`u_ab log(n_i d_ii/p^2)+O(log N/sqrt(N))`.

The common coefficient is

`sum_a u_aa/2+sum_(a<b)u_ab=(sum_ab u_ab)/2=0`.

Thus `(5)` holds for internal factors too. The pooled parity is preserved exactly by `(2)`.

Combining `(4)` and `(5)` gives

`nu_N(m+z)/nu_N(m)=1+o(1)`                               `(6)`

uniformly in the logarithmic window. The shifted array is valid there for all sufficiently large `N` because entries are `Theta(N)`, affine-table constraints are preserved, and pooled matching parities are preserved.

The weighted reference concentration in `central-frame.md` puts probability `1-o(1)` in that window, and also in the window shrunk by any fixed amount. Extending `nu_N` by zero off its actual finite support, `(6)` therefore proves

`||nu_N - (nu_N translated by z)||_TV -> 0`.              `(7)`

For an explicit justification, sum the uniform relative error over an inner central window, whose mass tends to one. Both complementary masses tend to zero, since a fixed translation moves its radial boundary by at most `||z||` and the reference tail is subgaussian. This yields total variation convergence without assuming that the entire finite support is translation invariant.

## 3. Equal mass of the finite compatible cosets

The finite quotient `G=K0/(K0 intersect L)` has `J` elements. Choose fixed integer representatives `z_g in K0`. Translation by `z_g` permutes the cosets in `A_N`. Equation `(7)` implies that any two cosets have masses differing by `o(1)`. There are only `J` cosets and their masses sum to one, hence

`nu_N(m0(N)+g+(K0 intersect L))=1/J+o(1)`                 `(8)`

for every coset. No modulo-`p` saturation theorem has been invoked: this is equidistribution in the actual integer quotient defined above.

On the legal affine lattice, the relative legal/unrestricted local CLT is

`P_N(m)/Q_N(m)=I(1+o(1))`

uniformly on the logarithmic window. The legal points in `A_N` constitute the identity coset in `(8)`. Multiplying the relative likelihood by the exact reference law and using concentration gives a logarithmic-window contribution `I/J+o(1)`. The fixed-neighborhood remainder is `o(1)` by the already proved cubic-likelihood/subgaussian-tail estimate. Consequently

`E Z_unif=I/J+o(1)`.                                    `(9)`

It remains to calculate this integer-lattice quotient index. The next section does so directly rather than replacing `K0` by an unchecked finite-field constraint space.

## 4. Scalar annihilator calculation on the actual integer lattice

The map `C` has codomain `F_p^{k p}`. Pair its image with a family of functions `h_i:F_p->F_p` by

`sum_i sum_a h_i(a) C_i,a(z)`.

We determine exactly which such families annihilate every `z in K0`.

### 4.1 Cross interactions force affine functions with alternating slopes

For every positive cross factor `i-j`, every integer zero-row/zero-column pooled interaction table can be inserted in one physical slot at `i`, its transpose in one at `j`, with all other physical tables zero. This belongs to `K0` with all root marginals zero, regardless of the values of `d_ij,d_ji` modulo `p`.

Applying the annihilator to a two-by-two interaction gives, for all labels,

```
[h_i(a)-h_i(a')](b-b')
  +[h_j(b)-h_j(b')](a-a')=0.                            (10)
```

Dividing only by nonzero label differences in `F_p` shows

`h_i(a)=t_i a+c_i,     h_j(b)=t_j b+c_j,     t_i+t_j=0`.

No old degree or type-size factor was divided by.

### 4.2 An internal factor forces its function to be constant

For an internal factor at `i` and any distinct labels `a,b`, let `B_ab` have off-diagonal entries `(a,b),(b,a)` equal to one, diagonal entries `(a,a),(b,b)` equal to minus one, and all other entries zero. The pooled direction `2 B_ab` is symmetric, has zero row sums, and has even diagonal, so it is a direction in `K0`, again placed in one physical slot. Its annihilator value is

`2(b-a)[h_i(a)-h_i(b)]`.

Since `p` is odd, this forces `h_i(a)=h_i(b)` for all labels. This argument uses an explicit integer parity-preserving direction; it does not discard the internal parity constraint modulo `p`.

If the connected old support has an internal factor, this constancy propagates over the cross edges by `(10)`. If there is no internal factor but the support is nonbipartite, its odd cycle forces the alternating slopes to satisfy `t=-t`, so they vanish in odd characteristic. Thus in every connected nonbipartite case all annihilator functions are constant:

`h_i(a)=c_i`.

### 4.3 Root margins really are independently variable over the integers

We prove this explicitly to avoid a hidden saturation assumption. Choose arbitrary integer root-row vectors `r_i` with `sum_a r_i(a)=0`, independently for all old types.

For a cross factor define desired row margins `v=d_ij r_i` and column margins `w=d_ji r_j`. Both total zero. An integer table with these margins is

```
z_ij(a,0)=v(a)       for a!=0,
z_ij(0,b)=w(b)       for b!=0,
z_ij(0,0)=v(0)+w(0),
```

all other entries zero; set `z_ji=z_ij^T`.

For an internal factor set `v=d_ii r_i`, and use

```
z_ii(a,0)=z_ii(0,a)=v(a)    for a!=0,
z_ii(0,0)=2v(0),
```

with all other entries zero. This table is symmetric, has row margins `v`, and has even diagonal.

Finally lift each pooled table into its physical slots. If there are `d_ij` such slots, put in each of the first `d_ij-1` slots any fixed integer table `E_i` with row margins `r_i` and total zero, for example `E_i(a,0)=r_i(a)`. Put the pooled table minus their sum in the last slot. Its row margins are also `r_i`. This works for internal pools as well; individual physical-slot tables need not be symmetric. Every physical table has total zero and every slot at a type has the same row vector. The resulting full direction belongs to `K0` and realizes all the chosen `r_i`.

Thus root-row marginals are independently variable as integer vectors of total zero, with no divisibility restriction involving degrees, type proportions, or scale.

### 4.4 The residual condition is the old scalar kernel

For constant `h_i(a)=c_i`, transpose compatibility and the common row margins give the annihilator value

`sum_j [(D-lambda I)c]_j sum_a a r_j(a)`.

Each last moment can be varied arbitrarily in `F_p`, using for example an integer multiple of `e_1-e_0` in the chosen root row. Therefore annihilation is equivalent to

`(D-lambda I)c=0`.

Conversely this condition annihilates every direction in `K0`, by the same pooled column-margin identity. The annihilator of `C(K0)` has dimension exactly `t`. Since its codomain has dimension `kp`,

```
|C(K0)|=p^{kp-t},
I/J=p^{kp}/p^{kp-t}=p^t.                               (11)
```

Combining `(9)` and `(11)` proves `(1)`. The computation is valid when `p` divides degrees or type-size proportions; only odd characteristic and connected nonbipartite old support were used to kill slopes.

## 5. Conditional consequence for the full scalar moment

Once the general-frame zero-phase classification and sparse-neighborhood estimate are independently established, a scalar alphabet has only `H=0` and `H=F_p` phases on a connected nonbipartite support. There are `p^t` point phases, namely the fiber-constant old solutions `(D-lambda I)a=0`. Each contributes `1+o(1)` under the sparse estimate, including support-one defects allowed in a configuration model. The entropy complement contributes `o(1)`. Together with `(1)` this gives

`E |ker_Fp(A-lambda I)|=2p^t+o(1)`.                     `(12)`

This final equality uses those separate boundary and phase inputs; the present note alone proves the exact full-uniform coefficient.

For the two-block regular SBM with positive internal degree, the old support is nonbipartite because both internal factors are self-incidences. At `lambda=a-b` and an odd prime not dividing `b`, the old degree matrix has scalar kernel dimension `t=1`. Thus `(12)`, if the separate inputs close as stated, becomes `2p+o(1)` and the fixed-prime-to-real argument would prove planted real-kernel simplicity at every admissible size, including `(a,b)=(2,1)`. This is a consequence to be taken only after those inputs have been audited; it is not inferred from entropy alone.
