# Exact fixed-prime scalar moment and planted-eigenvalue simplicity

This is a derived strengthening of the central and boundary estimates in this directory. It is restricted to a connected **nonbipartite** regular type support and an **odd fixed prime**. The full vector-moment theorem does not require these two extra assumptions.

## Statement

Use the regular configuration-frame model of `bounded-frame-moment-theorem.md`: old degree matrix `Q=(q_ij)` has common row sum `d>=3`, fixed positive integer size multipliers `a_i` satisfy `a_i q_ij=a_j q_ji`, type `i` has `a_i N` vertices, and all independent internal pairings and cross-stub bijections are retained. The connected old support has a loop when `q_ii>0`; assume it is nonbipartite.

Fix an odd prime `p` and scalar `lambda in F_p`. Put

`t=dim_Fp ker(Q-lambda I)`.

Then, along **every admissible scale**, in the unconditioned configuration model,

`E |ker_Fp(A_N-lambda I)| = 2 p^t+o_(Q,a,p)(1)`.

No condition that `p` avoid any degree or size multiplier is imposed. The prime is fixed before the size limit. The sharp moment formula is not asserted unchanged after simplicity conditioning; its configuration-model upper bound is enough to transfer real simplicity.

## 1. The full-uniform contribution is an exact lattice ratio

Use the full physical-slot tables and the independent laws `P_N,Q_N` from `central-frame.md`. Write `L0` for the unrestricted integer table-difference lattice (each slot has total zero and every slot at one old type has the same root-row margin), and `L` for the legal support-difference lattice. The latter is exactly the kernel of the congruences

```
C_i,x(m)=sum_(physical slots s)sum_y y m_i,s(x,y)
            -lambda x r_i(x)  in F_p,
```

one per root label `x` and old type `i`. Here `r_i` is the common root-row count. Its maximal index is

`[L0:L]=p^(k p)=I`.

Let `K0` be the subgroup of `L0` also satisfying all pooled cross reversal constraints, pooled internal symmetry, and **even internal pooled diagonal**. This is the compatible integer direction lattice. At each admissible size, the all-zero star table `m0(N)` is both legal and compatible. Thus unrestricted compatible arrays have affine lattice `m0(N)+K0`, and legal compatible arrays have affine lattice `m0(N)+(K0 intersect L)`. Put

`J=[K0:K0 intersect L]`.

The direction lattices are fixed independently of size, and `K0 intersect L` has finite index in `K0`; the affine translation is the only size-dependent item. No claim is made that `K0` has finite index in `L0`, whose real span can be larger.

The normalized weighted reference law

`nu_N(m)=K_N Q_N(M=m) W(m)`

is exactly a random configuration with iid uniform vertex labels. Its full-table deviations from the independent mean obey a subgaussian bound, including the bounded loop bias. Consequently its mass lies in `||M-mu_N||<=sqrt(N)log N` with probability `1-o(1)`.

For **every fixed** `z in K0`, uniformly on that window (and its fixed-width enlargement),

`nu_N(m+z)/nu_N(m)=1+o(1)`.

This follows without a pooled Gaussian determinant. For `Q_N` it is the relative iid full-table local limit estimate: its centered Gaussian exponent changes by `O(||z|| log N/sqrt(N))`, and its relative error is uniform. For a cross pool, the exact factorial ratio in `W(m+z)/W(m)` has leading factor `(pool_size/p^2)^(sum_(x,y) z_ij(x,y))=1`. For an internal pool, each diagonal shift is even, and the double-factorial and factorial ratios have leading exponent

`(1/2)sum_x z_ii(x,x)+sum_(x<y)z_ii(x,y)
 =(1/2)sum_(x,y)z_ii(x,y)=0`.

Every pooled and physical-slot entry is `Theta(N)` in the window, so all these ratios are uniformly `1+o(1)` and all fixed translations preserve nonnegative entries for large sizes. The same relative local limit estimate guarantees positive unrestricted masses on the relevant affine lattice points.

Choose fixed representatives for the finite quotient `K0/(K0 intersect L)`. Translation by their differences bijects its affine cosets. The translated logarithmic windows differ only in a fixed-width outer shell, whose `nu_N`-mass is `o(1)` by concentration. The preceding ratio therefore makes the masses of all `J` cosets equal up to `o(1)`. Since their total mass is `1-o(1)`, each coset has mass `1/J+o(1)`.

On the legal affine lattice, the central likelihood ratio is `P_N/Q_N=I(1+o(1))`. The surrounding fixed-neighborhood annulus has vanishing contribution by the cubic-ratio/subgaussian integration in `central-frame.md`. Hence the **exact** full-uniform expected contribution is

`I/J+o(1)`.

## 2. Computing the compatible congruence rank

We show `J=p^(k p-t)`, hence `I/J=p^t`.

Let coefficients `h_i(x) in F_p` define a linear functional on the congruence image. It annihilates `C(K0)` exactly when

`sum_(i,x) h_i(x) C_i,x(m)=0` for every `m in K0`.

For a present cross factor `i,j`, insert a zero-row/zero-column `2x2` transfer in its pooled table and its transpose in the reverse pool, putting the transfer in one physical slot of each orientation. This is an actual integer direction in `K0`. It gives

```
[h_i(x)-h_i(x')](y-y')
 +[h_j(y)-h_j(y')](x-x')=0.
```

Taking anchor labels zero and one shows that `h_i(x)=s_i x+c_i`, `h_j(y)=s_j y+c_j`, with `s_i+s_j=0`.

For an internal factor, put twice the symmetric `2x2` direction with diagonal entries `+1` at `(x,x),(y,y)` and off-diagonal entries `-1` at `(x,y),(y,x)` into one physical slot. It has zero row margin, symmetric pooled table, and even pooled diagonal, so it belongs to `K0`. It forces

`2[h_i(x)-h_i(y)](x-y)=0`.

Since the prime is odd, `h_i` is constant. More generally, an odd old cross cycle forces the affine slopes above to equal their own negatives, hence to vanish. Connectivity of the nonbipartite support therefore makes **every** annihilator function constant, `h_i(x)=c_i`.

For such constants the functional on any compatible table reduces exactly to

`sum_i [(Q-lambda I)c]_i sum_x x r_i(x)`.

All root-margin directions needed here really occur in `K0`; no assertion of mod-`p` saturation is being assumed. One explicit construction is enough. Given arbitrary integer root margins `r_i(x)` of zero total, use twice these margins at every type. For a cross pool `i,j`, choose an integer table with row margins `2q_ij r_i` and column margins `2q_ji r_j`, using label zero as an anchor. For an internal pool take the diagonal table with entries `2q_ii r_i(x)`, which has even diagonal. Any pooled table with row margin `2q_ij r_i` splits into `q_ij` physical-slot tables each with row margin `2r_i`: use `q_ij-1` anchor-neighbor tables and put the residual in the last slot. Negative entries are allowed in a lattice direction. Reverse cross pools are transposes and are decomposed independently into their physical slots.

Thus the root margins are free modulo `p`, because multiplication by two is invertible. Taking a root-margin difference between labels one and zero at any chosen old type proves that the functional vanishes exactly when

`(Q-lambda I)c=0`.

Conversely every such `c` annihilates all compatible directions by the exact pooled-margin identities. The annihilator therefore has dimension `t`. The image of the `k p` scalar congruences on `K0` has rank `k p-t`, and elementary finite-group duality gives

`J=|C(K0)|=p^(k p-t)`.

This proof explicitly permits multiplicities `q_ij` divisible by `p` and arbitrary fixed size multipliers. Internal parity causes no odd-prime obstruction because all constructed diagonal shifts are even.

## 3. Point phases and the global sharp moment

For a scalar alphabet `F_p`, its only linear subspaces are `0` and `F_p`. The complete nonbipartite zero-phase classification in `boundary-frame.md` therefore leaves precisely:

- the full-uniform phase;
- point phases `c=(c_i)` satisfying `(Q-lambda I)c=0`.

There are exactly `p^t` point phases. Each is an exact type-constant eigenvector for every configuration, since every physical vertex has exactly `q_ij` incidences toward old type `j`. A small neighborhood of a point phase contains this one exact labeling plus nonzero quotient supports. The correlation-safe sparse certificate bound applies with zero-dimensional restricted space, whose homogeneous count is one, so its extra expected contribution is `O(N^{-(d-2)/2})`.

Choose the point-coset neighborhoods disjoint by taking their defect radius less than one quarter of the smallest old-type size coefficient; distinct point maps differ on every physical vertex of at least one old type. Shrink the full-uniform neighborhood so that it is disjoint from these point neighborhoods. Every remaining feasible type lies in a compact region with strictly negative entropy exponent. Its total contribution is `poly(N)exp(-cN)=o(1)`.

The full-uniform contribution from Sections 1–2 is `p^t+o(1)`. The `p^t` point neighborhoods contribute `p^t+o(1)`. Adding the vanishing complement proves

`E |ker_Fp(A_N-lambda I)|=2p^t+o(1)`.

## 4. Full RSBM planted-eigenvalue simplicity

For the original regular SBM take

```
Q=[[d1,d2],[d2,d1]],   d1>d2>0,
d=d1+d2>=3,           lambda=d1-d2.
```

The old support is connected and nonbipartite because `d2>0` and the internal degrees `d1>0` supply self-incidences. The fixed block size is any `N` for which `N d1` is even. Over every fixed odd prime `p` not dividing `d2`, the two quotient eigenvalues differ by `2d2`, so

`dim_Fp ker(Q-lambda I)=1`.

The sharp configuration-model moment is therefore `2p+o_p(1)` for **all** fixed `d1>d2>0`, including `(2,1)`, at every admissible block size.

If the real nullity of the integer matrix `A-lambda I` is at least two, all its minors of order `2N-1` vanish as integers and hence modulo every prime. Its finite-field kernel then has at least `p^2` elements. Markov's inequality gives

`limsup_N P_config(nullity_R>=2) <=2/p`.

The planted sign vector is always a nonzero real kernel vector. Letting fixed odd primes not dividing `d2` tend to infinity proves configuration-model nullity exactly one with high probability.

Finally, the probability that the two internal factors and cross factor are all simple is bounded below by a degree-dependent positive constant, independent of the prime. Thus

`P_simple(nullity_R>=2)
 <=P_config(nullity_R>=2)/P_config(all factors simple) ->0`.

Conditioning gives exactly the requested independent uniform simple regular/biregular factors. Hence the planted eigenvalue is simple with high probability for **every fixed `d1>d2>0` and every admissible block-size sequence**, without an outlier-gap assumption. Exact rational nullspace elimination gives recovery up to global sign.

The real high-probability conclusion here uses a fixed-prime limit followed by primes tending to infinity. No polynomial real failure rate or uniform growing-prime estimate is asserted. The known `(2,1)` localized switching lower bound `Omega(N^-2)` remains compatible with this conclusion.
