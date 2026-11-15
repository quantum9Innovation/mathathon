# Full-uniform central bound for heterogeneous channels

Derived November 15, 2026. This module proves the central estimate directly for the channel class below. It does not use a common root alphabet, equal total degrees, a common rectangular table width, or a common subspace at entropy-zero phases. The finite-support Fourier argument is included rather than invoked as an analogy with an earlier model.

## 1. Fixed data and conclusion

There are finitely many types `i`, integers `d_ij>=0`, and positive integers `a_i` with

```
a_i d_ij=a_j d_ji,      n_i=a_i N,      d_i=sum_j d_ij<=D.
```

At each type-`i` vertex there are `d_ij` labeled physical slots aimed at type `j`. Independently, the cross-factor stubs are matched by uniform bijections and internal-factor stubs by uniform pairings. Admissible scales have even internal stub counts. A loop has two physical incidences. No assertion here conditions away loops or parallel edges.

Fix symmetric numbers `q_ij=q_ji` on the present type pairs, satisfying

```
0<=q_ij<1/2,             sum_j d_ij q_ij=1.
```

A physical slot aimed at `j` has weight `q_ij` and is called active when that weight is positive. Every vertex has at least three active physical slots, since two numbers strictly below `1/2` cannot sum to one.

Fix finite vector spaces `V_i,U_i` over a prime field. For each present ordered type pair fix a linear injection `L_ij:V_j -> U_i`, required to be an isomorphism when `q_ij>0`. The local equation is

```
sum_(physical slots s at i) L_i,j(s)(Y_s)=T_i(X),       (1)
```

where `X in V_i` is the root. The proof permits any fixed function `T_i:V_i -> U_i`; the global induction needs linear maps. Put `A_i=|V_i|`, `B_i,s=|V_j(s)|`, and `C_i=|U_i|`.

For each physical slot retain a separate table

```
M_i,s(x,y)=#{type-i vertices having root x and slot-s label y},
mu_i,s(x,y)=1/(A_i B_i,s),
mu_N=(n_i mu_i,s)_(i,s),     Delta=M-mu_N.
```

Use any fixed Euclidean norm on this finite-dimensional table space. Let `Z_unif` count global solutions of (1) whose full physical tables satisfy `||Delta||<=epsilon N`.

**Central theorem.** For some fixed `epsilon>0`,

```
limsup_(admissible N -> infinity) E Z_unif <= I,
I=product_i C_i^(A_i).                                (2)
```

The bound covers every admissible residue class. No positivity of the inactive weights or surjectivity of inactive channels is used.

## 2. Exact weights and normalization

For a full table array `m`, pool the slots aimed at the same old type:

`m_ij(x,y)=sum_(s:j(s)=j) m_i,s(x,y)`.

Let `W(m)=0` unless `m_ji=m_ij^T` on cross factors and `m_ii` is symmetric with even diagonal on internal factors. Otherwise set

```
W_ij=product_(x in V_i,y in V_j) m_ij(x,y)! / (n_i d_ij)!,   i<j,

W_ii=[product_x (m_ii(x,x)-1)!! product_(x<y) m_ii(x,y)!]
      /(n_i d_ii-1)!!,

W=product_present_factors W_ij.                         (3)
```

Absent factors are omitted and `(-1)!!=1`. For a complete assignment of root and neighbor labels, `W` is exactly the probability that the configuration realizes all the indicated neighbor labels. It does not depend on the linear channels.

At each vertex let `Q_i` sample its root and every physical neighbor label independently and uniformly. Let `P_i` sample uniformly from the stars legal for (1). One active slot is an isomorphism and can absorb the sum of all other labels. Thus the number of legal stars is exactly

```
k_i=A_i product_s B_i,s / C_i.                         (4)
```

Let `P_N,Q_N` denote the independent-vertex full-table laws and set `K_N=product_i k_i^(n_i)`. Summing over legal ordered stars gives exactly

`E Z=K_N E_(P_N) W(M)`.                                (5)

Summing instead over all ordered stars gives

`E_(Q_N) W(M)=product_i product_s B_i,s^(-n_i)`.          (6)

Indeed, for each configuration and each root labeling there is exactly one consistent collection of ordered neighbor labels. The independent uniform probability of any such collection is `product_(i,s) B_i,s^(-n_i)`, independent of the root labeling; averaging uniform roots leaves this number unchanged.

The remaining factor in `K_N E_Q W` is `product_i(A_i/C_i)^(n_i)`. It is exactly one. To see this, active isomorphisms and the unit row budgets give

```
sum_i n_i log C_i
 =sum_i n_i sum_j d_ij q_ij log |V_j|
 =sum_j n_j log |V_j| sum_i d_ji q_ji
 =sum_j n_j log A_j.                                   (7)
```

The middle equality uses both reversibility and symmetry of `q`. Terms with zero weight contribute zero. Consequently

`K_N E_(Q_N) W=1`.                                     (8)

The weighted law

`nu_N(m)=K_N Q_N(M=m) W(m)`                             (9)

is a probability law. More precisely, it is the table law obtained by sampling the configuration and then independent uniform root labels in their respective spaces `V_i`. For a complete ordered-star array the weight `K_N Q_N` is `product_i C_i^(-n_i)=product_i A_i^(-n_i)` by (7), which is exactly the probability of its specified root labeling. Multiplication by `W` then gives the configuration probability. Passing to tables proves the claim.

## 3. Covariance on the heterogeneous full-table space

For one type `i`, let `H_i` be the real vector space of arrays `(h_s(x,y))_s` such that every table has total zero and all slot tables have the same row-sum vector. Its dimension is

`h_i=(A_i-1)+A_i sum_s(B_i,s-1)`.                       (10)

This is the full real difference space of unrestricted star tables. Its full integer lattice is `L0_i=H_i intersect Z^(all table entries)`.

Under `P_i`, the root and any two distinct neighbor labels are independent uniform. Fix those two labels and the root and choose an active slot distinct from the two. The chosen active isomorphism uniquely solves the constraint after all the remaining labels are freely chosen. The resulting number of completions is independent of the three specified values and has the required product-law cardinality. The same argument covers one specified neighbor. Thus all first moments and all pairwise second moments of the table-indicator vector agree under `P_i` and `Q_i`.

Their common covariance `Sigma_i` is positive definite on exactly `H_i`. Here is a direct proof avoiding any equal-width formula. Under `Q_i`, for a test array `f`, the random functional is

`F=f_1(X,Y_1)+...+f_(d_i)(X,Y_(d_i))`.

Every unrestricted tuple has positive probability. If `Var F=0`, varying `Y_s` while fixing the other labels shows that each `f_s(x,y)` is constant in `y` for each row `x`. Varying `x` then shows that the sum of these slot-row constants is constant in `x`. These are exactly the functionals constant on the affine space of slot tables with common root-row margins; equivalently their restrictions to `H_i` vanish. Therefore covariance has no null direction in `H_i`. Agreement of covariance gives the same conclusion for `P_i`, and in particular its support differences also span `H_i` over the reals.

Singleton spaces simply remove coordinates from (10). If `h_i=0`, all laws and lattice factors at this type are deterministic and interpreted as one.

## 4. Complete maximal-lattice calculation

Differences of unrestricted star tables generate `L0_i`: changes of a neighbor at a fixed root give arbitrary integral transfers within one slot row, and changing the root with fixed neighbors gives the remaining common-row directions.

Write `L_i` for the lattice generated by differences of legal-star table vectors. For `m in L0_i`, let `r(x)` be its common root-row sum and define

```
C_x(m)=sum_s sum_(y in V_j(s)) L_i,j(s)(y)m_s(x,y)
        -T_i(x)r(x) in U_i.                           (11)
```

This is an additive map on the integer lattice, with integer coefficients interpreted by repeated addition in `U_i`. Every legal-star difference has `C_x=0` for all `x`.

We prove that these are all lattice congruences. A circle-valued linear functional on the table space is represented by functions `g_s(x,y) in R/Z`. It has constant value on the local legal support exactly when, for every fixed `x`,

`sum_s g_s(x,y_s)` is constant whenever `sum_s L_i,j(s)y_s=T_i(x)`,

and that value is independent of `x`.

Fix `x`, choose three active slots `a,b,c`, and fix every other neighbor label. In image coordinates `z_s=L_i,j(s)y_s in U_i`, the selected three have full domain `U_i` and satisfy `z_a+z_b+z_c=t`. Hence functions `f_a,f_b,f_c:U_i -> R/Z` obey

`f_a(u)+f_b(v)+f_c(t-u-v)=constant` for every `u,v`.

Compare this identity at `(u+h,v)` and `(u,v+h)`. Their third arguments agree, so

`f_a(u+h)-f_a(u)=f_b(v+h)-f_b(v)`.

For fixed `h` the left side is independent of `u` and the right side independent of `v`; call the common increment `chi(h)`. Comparing increments by `h` and `h'` proves `chi(h+h')=chi(h)+chi(h')`. The same relation with the third slot shows that all three functions have the form `constant+chi(z)`. Thus `chi` is an additive character of `U_i`.

For any other slot `s`, active or inactive, vary its label from `0` to `y` and compensate in active slot `a`. The constraint remains legal, so its function obeys

`g_s(x,y)-g_s(x,0)=chi(L_i,j(s)y)`.

The active slots also show that the same `chi` is independent of the initially fixed labels at other slots: their entire increment function is determined by the fixed original function in slot `a`. Therefore all legal-support characters, at this root, are exactly

`g_s(x,y)=alpha_s(x)+chi_x(L_i,j(s)y)`.                 (12)

Their value on a legal star is `sum_s alpha_s(x)+chi_x(T_i(x))`, which must be independent of `x`. Modulo characters constant on the unrestricted support, these are precisely the characters `chi_x(C_x(m))` of (11), with one freely chosen additive character of `U_i` per root value `x`.

These choices are independent. A transfer `+1` at `(s,x,y)` and `-1` at `(s,x,0)` in one active slot changes `C_x` by `L_i,j(s)y`, which ranges over `U_i`, and leaves every other `C_(x')` unchanged. Thus the map `C=(C_x)_x:L0_i -> U_i^(V_i)` is surjective. Since `L_i` has full real rank, the character calculation of its finite quotient gives

```
L_i=ker C,
[L0_i:L_i]=C_i^(A_i).                                (13)
```

For clarity, equality follows without an assumption about semigroup saturation: `L_i` is a full-rank sublattice of `ker C`; if the inclusion were strict, the nontrivial finite quotient `ker C/L_i` would provide an additional circle character constant on legal support, contrary to (12). Every finite abelian quotient has a separating character.

For any legal single-star vector `z_i`, sums of `n_i` legal stars lie in `n_i z_i+L_i`, contained in the unrestricted lattice `n_i z_i+L0_i`. The product index over types is `I` in (2). These are maximal support-difference lattices. There is no assumption that every affine lattice point is already an attainable sum at every small size.

## 5. Uniform relative finite-support local limit estimate

The analytic ingredient is as follows. Let a finite-support law `X` have positive probabilities at every point of its support, support-difference lattice `L` spanning its real difference space `H`, dimension `h`, mean `mu`, and positive covariance on `H`. Choose coordinates after translating its affine support into `H`. Its log moment generating function `Lambda(theta)` is analytic. The gradient map is locally invertible at zero because its derivative is covariance. There are fixed compact neighborhoods on which each target mean `t` near `mu` has a unique analytic exponential tilt `theta(t)`; the tilted covariance `Sigma_t` stays uniformly positive definite, and all finite-order derivatives stay bounded. Write `J(t)=theta(t).t-Lambda(theta(t))`.

For an affine lattice point `m in n z+L`, `m/n=t` in this neighborhood, the exact tilt identity and Fourier inversion give

```
P(S_n=m)
 =exp(-n J(t)) covol(L) (2 pi n)^(-h/2)
   (det Sigma_t)^(-1/2) [1+O(n^(-1/2))],               (14)
```

uniformly in these `m`. Here determinants and covolumes use the same Euclidean coordinates on `H`.

To justify the relative uniform error, Fourier-invert the tilted law on a fundamental torus of the dual lattice. Maximality of the support-difference lattice means that zero is its only modulus-one point on this torus. Since the compact set of tilted support probabilities is bounded away from zero, outside a fixed small neighborhood of zero its characteristic-function modulus is bounded by a common `rho<1`. Inside that neighborhood the centered logarithm has expansion

`-xi.Sigma_t xi/2+O(||xi||^3)`

and a uniform Gaussian modulus bound. Rescaling `eta=sqrt(n)xi`, integrate the cubic error against the Gaussian to obtain relative `O(n^(-1/2))`; the part with `||eta||>n^(1/12)` is exponentially small and the outer torus contributes `O(rho^n)`. The leading Gaussian integral is uniformly bounded above and below after its `n^(-h/2)` scaling. This proves (14), including positivity at every such lattice point for all sufficiently large `n`.

Apply this separately to the local full-table indicator laws `P_i,Q_i`. Their covariances are identical by Section 3, so their rate functions agree through quadratic order at their common mean. Their difference is bounded by a constant times the cube of the mean displacement. Their lattice covolume ratio is the index (13). Hence, for sufficiently small fixed `epsilon_0>0`,

```
P_i(M_i=m_i)/Q_i(M_i=m_i)
 <= C C_i^(A_i) exp(C ||m_i-n_i mu_i||^3/n_i^2),         (15)
```

uniformly on the legal affine lattice within `epsilon_0 n_i` of its mean. On `||m_i-n_i mu_i||<=sqrt(n_i)log n_i`, the sharper uniform estimate is

`P_i(M_i=m_i)=C_i^(A_i)(1+o(1))Q_i(M_i=m_i)`.          (16)

The determinant ratio tends to one in (16); it is bounded in (15). If the numerator vanishes, define the ratio to be zero. The containment of affine lattices and (14) ensure a positive denominator for every nonzero numerator in these neighborhoods at sufficiently large sizes.

Because the number of types is fixed and `n_i=a_i N`, multiplying gives

```
P_N(M=m)/Q_N(M=m)
 <= C I exp(C ||Delta||^3/N^2)                         (17)
```

on a fixed `epsilon_0' N` neighborhood, and the ratio is `I(1+o(1))` uniformly on `||Delta||<=sqrt(N)log N` on the legal affine lattice. It is zero off that lattice. This is a relative estimate on the required neighborhood, not a central-window absolute-error bound used beyond its validity range.

## 6. Concentration under the exactly normalized weighted law

Use the configuration-plus-iid-roots representation of `nu_N` from Section 2. Generate each internal pairing by a uniform permutation of its stubs, pairing consecutive positions, and each cross bijection by a uniform permutation of one stub set. The internal construction is uniform because every pairing has the same `2^(L/2)(L/2)!` preimages. There are `O(N)` permutation entries in total.

Fix one scalar table entry. A transposition in a permutation changes at most two matched edges, hence at most four physical incidences, so the entry changes by at most four. Changing one vertex label changes its own at most `D` slot indicators and at most `D` partner incidences, so the entry changes by at most `2D`. Loops and parallel edges may cause overlaps and do not increase these bounds.

Expose permutation images successively. Two choices for the next image have uniform completions coupled by a single transposition preserving all previous images. The possible conditional expectations therefore have uniformly bounded range. Expose the independent root labels afterwards. The same bounded-range argument applies to their increments. The elementary exponential-moment proof for this Doob martingale gives

`nu_N(|M_j-E_nu M_j|>=t)<=2 exp(-c t^2/N)`

for every scalar table coordinate, with fixed `c>0`. A union bound over the fixed number of coordinates yields

`nu_N(||M-E_nu M||>=t)<=C exp(-c t^2/N)`.               (18)

The expected table array differs from `mu_N` by `O(1)`. Cross factors have distinct endpoint vertices, so independent root labels give the exact product means. At an internal slot, the two root spaces are both `V_i`; the probability that a stub's partner belongs to the same physical vertex is

`rho_i=(d_ii-1)/(n_i d_ii-1)`

when that factor is present. Thus that slot's expected `(x,y)` count is

`n_i[(1-rho_i)/A_i^2+rho_i 1_(x=y)/A_i]`,

whose difference from `n_i/A_i^2` is bounded uniformly in `N`. There are finitely many entries. For constants `C,c,C0>0`, (18) therefore implies

```
nu_N(||Delta||>=t)<=C exp(-c t^2/N),
t>=C0 sqrt(N).                                        (19)
```

This tail holds at all larger deviations, not only in the central neighborhood.

## 7. Integrating the likelihood ratio

Equations (5), (8), and (9) express each full-table-restricted solution count as a `nu_N` expectation of the likelihood ratio `P_N/Q_N`. On `||Delta||<=sqrt(N)log N`, (16) bounds its expectation by `I+o(1)`.

Shrink fixed `epsilon>0` so that (17) holds and `C epsilon<c/2`, where `c` is the tail constant in (19). Let `T=||Delta||`, `L=sqrt(N)log N`, and `eta=C epsilon<c/2`. When `T<=epsilon N`,

`exp(C T^3/N^2)<=exp(eta T^2/N)`.

Integration of (19) gives

```
E_nu[exp(eta T^2/N) 1_(T>=L)]
 <=C exp(-(c-eta)L^2/N)
   +C integral_L^infinity (2 eta t/N)exp(-(c-eta)t^2/N)dt
 <=C' exp(-c' log^2 N)=o(1).                           (20)
```

Multiplying by the fixed constant in (17) bounds the annulus `L<T<=epsilon N` by `o(1)`. Together with the inner-window estimate this proves (2).

This module proves only the full-uniform contribution. The complete bounded-moment theorem additionally requires an exhaustive entropy-zero classification, restriction closure, and correlation-safe bounds near each proper phase.
