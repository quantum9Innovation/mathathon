# Full-uniform central contribution for regular configuration frames

This note proves the central input for the proposed general-frame bounded-moment theorem. It is a local estimate, not an entropy-only assertion about the complete moment. Internal pairings, repeated physical slots, unequal fixed type sizes, and all admissible size residues are included.

The proof is self-contained. It uses exponential tilting and Fourier inversion for a finite-support lattice law, with the uniformity and lattice factors stated and proved below. No asymptotic equivalence between a configuration model and a permutation model is used.

## 1. Frame model and precise conclusion

Fix finitely many types `i=1,...,k`, positive integers `a_i`, and nonnegative integers `d_ij` such that

```
sum_j d_ij=d>=3,             a_i d_ij=a_j d_ji.
```

For scale `N`, type `i` has `n_i=a_i N` vertices. Each type-`i` vertex has `d_ij` labeled physical stubs directed toward type `j`. Every cross factor `i<j` with `d_ij>0` is an independent uniform bijection between its `n_i d_ij=n_j d_ji` labeled stub sets. Every internal factor has an independent uniform pairing of its `n_i d_ii` stubs. Scale `N` is admissible when the internal stub counts are even. Multiple edges and loops are allowed at this stage; each internal loop contributes its two physical incidences to adjacency.

At a type-`i` vertex assign a root label in a finite vector space `V_i`. Its neighbor labels lie in a common space `U_i` for all its `d` physical slots, and impose

`sum_(s=1)^d neighbor_s = T_i(root)`.                    `(1)`

Here `T_i:V_i->U_i` can be any fixed affine map. The cases needed for the induction are:

1. **One space:** `V_i=U_i=V` for all types. Write `q=|V|`.
2. **Two spaces on a bipartite type support:** `V_i=V_L,U_i=V_R` on the left and the reverse on the right. Write `u=|V_L|,v=|V_R|`. There are no internal factors in this case. Reversibility and common degree imply `sum_(i in L)n_i=sum_(i in R)n_i` exactly.

The maps may vary with type and need not be invertible. A vector space of dimension zero has size one and is allowed.

Let `Z` count labelings satisfying `(1)`. For each physical slot `s` of type `i`, let `M_i,s(x,y)` count vertices whose root is `x` and whose label at that slot is `y`. These are full physical-slot tables; slots aimed at the same old type are still recorded separately. Put

```
mu_i,s(x,y)=1/(|V_i||U_i|),
mu_N=(n_i mu_i,s)_(i,s),
Delta=M-mu_N.
```

Use a fixed Euclidean norm on this finite-dimensional array space.

**Central theorem.** There is `epsilon>0`, depending only on the fixed data, for which the expected number `Z_unif` of valid labelings with `||Delta||<=epsilon N` satisfies

```
limsup_(admissible N->infinity) E Z_unif <= I,
I=product_i |U_i|^{|V_i|}.                               (2)
```

In the one-space case `I=q^{kq}`. In the two-space case
`I=v^{|L|u}u^{|R|v}`. The type sizes affect the neighborhood and concentration constants, but not this lattice-index upper bound. If both alphabets are singletons the assertion is immediate, with `Z<=1`.

The restriction here is a neighborhood in **full physical-slot tables**. A proof of the full moment must show separately that all remaining zero phases and the entropy complement are covered. This note makes no claim based solely on pooled-table closeness.

## 2. Exact pooled pairing weight and two normalizers

For a full table array `m`, form the pooled table

`m_ij(x,y)=sum_(slots s aimed at j) m_i,s(x,y)`.

Compatibility means `m_ji=m_ij^T` for cross factors; an internal `m_ii` must be symmetric and have even diagonal. Set the weight `W(m)` to zero otherwise. For compatible arrays set

```
W_ij(m)=product_(x,y) m_ij(x,y)! / (n_i d_ij)!,       i<j,

W_ii(m)= [product_x (m_ii(x,x)-1)!!
           product_(x<y) m_ii(x,y)!]
          / (n_i d_ii-1)!!,

W(m)=product_factors W_ij(m).                           (3)
```

Empty factors are omitted and `(-1)!!=1`. These formulas count exactly the compatible bijections or pairings of labeled stubs. In particular, internal loops and prescribed parities have not been dropped. The weight depends only on the pooled tables, although the probability laws below retain full physical-slot tables.

For each type define two local laws, sampled independently at every vertex and between types:

- `P_i`: a uniform legal star. Its root and any `d-1` neighbor labels are independent uniform; the omitted label is determined by `(1)`. The number of legal stars is `|V_i||U_i|^{d-1}`.
- `Q_i`: its root and all `d` neighbor labels are independent uniform.

Write `P_N,Q_N` for the resulting full-table distributions. Put

`K_N=product_i [|V_i||U_i|^{d-1}]^{n_i}`.

Exact counting gives

```
E Z=K_N E_(P_N) W(M).                                  (4)
```

The independent-neighbor count similarly gives

```
E_(Q_N) W(M)=product_i |U_i|^{-d n_i}.                  (5)
```

Indeed, each configuration together with its root labeling determines exactly one set of ordered neighbor labels. Summing `W` over unrestricted stars therefore counts root labelings, and dividing by their total number gives `(5)`.

In the one-space case `K_N=q^{d sum_i n_i}`. In the two-space case, write the equal total vertex count on each side as `n_side`. Then

```
K_N=(uv)^{d n_side}=product_i |U_i|^{d n_i}.
```

Thus in both cases

```
K_N E_(Q_N) W(M)=1.                                    (6)
```

Define the **normalized weighted reference law**

`nu_N(m)=K_N Q_N(M=m) W(m)`.

It is a probability law. More concretely, it is precisely the law of the full physical-slot tables obtained by first sampling the independent configuration factors and then choosing every vertex's root label independently uniformly from its type's alphabet. This exact representation is the source of the concentration bound in Section 5.

## 3. Common real span, covariance, and maximal lattices

For one old type `i`, let `H_i` be the real vector space of deviations of its `d` rectangular `|V_i|`-by-`|U_i|` tables with zero total in each table and identical row-sum vectors in all slots. Its dimension is

`h_i=(|V_i|-1)+d |V_i|(|U_i|-1)`.

The full deviation space is the orthogonal direct sum `H=direct-sum_i H_i`. Coordinates of dimension zero contribute no determinant or lattice factor.

Let `P_row,i` denote the orthogonal projection in `H_i` onto tables that are identical across slots and constant within each row. Under both local laws the table mean is `mu_i`, and their covariance on `H_i` is

```
Sigma_i=(|V_i||U_i|)^{-1}[Id+(d-1)P_row,i].              (7)
```

To verify this, condition on the root. Any two distinct neighbor labels are independent uniform under `P_i` because `d>=3` leaves a third coordinate to absorb the constraint; the same holds under `Q_i`. If the root alphabet or neighbor alphabet is a singleton, the absent covariance modes are simply removed. For test tables whose slot row means coincide, total variance is the sum of the conditional variances plus the variance of the sum of those row means, giving `(7)`. Its eigenvalues are `d/(|V_i||U_i|)` on the common-row modes and `1/(|V_i||U_i|)` on the row-centered modes. It is therefore positive definite on the entire declared space.

In particular both support difference spans are exactly `H_i`. Let `L0_i` be the full integer lattice in `H_i`. Differences of `Q_i`-support generate `L0_i`: changing one neighbor within one root row gives all within-row transfers; changing the root with all neighbors fixed gives the remaining common-row directions.

Let `L_i` be the lattice generated by differences of legal-star table vectors. It is characterized inside `L0_i` by the finite-group congruences, one for each root label `x`,

```
C_i,x(m)=sum_s sum_y y m_i,s(x,y)-T_i(x) r_i(x)=0
             in the additive group U_i,                 (8)
```

where `r_i(x)` is the common slot row sum. On difference arrays this formula is interpreted linearly, so it applies equally to affine `T_i`.

Here is a maximal-period proof, including completeness. A circle-valued character constant on the local legal support can be written by row functions `theta_s(x,y)`. At fixed root `x`, their sum is constant whenever `sum_s y_s=T_i(x)`. Three distinct slots and a compensating variation give the finite additive Cauchy equation; consequently

`theta_s(x,y)=alpha_s(x)+chi_x(y)`,

where all slots have the same additive character `chi_x` of `U_i`. Variation of the root forces `sum_s alpha_s(x)+chi_x(T_i(x))` to be constant in `x`. Modulo the characters already constant on the unrestricted `Q_i` support, these are exactly the characters of `(8)`. Each `chi_x` is free, with `|U_i|` choices. They are independent: a within-row transfer at root `x` changes `C_i,x` arbitrarily while leaving all other root rows fixed. Hence

```
[L0_i:L_i]=|U_i|^{|V_i|},
[L0:L]=I=product_i |U_i|^{|V_i|}.                        (9)
```

This is the maximal support-difference lattice, so after choosing a fundamental dual torus there is exactly one modulus-one characteristic-function point. Repeated target types do not enter this local character calculation.

If `z_i` is any legal single-star table vector, the legal affine support lies in `n_i z_i+L_i`, and the unrestricted affine support lies in `n_i z_i+L0_i`, because a legal star is also an unrestricted star. Thus the first affine lattice is contained in the second at every size. Compatibility with the pooled pairings can fail on a given residue class, but then its contribution is zero; no residue assumption is needed for the upper estimate.

## 4. Uniform relative tilted lattice estimate

We give the finite-support analytic statement rather than invoking a central-window estimate beyond its range.

Let `X` be a finite-support random vector in an affine real space `z0+H`, with all support probabilities positive, support-difference lattice `L` spanning `H`, and positive covariance on `H`. Write `mu=E X`. Identify `H` with its Euclidean coordinates. The log moment generating function

`Lambda(theta)=log E exp(<theta,X>)`

is analytic. Its Hessian at zero is positive definite. The inverse function theorem supplies fixed neighborhoods of zero and `mu` on which `theta -> grad Lambda(theta)` is an analytic diffeomorphism. Shrink them to compact neighborhoods. For every target `t` in the latter let `theta(t)` be its tilt, `Sigma_t` its covariance, and

`J(t)=<theta(t),t>-Lambda(theta(t))`

with the harmless normalization `Lambda(0)=0`. Translation of the affine support only adds linear terms and does not affect the argument. Uniformly on this neighborhood, eigenvalues of `Sigma_t` stay positive and finite, support probabilities are bounded below, and all derivatives through any fixed order are bounded.

For any lattice point `m in n z0+L` with `m/n=t` in that neighborhood, exponential tilting gives the exact identity

`P(S_n=m)=exp(-n J(t)) P_(theta(t))(S_n=m)`.

At the tilted mean, Fourier inversion on a fundamental dual torus gives, uniformly in those `t`,

```
P_(theta(t))(S_n=m)
 = covol(L) (2 pi n)^(-h/2) (det Sigma_t)^(-1/2)
       [1+O(n^{-1/2})].                                 (10)
```

For completeness, the uniformity follows directly as follows. The finite support and the compact tilt set make the tilted probabilities uniformly positive. Away from any fixed neighborhood of the origin on the maximal-lattice torus, the characteristic-function modulus is at most a common `rho<1`. In a fixed small neighborhood, the centered logarithm is

`-<xi,Sigma_t xi>/2+O(||xi||^3)`

uniformly in `t`, with a common Gaussian modulus bound. Rescale `eta=sqrt(n)xi`. Integrating the cubic error against this Gaussian gives `O(n^{-1/2})`; the portion with `||eta||>n^{1/12}` is exponentially small, and the outer torus contributes `O(rho^n)`. This proves `(10)` with its exact covolume and determinant. It also proves positivity at every such affine lattice point for all sufficiently large `n`; there is no unproved support-saturation assumption.

Apply this to `P_i` and `Q_i`. Their means and covariance agree by `(7)`, hence their analytic rate functions have identical constant, linear, and quadratic Taylor terms at `mu_i`. Consequently there are fixed constants `epsilon0,C` such that, uniformly for `||m_i-n_i mu_i||<=epsilon0 n_i` on the legal affine lattice,

```
P_i(M_i=m_i)/Q_i(M_i=m_i)
 <= C [L0_i:L_i]
      exp(C ||m_i-n_i mu_i||^3/n_i^2).                  (11)
```

Here the determinant ratio is uniformly bounded on the compact tilt neighborhood, while the rate-function difference is bounded by a constant times the cube of the displacement. On the logarithmic window `||m_i-n_i mu_i||<=sqrt(n_i)log n_i`, the determinant ratio tends to one and the rate-function error is `o(1)`, giving the sharper uniform relation

```
P_i(M_i=m_i)=[L0_i:L_i](1+o(1))Q_i(M_i=m_i).            (12)
```

The number of types is fixed and `n_i=a_i N` with all `a_i>0`. Multiplying these estimates proves, after changing fixed constants, the global comparison

```
P_N(M=m)/Q_N(M=m) <= C I exp(C ||Delta||^3/N^2)         (13)
```

throughout `||Delta||<=epsilon0' N` on the legal affine lattice. It is zero outside that lattice. Also

```
P_N(M=m)=I(1+o(1))Q_N(M=m)                             (14)
```

uniformly on `||Delta||<=sqrt(N)log N`. The affine containment and `(10)` ensure that every nonzero numerator in these comparisons has positive denominator for sufficiently large `N`.

## 5. Exact weighted reference concentration

Under `nu_N`, first choose the independent configuration and then iid uniform labels. It is useful to represent all its randomness as independent uniform permutations and independent vertex labels:

- An internal pairing of `L` stubs is generated by a uniform permutation of those stubs, pairing positions `(1,2),(3,4),...`. Each pairing has exactly `2^{L/2}(L/2)!` preimages, so the induced pairing is uniform.
- A cross bijection is generated by a uniform permutation of one endpoint stub set after fixing orders on both sets.

The total number of permutation entries is `O(N)` because the frame is fixed. Fix one scalar entry of the full physical-slot array `M`.

Changing an internal stub permutation by one transposition changes at most two paired edges, thus at most four directed physical incidences. The same bound holds for a cross permutation transposition. Hence this table entry changes by at most four. Internal loops cause no problem: even if some incidences share a vertex, there are still at most four affected stubs.

Changing the root label at one vertex affects its own `d` physical-slot indicators and at most `d` reverse incidences at its partners. Thus a scalar table entry changes by at most `2d`. Multiple edges and loops can only identify some of these incidences; they cannot increase the bound.

Expose the permutation images one at a time, and then the independent labels. Two possible choices for the next image have completions coupled by a single transposition of images, preserving all previously exposed entries. Their conditional expectation difference is therefore at most four. This gives Doob martingale increments of uniformly bounded range for each permutation exposure. The analogous label increments have range at most `2d`. The sum of squared range bounds is at most `C N`, so the elementary martingale exponential-moment argument yields

`nu_N(|M_j-E M_j|>=t)<=2 exp(-c t^2/N)`

for every scalar coordinate `j` and all `t>=0`. The fixed number of coordinates and a union bound give

```
nu_N(||M-E_nu M||>=t)<=C exp(-c t^2/N).                 (15)
```

The centering used by the local limit theorem is `mu_N`, not `E_nu M`. They differ by only `O(1)`. Cross edges always join distinct vertices, so iid root labels give the exact independent mean in every cross slot. For an internal physical stub at a vertex of type `i`, the probability its partner belongs to the same vertex is

`(d_ii-1)/(n_i d_ii-1)`

when `d_ii>0`. Otherwise its two endpoint labels are independent uniform. Thus the mean of a fixed internal-slot table is

```
n_i[(1-rho_i)/(q^2) + rho_i 1_(x=y)/q],
rho_i=(d_ii-1)/(n_i d_ii-1),
```

entrywise. Its difference from `n_i/q^2` is uniformly bounded. This also covers `d_ii=1`, where the loop probability is zero. Since there are finitely many coordinates,

`||E_nu M-mu_N||<=C`.

Consequently `(15)` gives constants `C,c,C0>0` such that

```
nu_N(||Delta||>=t)<=C exp(-c t^2/N),   t>=C0 sqrt(N).    (16)
```

The bound is valid for all larger `t`, not merely within the central neighborhood. In the bipartite two-space case there are no internal loops and the means agree exactly. All constants may depend on the fixed spaces and frame.

## 6. Integrating the cubic likelihood ratio

By `(4)` and `(6)`, every restricted central contribution is the expectation under `nu_N` of the likelihood ratio `P_N(M)/Q_N(M)`, with that ratio taken to be zero away from its legal affine lattice.

On `||Delta||<=sqrt(N)log N`, `(14)` gives

`E Z_log <= I+o(1)`.

For the surrounding neighborhood choose fixed `epsilon>0` so small that `(13)` applies and `C epsilon<c/2`, with `c` from `(16)`. Write `T=||Delta||` and `eta=C epsilon`. On `T<=epsilon N`,

`exp(C T^3/N^2)<=exp(eta T^2/N)`.

The subgaussian tail integrates this exponential weight with no polynomial loss. For `L=sqrt(N)log N`, integration by parts gives

```
E_nu [exp(eta T^2/N) 1_(T>=L)]
 <= C exp(-(c-eta)L^2/N)
    + C integral_L^infinity (2 eta t/N)
                         exp(-(c-eta)t^2/N) dt
 <= C' exp(-c' log^2 N).                               (17)
```

The constants are fixed and `eta<c`; the concentration bound is valid along the whole integral. Multiplying by the fixed prefactor in `(13)` proves that the contribution with

`sqrt(N)log N<T<=epsilon N`

tends to zero. This proves `(2)`.

## 7. What this closes, and what it does not

The full-uniform contribution for general regular frames is bounded with its finite lattice index retained. The argument neither pools away physical-slot fluctuations nor assumes an unproved pooled Gaussian determinant cancellation. Its fixed-neighborhood tail estimate uses the exact weighted reference law, not the original iid star law.

For a complete bounded-moment theorem one must still prove the zero-phase classification and proper-coset neighborhood bounds, including conditional forcing for internal pairings and the bipartite two-space induction. This note supplies only the full-uniform input to that proof. It does not infer the complete theorem from nonpositive entropy.
