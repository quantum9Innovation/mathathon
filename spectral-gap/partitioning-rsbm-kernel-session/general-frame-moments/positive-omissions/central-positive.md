# Central contribution for mixed-degree frames with positive omission weights

This note proves the central full-uniform estimate for the proposed positive-omission extension. The earlier regular-frame packet is read-only and is not modified. The proof below includes the actual local covariance, maximal lattice, uniform relative local limit estimate, exact weighted normalizer, and concentration/integration argument. It does not infer a bounded full moment solely from an entropy inequality.

## 1. Frame, omission certificate, and induction alphabets

Fix a connected integer frame `D=(d_ij)`, positive integer size multipliers `a_i`, and

```
a_i d_ij=a_j d_ji,
d_i=sum_j d_ij,
Dmax=max_i d_i<infinity.
```

Type `i` contains `n_i=a_i N` physical vertices. A type-`i` vertex has `d_ij` labeled physical slots aimed at type `j`. The independent factors are uniform cross-stub bijections and uniform internal stub pairings. Internal loops contribute two physical incidences. Scales are admissible when all internal pool sizes `n_i d_ii` are even.

Assume symmetric omission weights `theta_ij=theta_ji` on every active factor, including internal factors, such that

```
0<theta_ij<1/2,
sum_j d_ij theta_ij=1 for each i.                        (P)
```

This forces `d_i>=3`: a sum of at most two numbers each strictly below one half cannot equal one. For the central proof the roles of `(P)` are precisely this minimum-slot condition and the bipartite physical-size balance proved next. The weights do not enter the local star probabilities.

The two required alphabet classes are:

1. One common finite vector space `V`, so root and all neighbor labels lie in `V`.
2. On a bipartite old support `L,R`, spaces `V_L,V_R`, with root space `V_i=V_side(i)` and common neighbor space `U_i=V_opposite(i)`.

In the first case put `V_i=U_i=V`. In the second the two spaces may have different dimensions; a dimension-zero space is allowed. At each old type impose a fixed affine local equation

`sum_(s=1)^(d_i) y_s=T_i(x),     T_i:V_i->U_i`.          `(1)`

The maps may depend on type and need not be invertible. The common linear target `x->xR` is included. An affine version is harmless and also allows fixed coset shifts.

### Exact bipartite size balance

If the old support is bipartite, it has no internal factors. Reversibility and `(P)` give the exact identity

```
sum_(i in L) n_i
 =sum_(i in L,j in R) n_i d_ij theta_ij
 =sum_(j in R,i in L) n_j d_ji theta_ji
 =sum_(j in R) n_j.                                    (2)
```

Thus the **total number of physical vertices** on the two sides is equal, even though their individual old class sizes and their total degrees may differ. This identity continues to hold for every restricted pair of side alphabets, since it depends only on the frame and omission certificate.

## 2. Exact weight and the central theorem

Keep a table `M_i,s(x,y)` for every physical slot, including separate tables for repeated slots aimed at the same old type. Its independent mean is `n_i/(|V_i||U_i|)` in every entry. Write `mu_N` for the array of these means and `Delta=M-mu_N`, in any fixed Euclidean norm.

For the pooled tables

`m_ij(x,y)=sum_(slots s aimed at j) m_i,s(x,y)`,

require cross reversal `m_ji=m_ij^T`, and internal symmetry with even pooled diagonal. Set `W=0` if these fail. Otherwise define

```
W_ij=product_(x,y) m_ij(x,y)!/(n_i d_ij)!       (i<j),

W_ii=[product_x (m_ii(x,x)-1)!!
       product_(x<y)m_ii(x,y)!]/(n_i d_ii-1)!!,

W=product_(active factors) W_ij.                        (3)
```

As usual absent factors are omitted and `(-1)!!=1`. These are exact labeled-stub pairing probabilities, not approximations. In particular loops and parity constraints remain present.

Let `Z` count assignments satisfying `(1)`. Let `Z_unif(epsilon)` count those whose full physical-slot tables satisfy `||Delta||<=epsilon N`.

**Central theorem.** For some fixed `epsilon>0`,

```
limsup_(admissible N->infinity) E Z_unif(epsilon)
 <= I_*=product_i |U_i|^{|V_i|}.                         (4)
```

Thus `I_*=q^{kq}` in the one-space case `q=|V|`, and
`I_*=v^{|L|u}u^{|R|v}` in the two-space case `u=|V_L|,v=|V_R|`.
The bound includes all admissible scale residues. Constants in the neighborhood and estimates depend only on the fixed frame, spaces, and maps. They can be made uniform over any fixed finite family of maps.

This is a full physical-slot neighborhood. Control of other zero phases and the entropy complement is a separate part of the complete bounded-moment proof.

## 3. Legal and independent laws, with the exact normalizer

Independently at each vertex choose one of two laws:

- `P_i`: uniform among legal stars `(1)`. The root and any `d_i-1` neighbor labels are independent uniform. There are `|V_i||U_i|^{d_i-1}` stars.
- `Q_i`: the root and all `d_i` neighbor labels are independent uniform.

Use `P_N,Q_N` for their full-table laws and put

`K_N=product_i [|V_i||U_i|^{d_i-1}]^{n_i}`.

Exact counting of star assignments followed by compatible labeled-stub factors gives

```
E Z=K_N E_(P_N) W(M).                                  (5)
```

Under unrestricted stars, each configuration and every root labeling determine exactly one ordered neighbor assignment. Therefore

```
E_(Q_N) W(M)=product_i |U_i|^{-d_i n_i},

K_N E_(Q_N) W(M)=product_i (|V_i|/|U_i|)^{n_i}.          (6)
```

The last factor is the normalizer issue that must not be dropped in a nonregular extension. In the common-space class it is exactly one. In the two-space class it is `(u/v)^{n_L-n_R}`, which is one by `(2)`. More explicitly, if

`E_N=sum_(i in L) n_i d_i=sum_(j in R)n_j d_j`

is the number of physical bipartite edges, then

`K_N=(uv)^{E_N}`

once `n_L=n_R`. This replaces the common-degree formula; no common value of the `d_i` is used.

Consequently in both induction classes

```
K_N E_(Q_N) W(M)=1.                                    (7)
```

The probability law

`nu_N(m)=K_N Q_N(M=m)W(m)`

is exactly the law obtained by first sampling the independent configuration factors and then labeling all roots independently uniformly in their type's space. This gives an actual probabilistic reference distribution, including internal loops.

## 4. Local real spaces and identical positive covariance

For old type `i`, let `H_i` be the real deviation space of its `d_i` rectangular `|V_i|`-by-`|U_i|` tables, with zero total in every slot and one common root-row margin vector. Its dimension is

`h_i=(|V_i|-1)+d_i |V_i|(|U_i|-1)`.

Let `Pi_row,i` be the orthogonal projection onto arrays identical across slots and constant within each root row. The local table mean and covariance under both `P_i,Q_i` are

```
mu_i,s(x,y)=1/(|V_i||U_i|),
Sigma_i=(|V_i||U_i|)^(-1)[Id+(d_i-1)Pi_row,i].           (8)
```

Indeed, given the root, any two distinct legal neighbor labels are independent uniform because `d_i>=3` leaves a third coordinate to absorb the sum constraint. The same pairwise law holds under `Q_i`. Conditional variance of a test array is the sum of its individual conditional variances; variance of its common row mean supplies the second term in `(8)`.

For an explicit check, if all slot row means are `g(x)`, then

`Var(sum_s f_s(X,Y_s))
 =(|V_i||U_i|)^(-1)||f||^2
   +d_i(d_i-1) E g(X)^2`.

The squared norm of the common-row projection is
`d_i |U_i| sum_x g(x)^2`, proving `(8)`.

The covariance eigenvalues are `d_i/(|V_i||U_i|)` on the common-row modes and `1/(|V_i||U_i|)` on row-centered modes. They are positive on all of `H_i`; singleton spaces merely remove absent modes. The joint covariance is the direct sum of `n_i Sigma_i`. There is no requirement that the different `d_i` agree.

## 5. Maximal local lattices and every period

Let `L0_i` be the unrestricted integer lattice in `H_i`. Changing one neighbor label at one root row in one slot gives every within-row transfer; changing the root while fixing all neighbor labels gives the remaining common-row directions. Thus the unrestricted support differences generate `L0_i`.

The legal support-difference lattice `L_i` is the kernel in `L0_i` of the congruences, one for each root label `x`,

```
C_i,x(m)=sum_(s=1)^(d_i) sum_y y m_i,s(x,y)
                -T_i(x)r_i(x)=0 in U_i,                (9)
```

where `r_i` is the common root-row direction. The affine nature of `T_i` causes no issue because `x` is a fixed index in this linear expression in the table entries.

Here is the completeness argument. A circle-valued character constant on legal stars has row functions `theta_s(x,y)`. At a fixed root, vary two slot labels while a third compensates. Since `d_i>=3`, the finite additive Cauchy equation forces

`theta_s(x,y)=alpha_s(x)+chi_x(y)`

with one common additive character of `U_i` in every slot. Variation of the root forces `sum_s alpha_s(x)+chi_x(T_i(x))` to be constant in `x`. Modulo the unrestricted-support characters, these are exactly the characters of `(9)`. The character `chi_x` is arbitrary at each root row. A within-row slot transfer changes its congruence arbitrarily without changing another row, so these characters are independent. Therefore

```
[L0_i:L_i]=|U_i|^{|V_i|},
[L0:L]=I_*=product_i |U_i|^{|V_i|}.                     (10)
```

In particular this is the maximal support-difference lattice, with a single modulus-one characteristic-function point on its dual fundamental torus. The number of slots changes the real dimension but not this finite index.

Choose any legal local star vector `z_i`. Because it is also unrestricted, the affine legal lattice `n_i z_i+L_i` is contained in the unrestricted affine lattice `n_i z_i+L0_i` at every size. Compatibility with the pooled factors may fail for a particular legal residue; then its contribution is simply zero. No extra size-residue assumption is needed for an upper bound.

## 6. Uniform relative local limit estimate on a fixed neighborhood

For clarity the analytic lemma is stated here, not replaced by an assertion of matching second moments. Let `X` have fixed finite support in an affine lattice `z0+L` spanning a real space of dimension `h`, with positive probabilities and positive covariance. Its log moment generating function is analytic; its Hessian at zero is positive definite. The inverse function theorem gives an analytic mean-to-tilt map on a fixed neighborhood of the mean. On a smaller compact neighborhood, tilted probabilities have a common positive lower bound, covariance eigenvalues have common positive bounds, and all derivatives are bounded.

For `S_n` a sum of iid copies, every affine lattice target `m` with `t=m/n` in that neighborhood has the exact exponential-tilt relation followed by the uniform local estimate

```
P(S_n=m)=covol(L)(2 pi n)^(-h/2)
          [det Sigma_t]^(-1/2) exp[-n I(t)]
          [1+O(n^(-1/2))].                             (11)
```

The relative form and its uniformity can be proved directly by Fourier inversion at the tilted mean. On the maximal-lattice torus, outside a fixed origin neighborhood the characteristic-function modulus is uniformly bounded by a number less than one. Near the origin its centered logarithm is

`-<xi,Sigma_t xi>/2+O(||xi||^3)`

with common constants. After rescaling by `sqrt(n)`, Gaussian domination and integration of the cubic error give the uniform `O(n^-1/2)` relative error; the outer torus has exponentially small contribution. This proof also makes the local mass positive at every relevant affine lattice target for all sufficiently large `n`; no unproved saturation claim is needed.

Apply `(11)` separately at old type `i` with `n_i=a_i N`. The two laws have the same mean and covariance `(8)`, so their analytic rate functions agree through second order. Determinant ratios remain uniformly bounded on the fixed tilt neighborhood. Thus on the legal affine lattice, with `Delta_i=m_i-n_i mu_i`,

```
P_i(M_i=m_i)/Q_i(M_i=m_i)
 <=C [L0_i:L_i] exp(C ||Delta_i||^3/n_i^2).              (12)
```

In the logarithmic window the determinant ratio tends to one and the cubic rate difference tends to zero. Multiplying over the finitely many old types, using their fixed positive size multipliers, yields

```
P_N(M=m)/Q_N(M=m)
 <= C I_* exp(C ||Delta||^3/N^2)       (||Delta||<=epsilon0 N),

P_N(M=m)/Q_N(M=m)
 = I_*(1+o(1))                       (||Delta||<=sqrt(N)log N).
                                                               (13)
```

The numerator is zero away from its affine lattice. Inside the stated neighborhood, a nonzero numerator has positive denominator by affine containment and `(11)`. All estimates are uniform over every admissible size residue. If a local real dimension is zero, its determinant and covolume factors are omitted and its probability factor is one.

## 7. Weighted reference subgaussian concentration, including loops

Use the exact `nu_N` representation from `(7)`. Generate every internal pairing by a uniform permutation of its stubs paired consecutively; each pairing has `2^{L/2}(L/2)!` permutation preimages. Generate each cross bijection by a uniform permutation. These permutations are independent of one another and of all iid root labels. Their total number of entries is `O(N)` at the fixed frame.

A transposition in one stub permutation changes at most two matched edges and hence at most four directed physical incidences. A scalar full-table coordinate changes by at most four. This remains true for loops or repeated vertices. Changing one root label affects its own `d_i` incidences and at most `d_i` reverse incidences, giving a coordinate change at most `2d_i<=2Dmax`.

Expose permutation images successively and then expose root labels. Two choices for a next permutation image have completions coupled by one image transposition that preserves every earlier image; the conditional expectation ranges therefore differ by at most four. Root-label conditional ranges are at most `2Dmax`. The sum of squared martingale range bounds is `O(N)`. The elementary exponential martingale bound, followed by a union bound over the fixed number of table coordinates, gives

`nu_N(||M-E_nu M||>=t)<=C exp(-c t^2/N)`                 `(14)`

for all `t>=0`, after harmless changes of constants.

The local-limit center is `mu_N`. In cross factors its mean is exact because the paired endpoints are distinct vertices with independent uniform labels. For an internal physical stub at type `i`, the probability of pairing to another stub of its own vertex is

`rho_i=(d_ii-1)/(n_i d_ii-1)`.

Its fixed-slot table mean is

`n_i[(1-rho_i)/q^2+rho_i 1_(x=y)/q]`

in the one-space alphabet of size `q`. This differs from `n_i/q^2` by only `O(1)` in each entry. The case `d_ii=1` has no loop bias. All two-space bipartite factors are cross factors. Hence

`||E_nu M-mu_N||=O(1)`,

and `(14)` implies

```
nu_N(||Delta||>=t)<=C exp(-c t^2/N),
                                      t>=C0 sqrt(N).    (15)
```

The inequality holds for all larger `t`, not just within the fixed central neighborhood. Mixed total degrees change only the fixed constants through `Dmax` and the type sizes.

## 8. Integrating the cubic ratio and completing the central bound

Equations `(5)` and `(7)` make every restricted contribution the expectation under `nu_N` of the likelihood ratio `P_N/Q_N`, zero off the legal affine lattice.

On `||Delta||<=sqrt(N)log N`, the second line of `(13)` gives contribution at most `I_*+o(1)`. For the annulus, choose fixed `epsilon>0` small enough that `(13)` applies and `eta=C epsilon<c/2`, with `c` from `(15)`. Writing `T=||Delta||`, for `T<=epsilon N`,

`exp(C T^3/N^2)<=exp(eta T^2/N)`.

The tail integrates this ratio with no polynomial loss. For `L=sqrt(N)log N`,

```
E_nu [exp(eta T^2/N) 1_(T>=L)]
 <= C exp(-(c-eta)L^2/N)
    +C integral_L^infinity (2 eta t/N)
                         exp(-(c-eta)t^2/N) dt
 <= C' exp(-c' log^2 N).                               (16)
```

Thus the annular contribution is `o(1)`, proving `(4)`. This proof retains every lattice factor and uses the exact normalized reference measure, rather than an uncomputed pooled Gaussian precision.

## 9. Scope, closure, and the actual obstruction outside balance

There is no new central obstruction under `(P)`. The local inputs need only `d_i>=3`; the only global extra condition needed by the two-space central comparison is equality of total physical side sizes, which follows exactly from `(P)`. The same frame and balance identity remain after restricting to any pair of subspaces, so this central theorem is closed under the intended bipartite dimension induction.

If a bipartite frame has unequal total physical side sizes, `(6)` exhibits the genuine issue: for unequal side alphabet sizes the legal/independent normalizer has the factor `(u/v)^{n_L-n_R}`, generally exponential in `N`. The proof cannot silently drop that factor. Such a frame cannot satisfy symmetric unit-row omission weights, by `(2)`; it is not part of the present result.

The full bounded-moment theorem still requires the weighted entropy identity, classification of all zero phases using positivity of every omission weight, and sparse-boundary induction. This note does not assert that a weaker certificate allowing zero omission weights has the same phase classification. The old packet remains frozen.
