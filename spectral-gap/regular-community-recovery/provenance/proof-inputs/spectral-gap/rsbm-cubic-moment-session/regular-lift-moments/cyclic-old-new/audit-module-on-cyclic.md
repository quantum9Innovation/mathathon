# Independent audit of the cyclic compatible-lattice coefficient

Prepared 2026-11-15. Audited `cyclic-lattice.md`, especially the field-linear dependencies, row-action transposes, cyclic alternating-form argument, integer saturation, and the exact Gaussian fraction for every lift size. No frozen packet file was changed.

**Verdict: PASS.** The compatible dependency dimension is `h_old(R)+a(R)`, with `a(R)=dim{K:K^T=-K,RK=KR^T}`. For odd characteristic and cyclic right action, `a(R)=0`; the uniform coefficient is exactly `p^h_old(R)`.

## 1. Interaction signs and arbitrary-function linearization

The dependency coefficient `h_i(a)` is a column, paired with the row-valued congruence `C_i(a)`. On an edge table, the two endpoint contributions are `b h_i(a)` and `a h_j(b)`. Therefore a zero-margin 2-by-2 transfer gives exactly

`(b-b')[h_i(a)-h_i(a')] +(a-a')[h_j(b)-h_j(b')]=0`.

Set `a'=b'=0` and subtract `k_i=h_i(0)`. For arbitrary row labels `a,b`,

`b U_i(a)+a U_j(b)=0`.

Taking `b=e_l` expresses coordinate `l` of `U_i(a)` as the linear functional `-a U_j(e_l)`. This proves full `Fp`-linearity of each `U_i`; no continuity, polynomial or regularity hypothesis on the original arbitrary functions is being assumed. In the convention `U_i(a)=K_i a^T`, the relation is

`K_j=-K_i^T`.

The transpose and sign are correct: `bK_i a^T=aK_i^T b^T`.

The map `T(K)=-K^T` is an involution. An odd cycle forces `K=T(K)`, and connectedness then forces the same skew-symmetric `K` at every old vertex. This step is precisely where nonbipartiteness is used; it does not apply to bipartite bases.

## 2. Root-margin equation and row-action convention

For common skew `K`, the edge bilinear terms cancel:

`bK a^T+aK b^T=0`.

Collecting the remaining linear edge terms and the on-site term `-(aR)(K a^T+k_i)` gives the coefficient of the root-margin direction at `i,a`:

`a(sum_(j~i)k_j-Rk_i)-aRK a^T`.

The root-margin functions are free subject only to total zero, so this coefficient must be constant in `a`; its value at zero makes that constant zero. Evaluating at `a,-a` in odd characteristic separates linear and quadratic terms. The resulting conditions are exactly

`sum_(j~i)k_j=Rk_i`,

`RK=KR^T`.

For the second one, `aRK a^T=0` for all `a` says that `RK` is skew-symmetric. Since `(RK)^T=-KR^T`, the displayed relation follows with the stated sign.

Placing `k_i^T` in the rows of `X` gives `BX=XR^T`. The Frobenius adjoint of `Y->BY-YR` is `X->B^T X-XR^T`. Since the base adjacency is symmetric and the operator is square, its adjoint kernel has the same dimension as its kernel. Hence the linear dependency dimension is `h_old(R)`, even if either base or target is not semisimple. The `K` and `k` choices are independent and uniquely reconstruct the functions, proving the full dimension formula.

## 3. Cyclicity kills every alternating form, including degenerate ones

The bilinear form in the row convention is `beta(a,b)=aK b^T`. The relation `RK=KR^T` means

`beta(aR,b)=beta(a,bR)`.

If `v` is a cyclic row, write arbitrary rows as `vf(R),vg(R)`. Moving polynomial actions across the form gives

`beta(vf(R),vg(R))=beta(v,v g(R)f(R))`.

Commutativity of the two polynomial actions makes this expression symmetric in `f,g`. Thus `beta` is symmetric on the full space. It was already alternating/skew; odd characteristic forces it to vanish. The argument never inverts the form and applies unchanged to degenerate `K`, singular `R`, and a cyclic Jordan block.

Every companion matrix is cyclic for the row action as well as the column action. For the standard column companion, the last coordinate row and its successive right products form a reversed triangular basis. Thus irreducible companions satisfy the exact hypothesis without requiring a transpose replacement.

## 4. The integer compatible lattice has the claimed reduction

I checked the explicit basis parameterization: independent integer root margins of total zero, plus independent interior edge entries for `a,b!=0`, determine the last row and column by integer formulas. In particular

`m(0,0)=u_i(0)+u_j(0)+sum_(a,b!=0)m(a,b)`

is correct when both root margins have total zero. This supplies every compatible integer direction uniquely. Reducing those same parameters modulo `p` supplies every compatible field direction. There is no loss of rank caused by a hidden saturation index, by division by a degree, or by `p|n`.

The full legal-star lattice is the kernel of the row-wise vector sum congruences inside the independent-neighbor lattice. Its maximal-period proof is valid: at fixed root, three freely compensating neighbor slots force a common additive character in all slots. Root variation imposes precisely the displayed local-sum congruence character, with no further period. Independent within-row neighbor transfers make those congruences onto `V` for each root row. Thus the unrestricted lattice index is exactly `p^(kqr)`, and after compatibility the index is exactly `p^rho` for the computed field rank.

## 5. Exact Gaussian fraction and all lift sizes

The all-zero legal star supplies a compatible integer reference `v0`. Therefore the compatible affine lattice hulls are `n v0+K0` and `n v0+K`, nonempty for every `n`, with the same fixed index `p^rho`. The mean also belongs to their real affine span. Full-rank fixed lattices have bounded covering radius, so their translated central meshes remain within bounded unscaled distance of the mean. No congruence condition on `n` is needed.

The relative tilted LLT compares legal and independent probabilities pointwise on the legal affine lattice by the exact covolume ratio `p^(kqr)`. The Gaussian times matching-factorial weight on compatible tables has strictly positive precision. Consequently its sum over the finite-index legal sublattice is exactly the asymptotic fraction `p^(-rho)` of the sum over the full compatible lattice. This statement is uniform in the changing affine offset: reduce offsets modulo a fixed fundamental cell, then scale by `n^(-1/2)`; compact translated Riemann sums and the positive Gaussian tails give uniform convergence.

The independent-neighbor weighted sum has exact total mass one. Its logarithmic central window has mass `1-o(1)` because under this normalized law one has a random lift and iid uniform root labels; along each base edge the matched pairs are iid uniform pairs. A finite union bound with Chebyshev puts all edge tables in that window. The exact full-uniform coefficient is therefore

`p^(kqr-rho)=p^[h_old(R)+a(R)]`.

The separate local rate-function argument removes the rest of the fixed neighborhood, uniformly at all star allocations with those edge tables. It is a true prefactor calculation, rather than an entropy-zero inference.

## 6. Independent finite-field execution

I reran both direct rank-check programs in the available JavaScript execution runtime. All **15** reported cases passed. These include K4 scalar shifts, irreducible degree-two and degree-three companions, a cyclic Jordan block, noncyclic scalar doubles/triples, and an irreducible factor present in the old spectrum of the eight-vertex Möbius ladder.

The noncyclic scalar double and triple have additional alternating dimensions one and three respectively. Those cases are useful negative controls: the formula would fail if the alternating term were discarded for arbitrary matrix targets. The direct calculations agree with the exact sign `RK-KR^T` and with the dependency dimension asserted in the proof.

## Consequence within the audited scope

For an irreducible companion, there are only point and full-uniform phases. Its exact central coefficient combines with the already proved point-boundary estimate and compact entropy complement to give `E Z=2p^h_old+o(1)`. The modular transfer in `module-transfer.md` can therefore use this sharp moment. This audit does not extend the cyclic exact coefficient to bipartite bases or characteristic two, nor claim that arbitrary reducible cyclic targets have only two global phases.
