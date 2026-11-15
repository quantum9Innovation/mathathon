# Degree-three unweighted obstruction to logarithmic relative rank

Status: complete proof note, 15 November 2026. The clean compiled statement is `degree-three-lower-bound.tex` / `.pdf`. The separated-mass fractional lemma is proved independently in `../path-upper/bounded-degree-independent.tex`; its precise statement is recalled below. All graphs here are finite, connected, simple, unweighted before the update, and have maximum combinatorial degree three. Only one existing edge is doubled.

For fixed `0 < alpha < 1`, let

`C_alpha = (L^dagger)^(alpha/2) (Lprime^alpha - L^alpha) (L^dagger)^(alpha/2)`.

**Theorem.** There is a constant `c_alpha > 0` such that, for all sufficiently small `epsilon > 0`, some graph in the above degree-three class has at least `c_alpha / epsilon` eigenvalues of `C_alpha` strictly greater than `epsilon`. Together with the determinant upper bound, the worst-case strict count over this class is `Theta_alpha(1/epsilon)`.

Thus a bound `O_alpha(log^2(1/epsilon))`, independent of graph size, fails for unweighted bounded-degree hosts already at degree three. This theorem does not assert the full determinant-admissible spectral closure: a compulsory local outlier prevents that stronger closure at fixed maximum degree.

## 1. Uniform-gap unit-weight reservoirs with degree-two ports

Fix a family of connected simple cubic graphs with Laplacian spectral gap at least `gamma_0 > 0`, of every sufficiently large even size. This follows from Theorem 1 of Charles Bordenave, *A new proof of Friedman's second eigenvalue theorem and its extension to random lifts*, https://arxiv.org/abs/1502.04482v4 (take `d=3` and adjacency bound strictly below `3`). For example `gamma_0=(3-2sqrt(2))/2` is valid. No optimal expansion is needed.

Subdivide one edge and call the new degree-two vertex `p`. The resulting reservoir `H` has maximum degree three and a distinguished port `p` that can receive one extra edge. Its Laplacian gap remains uniformly positive. Here is an elementary bound: if `Q(x)` is its Dirichlet energy and `mu` the mean of `x` over old vertices, then old-graph energy is at most `2Q(x)`, whence

`sum_old (x_v-mu)^2 <= 2Q(x)/gamma_0`,

and

`(x_p-mu)^2 <= 2Q(x) + 4Q(x)/gamma_0`.

Variance about the actual mean is no larger, so the new spectral gap is at least

`gamma = 1 / (2 + 6/gamma_0) > 0`.

The port resistance to the reservoir mean is

`r(H,p) = e_p^T L_H^dagger e_p`,

and satisfies `0 <= r(H,p) <= R := 1/gamma`. Reservoir sizes can approximate any prescribed positive mass ratio, because subdividing changes the chosen even size by only one.

## 2. The finite core

Let `m=2^k >= 2`. Take a complete binary tree with root `o` and `m` leaves. At each leaf attach a simple neck of length

`ell = K m`,

where the integer `K >= 4(R+1)` is fixed once and for all. Attach the far end of neck `i` to port `p_i` of a reservoir `H_i`. Attach the root by one further edge `e=(o,p_0)` to an anchor reservoir `H_0`. Double exactly `e`.

Every degree is at most three: the root has two children and the edited bridge, internal tree vertices have degree three, neck vertices have degree two, and each reservoir port has internal degree two plus its one external edge. The edited edge is a bridge, so its original leverage is exactly one, independently of all reservoir sizes.

Eliminating a reservoir's mean-zero internal coordinates at zero frequency adds its port resistance `r_i` in series with the incident edge or neck. Consequently, on reservoir mean potentials, the terminal necks have resistances

`ell + r_i`,

and the root-anchor resistance is

`a = 1 + r_0` before the update,

`a' = 1/2 + r_0` after it.

If the anchor mean is fixed to zero, the grounding conductances at the root are

`c_0 = 1/(1+r_0)`, `c_0' = 1/(1/2+r_0)`.

Let `K(r)` and `Kprime(r)` be the SPD stiffness matrices on the `m` terminal reservoir means after eliminating the finite tree and neck core and grounding the anchor. Their difference is positive rank one, by the Schur-complement rank-one identity.

## 3. Every reverse pivot ratio is at least `exp(h/m)`

Order the terminals arbitrarily. For `0 <= j <= m`, let `g_j` be the effective admittance at root `o` when terminals `1,...,j` are grounded through their necks of resistance `ell+r_i` and the other terminals are open. This admittance excludes the root-anchor branch. Thus `g_0=0` and

`0 <= g_j <= m/ell = 1/K`.

We claim that each increment satisfies

`g_j - g_(j-1) >= 1/(4 K m)`.                                      (1)

To see this, hold the root at potential one in the network with the first `j-1` shunts installed. All potentials lie in `[0,1]`, and each grounded terminal draws at most `1/ell`. At tree depth `h`, the edge on the path to terminal `j` carries at most `(m/2^h)/ell = 1/(K 2^h)`. Hence the root-to-leaf drop is less than `1/K`, and the new leaf has open-circuit potential `v_j >= 1-1/K >= 3/4`.

The effective resistance `rho_j` from this leaf to the root, with the root held at zero and existing shunts grounded, is at most the direct tree-path resistance `k`. Adding its new shunt changes the root admittance by the exact rank-one/Thomson identity

`g_j-g_(j-1) = v_j^2 / (ell+r_j+rho_j)`.

Because `r_j <= R`, `k <= m`, and `K >= 4(R+1)`, the denominator is at most `2Km`. Thus the increment is at least `9/(32Km)`, proving the weaker convenient (1).

Put

`f(g) = (c_0'+g)/(c_0+g)`.

Uniformly in `r_0 in [0,R]` and `g in [0,1/K]`,

`-d(log f(g))/dg = (c_0'-c_0)/[(c_0'+g)(c_0+g)] >= beta > 0`,

where one explicit valid choice is

`beta = {1/[2(R+1/2)(R+1)]} / [(2+1/K)(1+1/K)]`.

Write `S_i={i,...,m}` and use determinant one for the empty principal matrix. Schur complementation through the fixed core, followed by the scalar determinant lemma at the root, gives

`det Kprime[S_i] / det K[S_i] = f(g_(i-1))/f(g_m)`.

Indeed the determinant ratio of the core-plus-`S_i` grounded matrix is `f(g_(i-1))`; dividing by the core-only determinant ratio `f(g_m)` leaves the displayed terminal Schur-complement ratio.

Therefore the reverse LDL pivot ratio is exactly

`rho_i := [det Kprime[S_i]/det K[S_i]] / [det Kprime[S_(i+1)]/det K[S_(i+1)]]`

`       = f(g_(i-1))/f(g_i)`.

Using (1),

`log rho_i >= beta/(4Km) =: h/m`,                              (2)

where `h=beta/(4K)>0` is independent of `m`, all reservoir sizes, and all their port resistances.

## 4. Separated terminal masses convert the pivots to fractional response eigenvalues

The finite-dimensional ingredient is the following.

**Separated-mass lemma.** Let `K>0`, `Kprime=K+vv^T`, and let `D_delta=diag(delta^((m-i)/2))_(i=1)^m`. For `A_delta=D_delta K D_delta`, `B_delta=D_delta Kprime D_delta`, as `delta -> 0`, the relative fractional correction eigenvalues tend, with ordering, to

`rho_i^alpha - 1`,

where `rho_i` are the reverse principal determinant/pivot ratios above. This convergence is uniform when `(K,v)` ranges over a compact subset of the SPD rank-one class. Equivalently, give terminal `i` mass `M_i=delta^(-(m-i))`.

A proof is supplied independently in the cited companion note: the positive eigenvalues of `A_delta` have separated scales with leading constants equal to reverse LDL pivots. In their eigenbasis, the leverage masses converge to successive differences of trailing-principal inverse leverages. Substitution into the fractional resolvent formula gives the diagonal limit; off-diagonal entries vanish by the divided-difference estimate with exponent `(1-alpha)/2 > 0`.

By (2), all limiting correction eigenvalues satisfy

`rho_i^alpha - 1 >= alpha log rho_i >= alpha h/m`.              (3)

The port parameters `r=(r_0,...,r_m)` range over the compact cube `[0,R]^(m+1)`, and the resulting `K(r),Kprime(r)` vary continuously and stay SPD. Hence one sufficiently small `delta` works simultaneously for every allowable port vector. The anchor can be made arbitrarily massive relative to these fixed terminal masses; the standard grounding limit then realizes this grounded relative correction, with one extra zero eigenvalue. Both limit steps are uniform over the same compact port cube.

## 5. Ordinary unit-mass reservoirs realize the low relative compression

For completeness, the needed reservoir limit is stated and justified without treating Schur complement as an exact fractional calculus.

**Reservoir limit.** Fix the core and fixed positive target masses `M_0,...,M_m`. Choose reservoir sizes `n_i(s)` with `n_i(s)/s -> M_i` and the common gap lower bound `gamma`. Along any subsequence on which every port resistance `r_i(s)` converges to `r_i`, the compression of the actual graph's relative fractional correction to its `m+1` dimensional low spectral subspace converges to the relative fractional correction of the mass-normalized reservoir Schur pair. This pair has masses `M_i` and physical stiffness equal to the zero-frequency core Schur complement described above. The shared kernel is included as one zero direction.

Here are the spectral details. Decompose the graph space into the normalized reservoir indicators and their orthogonal complement (the complement includes the entire finite core). With `P_s` the indicator isometry, the block sizes are

`P_s^T L_s P_s = O(s^-1)`,

`P_s^T L_s (I-P_sP_s^T) = O(s^-1/2)`.

The complementary block is bounded below by a fixed positive constant. This follows from the reservoir gaps and from coercivity on the fixed core with its reservoir means pinned: the core is connected to all these pins, so its grounded form has positive smallest eigenvalue. The same uniform bound holds after the edge is doubled. Norms of the full graph Laplacians stay bounded (`<=6` before, `<=8` after the update).

Eliminating the complement at zero gives exactly the core stiffness with series contact resistances `r_i(s)`; the frequency-dependent Schur complement differs by `O(lambda/s)`. Thus there are exactly `m+1` low eigenvalues of order `s^-1` (including the zero eigenvalue), and the others stay bounded below. The low spectral isometries differ from `P_s` by `O(s^-1/2)`. After multiplying the low eigenvalues by `s`, their matrices converge to the mass-normalized Schur pair.

For the fractional calculus, compressing a bounded high spectral part to either low subspace contributes only `O(s^-1)`. Multiplication by `s^alpha` makes this `o(1)`, precisely because `alpha<1`. The low part contributes the limiting `alpha` power. The inverse factors in the baseline low eigenbasis scale as `s^(alpha/2)` and converge after that scaling, zero on the shared kernel. This proves convergence of the compressed relative correction. No assertion of convergence of the high relative response is required.

By the min-max principle, `m` positive eigenvalues of the limiting low compression give at least `m` positive graph eigenvalues of the same lower size. Choose terminal separation, anchor mass, and then sufficiently large finite reservoir sizes so that the approximation error is below `alpha h/(2m)`. Compactness of port parameters guarantees that these choices can be made even though the particular reservoir port resistances are not prescribed. It follows from (3) that the actual unit-mass graph has

`lambda_m(C_alpha) >= alpha h/(2m)`.

## 6. The strict-count conclusion

Given sufficiently small `epsilon`, choose a power of two `m` with

`alpha h/(8epsilon) <= m < alpha h/(4epsilon)`.

The constructed finite graph then has at least `m` eigenvalues greater than `epsilon`. This yields the lower bound with `c_alpha=alpha h/8`.

Conversely, because the edited edge is a bridge, its leverage is one and

`det_support(I+C_alpha)=2^alpha`.

If `q` eigenvalues exceed `epsilon`, then `(1+epsilon)^q < 2^alpha`, so

`q < alpha log 2 / log(1+epsilon) = O_alpha(1/epsilon)`.

This upper bound holds for every connected unweighted graph with one edge doubled, whether or not the edited edge is a bridge (in general its leverage is at most one). Therefore the degree-three worst-case order is exactly `Theta_alpha(1/epsilon)`.

## Scope and comparison

The graph size can be enormous: the construction uses long terminal necks, widely separated reservoir sizes, and a still larger anchor. It is an existence theorem, not a practical compression algorithm. It uses only degree-three, unit-conductance, unit-mass graphs before the edge update. The source input from Bordenave's Theorem 1 is solely the existence of cubic reservoirs of every sufficiently large even size with a uniform spectral gap. The fractional spectral and circuit arguments above are deductions for the present relative-update question.
