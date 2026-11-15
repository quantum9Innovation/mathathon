# Exact ordered-star entropy for the `(2,1)` moment

Prepared 2026-11-15. These are direct finite counting and entropy arguments; no external theorem is imported. The result controls the exponential scale and gives uniform quadratic coercivity at the uniform phase. It does **not**, by itself, evaluate the Gaussian prefactor or prove the desired `Cp` bound.

## Exact configuration-model enumeration

Gauge the cross matching to the identity. For a candidate vector `(x,y)` the equations are

`C1 x = x-y`,  `C2 y = y-x`.

Give each vertex two distinguishable internal stubs in each of the two independent degree-two configuration models. A vertex has central labels `(a,b)=(x_i,y_i)`. If its first-block ordered neighbor labels are `(u,v)`, then `v=a-b-u`. If its second-block ordered neighbor labels are `(c,d)`, then `d=b-a-c`. All additions in this note are in `Fp`.

Let `n_ab` be the number of vertices of central type `(a,b)`. Let `n1_abu` and `n2_abc` be the ordered-star counts. They satisfy

`sum_u n1_abu = n_ab = sum_c n2_abc`.

Define the directed stub counts

`m1_az = sum_(b,u) n1_abu [1_(u=z)+1_(a-b-u=z)]`,

`m2_bz = sum_(a,c) n2_abc [1_(c=z)+1_(b-a-c=z)]`.

Admissibility requires `mj_az=mj_za` and every diagonal `mj_aa` to be even. For an admissible directed stub-count matrix put

`P(m)= product_(a<z) m_az! product_a (m_aa-1)!!`,

with `(-1)!!=1`. This is exactly the number of pairings consistent with the prescribed neighbor labels: for `a<z`, biject the two sets of `m_az` distinguished stubs; on the diagonal pair the `m_aa` stubs internally.

Consequently the exact contribution of a pair of ordered-star tables to the first moment is

`T = [N! product_(a,b) n_ab! / (product_(a,b,u) n1_abu! product_(a,b,c) n2_abc!)]`

`    * P(m1) P(m2) / ((2N-1)!!)^2`.                         (1)

Summing (1) over admissible nonnegative integer tables counts `E|ker_Fp(A-I)|` exactly in the two internal configuration models. There is no assumption that an individual ordered-star table is invariant under swapping its two stubs.

Write `q1=n1/N`, `q2=n2/N`, `pi=n/N`, and `rhoj=mj/(2N)`. The edge laws `rhoj` are symmetric probability laws. Stirling's bounds, including zero factorial arguments, give uniformly over all tables for fixed `p`

`log T = N F(q1,q2) + O_p(log(N+1))`,

`F = H(q1)+H(q2)-H(pi)-H(rho1)-H(rho2)`.                  (2)

For example, symmetry of `m` gives

`log[P(m)/(2N-1)!!] = -N H(rho)+O_p(log(N+1))`.

The number of pairs of tables is at most `(N+1)^(2p^3)`, so a compact family on which `F<=-eta` contributes at most a polynomial in `N` times `exp(-eta N)`.

## An exact information identity

Let `T1(a,b,u)=(a,b,a-b-u)` and `T2(a,b,c)=(a,b,b-a-c)`. These are involutions. Symmetrize each ordered-star law:

`s1=(q1+T1 q1)/2`, `s2=(q2+T2 q2)/2`.

Symmetrization preserves `pi` and `rhoj`; under `s1`, `rho1` is the law of `(A,U)`, and under `s2`, `rho2` is the law of `(B,C)`. Also

`H(sj)-H(qj)=D(qj || sj)`.

The elementary chain rule therefore turns (2) into the exact identity

`F = -I_pi(A;B) - I_s1(B;U | A) - I_s2(A;C | B)`

`    - D(q1 || s1) - D(q2 || s2) <= 0`.                    (3)

Indeed `H(s1)-H(rho1)=H(B|A,U)` and `H(s2)-H(rho2)=H(A|B,C)`, while

`H(B|A)+H(A|B)-H(A,B)=-I(A;B)`.

This proves entropy negativity without an unproved extremization assertion.

## Complete equality characterization over a prime field

Suppose `p` is odd and `F=0`. All five nonnegative quantities in (3) vanish. Hence `qj=sj`, `pi=mu x nu`, and

`q1(a,b,u)=mu(a) nu(b) K_a(u)`,

`q2(a,b,c)=mu(a) nu(b) L_b(c)`.

If the support of `nu` contains distinct `b,b'`, swapping the first block's neighbors gives, for every `a` in the support of `mu`,

`K_a(u)=K_a(a-b-u)=K_a(u+b-b')`.

The nonzero translation `b-b'` generates the additive group of `Fp`, so `K_a` is uniform. The first block's symmetric edge law then has rows `rho1(a,u)=mu(a)/p`. Its symmetry implies `mu(a)=mu(u)` for all `a,u`; thus `mu` is uniform. Since `mu` has at least two support points, the same argument with the second block shows `nu` uniform. The kernels `K_a,L_b` are then uniform as well. This is the full uniform phase

`q1=q2=p^(-3)`, `pi=p^(-2)`, `rho1=rho2=p^(-2)`.

If `nu` is a point mass at `b0`, symmetry of `rho2` forces both of the second block's neighbor labels to equal `b0` almost surely: a symmetric edge law whose central coordinate is constant has both coordinates constant. The local equation `C+D=B-A` then gives `A=-b0`. Thus `mu` is also a point mass. The first block's equation similarly holds exactly when `b0=-a0`. These are precisely the `p` planted constant phases

`(A,B,U,V,C,D)=(a0,-a0,a0,a0,-a0,-a0)`.

There are no other zero-exponent phases. This proof uses primality in the translation step. Oddness is not needed for this particular characterization, but is needed elsewhere for the target modular argument.

## Uniform quadratic coercivity at the full uniform phase

The following bound has a numerical constant independent of `p`. It may help control all tails within the uniform phase; the exact Gaussian determinant and lattice covolume remain separate tasks.

Use normalized `L2` norms with respect to the relevant uniform laws. First restrict to the symmetric-star tangent space. Write relative perturbations `h1,h2`, so for example `q1=p^(-3)(1+h1)`. Let their common central projection be `hpi=E(h1|A,B)=E(h2|A,B)`. Put

`alpha(A)=E(hpi|A)`, `beta(B)=E(hpi|B)`,

`t1(A,U)=E(h1|A,U)`, `t2(B,C)=E(h2|B,C)`.

The edge constraints say `t1(a,u)=t1(u,a)` and `t2(b,c)=t2(c,b)`. Define mutually orthogonal interaction residuals

`r0=hpi-alpha-beta`,

`r1=h1-hpi-t1+alpha`,

`r2=h2-hpi-t2+beta`.

The quadratic term of `-F` is exactly

`Q = (||r0||^2+||r1||^2+||r2||^2)/2`.                     (4)

For clarity, `r1` has zero projections onto both `(A,B)` and `(A,U)`, and `r2` has zero projections onto `(A,B)` and `(B,C)`.

Here is a uniform norm estimate. Decompose

`h1=t1+beta+r0+r1`,  `h2=t2+alpha+r0+r2`.

All terms within either decomposition are orthogonal. Under the first block's stub swap, `A,B` remain fixed and `U` becomes `V=A-B-U`. Since `h1` is swap invariant,

`(I-T1)t1=-(I-T1)(r0+r1)`.

For uniform independent `A,B,U`, the variables `U,V` are independent uniform conditional on `A`. Therefore

`||(I-T1)t1||^2=2||t1-alpha||^2`,

and the operator norm bound `||I-T1||<=2` gives

`||t1-alpha||^2 <= 2(||r0||^2+||r1||^2)`.

Because `t1` is symmetric and has mean zero, its one-coordinate projections are `alpha(A)` and `alpha(U)`, which are orthogonal. Hence

`||t1-alpha||^2 >= ||alpha||^2`,

`||t1||^2 <= 2||t1-alpha||^2 <=4(||r0||^2+||r1||^2)`.

The corresponding estimates for the second block are

`||beta||^2<=2(||r0||^2+||r2||^2)`,

`||t2||^2<=4(||r0||^2+||r2||^2)`.

Combining them yields

`||h1||^2+||h2||^2 <=14||r0||^2+7||r1||^2+7||r2||^2`

`                         <=14(||r0||^2+||r1||^2+||r2||^2)`.

Thus (4) implies

`Q >= (||h1||^2+||h2||^2)/28`.                             (5)

For arbitrary ordered-star tangents, split `hj=sj+aj` into swap-symmetric and swap-antisymmetric parts. The antisymmetric parts have zero central projection and zero averaged edge projection. They are orthogonal to the symmetric parts, and add exactly `(||a1||^2+||a2||^2)/2` to `Q`. Hence (5) remains valid on the full admissible tangent space.

This also gives an actual neighborhood bound, uniformly in `p`. If `||hj||_infinity<=delta<=1/1000`, Taylor expansion of `(1+t)log(1+t)` gives the entropy quadratic with remainder at most `delta/[6(1-delta)^2]` times the squared relative norm. There are five entropies in (2), and each marginal norm is at most the corresponding star norm. Their total squared norm is at most `3(||h1||^2+||h2||^2)` (bound the common central norm by half the sum of the two star norms). Consequently, with generous slack,

`F <= -(||h1||^2+||h2||^2)/56`

throughout this relative-coordinate neighborhood.

## Equivalent full-star formulation

Some enumerations keep a single table of the complete ordered stars. Let `R` be the law of `(A,B,U,C)`; the other internal neighbors are determined by `V=A-B-U` and `D=B-A-C`. The two star marginals are `q1=R_(A,B,U)` and `q2=R_(A,B,C)`. The exact full-table summand has the multinomial `N!/product n_abuc!` times the same two pairing factors. Its entropy exponent is

`Phi(R)=H(R)-H(rho1)-H(rho2)`

`      = F(q1,q2)-I_R(U;C|A,B) <= F(q1,q2) <=0`.             (6)

This gives the fourth nonnegative mutual information in the full-star convention. Summing over full tables with fixed two marginals recovers (1) exactly; it is the elementary multinomial marginal-counting identity.

The only zeros of `Phi` are the uniform law `R=p^(-4)` and the same `p` point masses: equality in (6) forces conditional independence of `U,C` given `A,B`, in addition to the earlier equality conditions.

The uniform coercivity extends directly to this full feasible table. Write `R=p^(-4)(1+h)` and let `h1=E(h|A,B,U)`, `h2=E(h|A,B,C)`, and `hpi=E(h|A,B)`. Put

`r3=h-h1-h2+hpi`.

Orthogonal projection on the uniform product space gives

`||h||^2=||h1||^2+||h2||^2-||hpi||^2+||r3||^2`,

while the quadratic term of `I(U;C|A,B)` is `||r3||^2/2`. Consequently the full quadratic loss satisfies

`-Phi_2 >= (||h1||^2+||h2||^2)/28+||r3||^2/2`

`        >= ||h||^2/28`.                                    (7)

All projections respect the central and averaged-edge constraints, and the two-marginal estimate already permits nonsymmetric ordered slots. Thus (7) applies to the **full** feasible tangent, without a stub-symmetry assumption on `R`.

Since `Phi` contains only the three entropies `H(R),H(rho1),H(rho2)`, each marginal relative norm is at most `||h||`, and each relative marginal supremum at most `||h||_infinity`. The same Taylor estimate gives the explicit full-star neighborhood bound

`Phi(R) <= -||h||^2/56` whenever `||h||_infinity<=1/1000`.      (8)

For each fixed `p`, (8), the polynomial number of integer tables, and uniform Stirling remainders make every feasible type in this neighborhood with `||R-U||_2>log(N)/sqrt(N)` contribute `o(1)`. Indeed the norm conversion has a fixed `p`-dependent factor, so the negative exponent is at least `c_p log(N)^2`, which dominates every fixed power of `N`. The prefactor calculation may therefore be restricted to the central `log(N)/sqrt(N)` window.

## What is and is not proved here

The exact configuration-model moment is a finite admissible-table sum (1). Its exponent is nonpositive, its only zeros are the full uniform phase and the `p` planted constants, and it has a uniform positive quadratic gap at the full uniform phase. Compactness therefore removes all types outside neighborhoods of these phases exponentially fast for each fixed prime.

To finish a `Cp` bound still requires (i) the **full prefactors**, lattice congruences, and Gaussian integral at uniformity with an estimate linear in `p`, and (ii) a rigorous estimate for neighborhoods of the planted constant phases. The polynomial factors suppressed in (2) cannot simply be discarded when `F=0`.
