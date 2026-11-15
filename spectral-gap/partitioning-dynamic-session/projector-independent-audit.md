# Independent audit of `projector-no-go.tex`

Auditor: literature/perturbation sub-agent. Date: 15 November 2026. Reviewed the complete first draft, including graph realization, secular estimates, Cauchy compression, singular-value transfer, and integrated lower bound.

**Verdict:** both quantitative theorems and their stated impossibility conclusions are mathematically sound. The original integrated-budget theorem and the subsequently added fixed-leverage rank theorem have been independently audited. The first draft's typesetting typo has been fixed, and the fixed-leverage theorem resolves the original count-quantifier concern. This audit does not certify novelty.

## Graph realization and leverage

- An isometry `U:R^r -> 1^perp` with `U^T b=sqrt(2/r)1` exists by an orthogonal basis change, since both prescribed vectors have squared norm two.
- `H=U diag(j/r) U^T` has zero row sums and operator norm one. Hence `L=Pi+delta H` has zero row sums and off-diagonal entries at most `-1/n+delta=-1/(2n)`. It is precisely a connected positive-weight complete-graph combinatorial Laplacian with unit vertex masses.
- In the chosen basis, `L'=I+(delta/r)(diag(j)+gamma 11^T)`, because `d=gamma delta/2` and `U^T b b^T U=(2/r)11^T`. No mass rescaling or generalized eigenproblem has been introduced.
- `tau=(gamma delta/r) sum_i lambda_i^-1` lies between `gamma delta/(1+delta)` and `gamma delta`. Thus `tau` does tend to zero along the theorem's sequence.

## Bulk eigenvalues and normalization

- The secular function has one zero in each `(j,j+1)`. The sign convention in equation (secular) is correct: the update characteristic equation is `1+gamma sum_i (i-nu)^-1=0`.
- At `theta=gamma/2`, its value is at most `-1+8gamma<0`; at `theta=2gamma`, its value is at least `1/2-8gamma>0`. Strict monotonicity gives the claimed bracket. The rough bound `|S_j|<=8` is comfortably valid in the specified bulk. Pairing terms controls the summable part, and the remaining harmonic tail has bounded endpoint ratio.
- For `theta<=2gamma<=1/16`, the off-pole square sum is bounded by `2(16/15)^2 zeta(2)<4`, so the draft's upper bound eight is conservative. It follows that `N_j>=theta/sqrt(1+8theta^2)>=gamma/sqrt(8)`, and `N_j<=theta<=2gamma`.
- For `i<j`, `|i-j-theta|=j-i+theta<=j-i+1`, giving the claimed overlap-square lower bound.

## Cutoff ranks and Hilbert–Schmidt lower bound

- A cutoff in the displayed interval lies above both old and new eigenvalues numbered `k`, and below both numbered `k+1`. Both projectors have rank `k`; the zero eigenvector is excluded from both.
- Put `q=r/16`. Since `r` is divisible by sixteen, the floor is redundant but harmless. For every cutoff index in `[3r/8,5r/8]`, the columns `j=k+1,...,k+q` remain in the bulk. The retained rows also exist.
- Retaining pairs `a+b=h` gives exactly `h` terms for each `1<=h<=q`. The inequality `h/(h+1)^2>=1/(4h)` produces cross-leakage at least `gamma^2 H_q/32`.
- Equal ranks give `||P-Q||_F^2=2 tr[P(I-Q)]`, establishing the coefficient `gamma^2/16` and `H_q>=log(q+1)`.

## Many nonnegligible singular values

- The geometric index blocks are disjoint and remain within the bulk. The restriction `2Q^ell<=r/16` is more conservative than necessary and causes no endpoint problem.
- The column normalization yields `c_h=sqrt(R_h)/sqrt(sum_{b in block_h}N_(k+b)^-2)`, so `min N<=c_h<=max N`.
- The diagonal of `K` is at least `1/5`. The off-diagonal row and column sums are each at most `2/(sqrt(Q)-1)=2/255`, which is below `1/30`. Therefore the off-diagonal operator norm has the same bound, even though `K` need not be symmetric.
- Thus `sigma_min(K)>1/6` and `sigma_min(K diag(c))>gamma/(6sqrt(8))>gamma/20`. Orthogonal compression cannot increase a singular value, so at least `s` singular values of the full cross-overlap matrix meet this threshold.
- For equal-rank orthogonal projectors, each nonzero principal-angle sine appears twice in the singular spectrum of `P-Q`. The claimed count `2s` is correct. For small dimensions `s` may be zero; the displayed finite theorem still holds and the asymptotic is logarithmic.

## Integrated bound

There are at least `r/4` disjoint equal-rank windows, each of length `(1-2gamma)delta/r`, with upper endpoint at most `1+delta`. Their total logarithmic measure is at least

`delta (1-2gamma)/(4(1+delta)) >= 5delta/32`,

using `gamma<=1/32` and `delta<=1/2`. Multiplying the Hilbert–Schmidt lower bound gives a coefficient at least `5/512`, which exceeds the stated `1/128`. Division by `log(1+tau)<=gamma delta` yields the diverging lower ratio `gamma log(q+1)/128`.

## First-draft corrections: resolved

The following records the original requests. Both are resolved in the current source: equation `(norms)` now has the intended spacing command, and Theorem 2 proves the stronger fixed-prescribed-leverage rank obstruction needed for the introduction's dimension-independent-count claim.

1. Equation `(norms)` contains literal `}quad(i<j)`; replace it by `}\quad(i<j)`.
2. The introduction says the example refutes “an n-independent bound on the number of projector singular values above a fixed tolerance determined by tau.” Its quantified theorem has **varying** `tau -> 0`. It refutes determinant-style budget bounds and, more generally, monotone-in-budget bounds that stay bounded as the budget decreases; it does not, by itself, rule out every conceivable function `F(tau,eta)` that could diverge as `tau -> 0`. State the exact coexistence of `tau -> 0` and `Omega(log n)` singular values above the fixed `gamma/20` threshold, or explicitly specify the class of budget bounds being falsified.

The integral target with universal `K` is fully and unambiguously falsified by the theorem. No repair to that statement is needed.

## Additional audit: extension at exactly prescribed leverage

The parent proposed a stronger extension after the first-draft audit. I have now read and checked its incorporated statement and proof as Theorem 2, label `thm:fixedtau`, in `projector-no-go.tex`. This extension is valid and removes the count-quantifier caveat in item 2 above.

Keep the same reference graph, put

`a_r = (1/r) sum_(i=1)^r (1+delta i/r)^-1`,

and, for any prescribed fixed `tau_0>0`, choose `d=tau_0/(2a_r)` and `gamma=2d/delta=tau_0/(delta a_r)`. The graph leverage is **exactly** `tau_0`, because `b^T L^dagger b=2a_r`. For all sufficiently large `r`, `gamma>=1/32`.

Set `c=1/64` and `F_j(theta)=sum_(i=1)^r(i-j-theta)^-1`. For bulk `r/4<=j<=3r/4`, the earlier bound gives `F_j(c)<=-64+8=-56`. The exact reflection identity is

`F_j(1-c) = -F_(r-j)(c)`.

It follows by substituting `h=r+1-i`; the mirror index is `r-j`, not `r+1-j`. That index remains in the stated bulk. Hence `F_j(1-c)>=56`. The secular function `1+gamma F_j(theta)` is negative at `c` (at most `-3/4`) and positive at `1-c`; strict monotonicity gives

`1/64 <= theta_j <= 63/64`.

For the eigenvector coefficient, split off the two nearest poles, at indices `j` and `j+1`. Their combined squared denominator contribution is at most `2*64^2`. The remaining terms sum to at most `2 zeta(2)<4`. Consequently

`N_j^-2 < 8196 < 10000`, so `N_j>1/100`.

The bound `N_j<=1` is conservative. With `theta_j<1`, the same Cauchy compression has diagonal `K_ll>=1/5`, off-diagonal norm at most `2/255`, and `sigma_min(K)>1/6`. Column normalization now gives `c_l>=1/100`; therefore `sigma_min(T)>1/600`.

Cutoffs between `1+(delta/r)(k+63/64)` and `1+(delta/r)(k+1)` have equal rank `k`. Each resulting projector difference has at least `2s=Omega(log n)` singular values above `1/600`. Thus, for every fixed prescribed `tau_0>0` and every fixed tolerance `eta<1/600`, **no finite dimension-independent count bound `F(tau_0,eta)` can hold over these weighted graphs**. In particular, the obstruction applies even to an arbitrarily small but fixed positive leverage.

The integrated-budget counterexample should continue to use the original small-`gamma` family. The fixed-leverage extension independently establishes the stronger rank-count obstruction; its displayed spectral windows shrink with `n`, so its pointwise rank lower bound alone does not establish a divergent integrated ratio at fixed leverage.

## Literature and scope

The citations to the Anderson mechanism, Gebert's rank-one determinant formula, and Pushnitski's scattering/noncompactness result are appropriate as motivation and novelty boundaries. The finite proof does not depend on any unverified infinite-volume transfer. The example is a weighted complete graph of growing degree, with no normalized-degree mass convention. It proves a projector obstruction; it does not prove a corresponding lower bound on recourse for a balanced-cut algorithm.
