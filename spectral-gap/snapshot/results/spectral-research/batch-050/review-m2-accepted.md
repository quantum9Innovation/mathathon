# Accepted review of m2: rank-one exterior proof and finite-size law

## Outcome

Accepted the exterior resolvent theorem, the limiting top-two-eigenvalue formula and,
for separated attachment sets, the leading $1/n$ correction.

This is the strongest result reviewed in batch 050. It supplies the actual error control
near $d$ that earlier fixed-energy arguments did not provide.

## Exact decomposition

Set $P=\mathbf1\mathbf1^T/n$ and $A'=A-dP$. Commutation gives
$PA'=A'P=0$, so $(A'^k)_{yy'}=(A^k)_{yy'}-d^k/n$ for $k\ge1$. On the complement of
the Perron vector,

$$(A-\lambda I)^{-1}=\frac{P}{d-\lambda}-\sum_{k\ge0}\frac{A'^k}{\lambda^{k+1}}.$$

The series converges whenever $\lambda>\|A'\|$. A fixed-degree second-eigenvalue
theorem gives $\|A'\|<2\sqrt{d-1}+\varepsilon$ with high probability, covering the
whole real exterior window without a stochastic-Montel or complex-limit step.

The fixed-set tree/separation event makes these powers exact Kesten-McKay moments,
apart from the known $d^k/n$ term. Pairing-conditioned simplicity supplies the uniform
random simple model. Consequently the resolvent limit and limiting roots follow,
including the subcritical bulk-edge case with host interlacing for the lower bound.

## Why the $1/n$ estimate holds

Write $c_1=\Delta G_d(d)-d>0$, $\lambda=d-s/n$, and
$\Sigma_n=\lambda+\mathbf1_T^T(A-\lambda I)^{-1}\mathbf1_T$. The decomposition gives

$$\Sigma_n(d-s/n)=f(d-s/n)+\frac{\Delta^2}{s}+O(\log n/n),$$

uniformly for bounded $s$. The finite rank-one coefficients are $O(L/n)$ since
$k\le L$ and $s$ is bounded. Both operator and tree tails are geometric. There is no
uncontrolled near-pole error term. Since $f(d)=-c_1$ and
$f(d-s/n)=-c_1-f'(d)s/n+o(1/n)$, uniqueness of the gap root yields

$$s_n=\frac{\Delta^2}{c_1}+O(\log n/n).$$

So $n(d-\lambda_2(G'_n))\to\Delta^2/c_1$ in probability. This is the finite-size law
that m3 correctly withheld pending a rate estimate.

## Executed checks

- `scripts/exact_checks.py` passed all rank-one, rational secular and truncated-tree
  checks.
- The closed Kesten-McKay values, root thresholds and nonintegrality of
  $\Delta=d^2(d-2)/(d-1)$ for $d\ge3$ were checked directly.
- The official Bordenave v4 PDF was read. Theorem 1 and Equation (2) supply the cited
  uniform simple-degree spectral estimate with logarithmic failure probability.
- The bounded numerical rerun `jmwgyi9le` completed successfully after 2m34s.
  For $(d,\Delta)=(3,6)$ and fixed seed, $n(d-\lambda_2(G'_n))$ was
  $30.7732,33.7244,35.9384,36.1716$ at $n=1000,2000,4000,8000$, approaching the
  predicted value $36$. The largest discrepancy between secular roots and direct
  peak eigenvalues was $4.02\cdot10^{-11}$. The output is
  `.ultramath/smwgwbyn9/m2/out/review_d3D6.json` with log `review_d3D6.log`.

## Scope

The accepted case remains fixed $d\ge3$, fixed labels that are asymptotically
separated, and the exact added-vertex model. Clustered attachment sets need the
off-diagonal tree correction. No bulk, complex-energy, growing-defect or novelty
theorem is inferred.
