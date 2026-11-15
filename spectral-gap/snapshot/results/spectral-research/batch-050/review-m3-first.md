# First review of m3: required corrections

## Decision

Returned for revision. The tree and Perron-removal calculations are promising, but the
full submission overstates what the resolvent limit proves near $d$.

## Algebraic verification

The old output file reports that every check A failed. Executing `checkA` from the
current `scripts/check_theorem.py` returned `True` for all five named graphs. Explicit
exact $K_4$ calculations also passed for every $\Delta=1,2,3$ and the three rational
energies. The raw file is stale and should be regenerated, not read as a failed proof
of the current identity.

The sign correction is valid: the host's Perron contribution to the secular function
is $\Delta^2/(n(d-\lambda))$, not $\Delta^2/(n(\lambda-d))$. The adjacent-pair
calculation and the observation that $\lambda_f=d$ cannot occur for the integer model
are consistent with the other accepted results.

## Gaps requiring revision

- The three-circles lemma requires a bound on a whole holomorphic domain. The current
  proof obtains its bound only on the start and target subsets. Choose a bounded
  resolvent subdomain on which the stated global bound holds, and reapply the lemma
  there. The submitted domain argument does not cover its own unbounded half-plane.
- The claimed $O(1/n)$ location of the eigenvalue near $d$ is not implied by the
  fixed-energy resolvent limit. The residual $(\lambda-d)g_n(\lambda)$ is uncontrolled
  at an unknown shrinking scale. A specific rate estimate or an alternative full
  proof is required. This overstatement is not repaired by the numerical output.

The main analytic-continuation argument should not be accepted merely because another
member obtained the same conclusion by a correct stochastic-Vitali step. Its own domain
hypotheses must be repaired separately. The finite-size coefficient and the bound near
$d$ are explicitly excluded unless a scaled estimate is later proved.
