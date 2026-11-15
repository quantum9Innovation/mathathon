# Accepted review of m4: scalar near-Perron reduction

## Outcome

Accepted the deterministic near-$d$ reduction and threshold analysis, with the
resolvent inputs supplied separately by accepted exterior proofs.

The top eigenvalue satisfies an exact scaled equation. If
$t=n(\lambda_1-d)$ and $\Gamma_n(\lambda)$ is the Perron-orthogonal resolvent
quadratic form, then

$$t(d-\Gamma_n(d+t/n)) + t^2/n = \Delta^2.$$

This isolates the single scalar $\Gamma_n(d)=\mathbf1_T^TL_n^+\mathbf1_T$. A fixed
spectral gap turned that scalar's convergence into the leading $1/n$ correction with
an explicit error estimate. Such control is now available for fixed separated labels
from the rank-one exterior proof already accepted in this batch.

## Root and threshold content

The exterior fixed point of $\lambda=\Delta G_d(\lambda)$ exists exactly when
$\Delta>2(d-2)$. Its edge behaviour has quadratic deviation in $\Delta-2(d-2)$ with
the claimed coefficient. The limit $\lambda_f=d$ requires
$\Delta=d^2(d-2)/(d-1)$, which is nonintegral for every integer $d\ge3$. This is the
same exclusion used in the m5 and m2 reviews. The general-critical section is not
accepted for the integer graph model.

**Scope corrections:** T1 is a leading limit, not an exact finite-$n$ equality. T3
is conditional on named inputs and gives a trace average, not a prescribed-vertex
statement. Disconnected raw examples with unbounded or negative numerical $\Gamma$
were excluded and are not used numerically to support any conclusion.

## Checks run

- `scripts/check_star_equation.py`: five affine-root versus direct-eigenvalue
  comparisons, maximum discrepancy at most $1.5\cdot10^{-11}$.
- `scripts/check_identities.py`: exact Schur identity, tree moments and Kesten-McKay
  special values passed.
- The reported threshold-edge expansion agrees with independent numerical calculation
  near $\Delta=2(d-2)$.

No bulk, clustered-set, growing-defect, formal-proof or novelty assertion is accepted
from this supplement. It is a useful proof refinement and a second ordering check,
not another required resolvent estimate.
