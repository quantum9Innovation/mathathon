# Accepted review of m1: fixed-set resolvent limit

## Decision and scope

Accepted. This is a proof-level fixed-degree component. It establishes the resolvent
limit in probability for deterministic fixed labels and uniformly on compact real
subsets of the exterior window. It also proves the limiting defect eigenvalue near a
simple isolated zero below $d$.

It does not establish the full top-one/top-two ordering, the near-$d$ correction,
uniformity up to the bulk edge, growing or clustered sets, or novelty. These exclusions
are not stylistic. They belong in any later theorem statement.

## Core proof audit

Let $T$ be a fixed $\Delta$-set. The pairing-model exploration bounds the failure of
radius-$L$ tree-likeness and separation by $O((d-1)^{2L}/n)$, with transfer to the
uniform simple model through a positive simplicity probability. For polynomials of
degree at most $2L$, the $T$ spectral measure therefore has exactly $\Delta$ times the
Kesten-McKay moments on the good event.

For real $\lambda>2\sqrt{d-1}+\varepsilon$, the Cauchy kernel on the non-Perron
spectral interval has a degree-$2L$ polynomial approximation with error controlled by
the Chebyshev parameter. The sign convention is

$$f(x)=\frac1{x-\lambda}=-\frac1\alpha\frac1{\tau-x/\alpha},
\qquad \tau=\lambda/\alpha.$$

This matters for independent reimplementation. The approximation of $1/(t-x)$ is
positive, not the desired signed graph kernel. The exact scaling is then part of $q$.

On the good event, write the spectral measure as the non-Perron part plus the Perron
mass $\Delta^2/n$ at $d$. On the non-Perron support, approximation reduces the
quadratic form to matched moments. Removed Perron terms sum to

$$\frac{\Delta^2}{n}\left(\frac1{d-\lambda}-q(d)\right),$$

which is $O(1/n)$ for fixed $\lambda$ because Chebyshev polynomials grow polynomially
or exponentially with exponent controlled by that degree. The non-Perron integral then
identifies $-\Delta G_d(\lambda)$ with a vanishing error. Taking
$2L\sim(1-\gamma)\log_{d-1}n$ balances tree-likeness against Chebyshev decay.

Uniformity on a compact interval follows because the same high-probability event and
a fixed support slack apply to the whole interval, and $\varrho$ is controlled at its
worst endpoint. No claim of uniformity up to the bulk edge is accepted.

## Root corollary audit

On a compact $K\subset(2\sqrt{d-1},d)$, the host spectrum is absent with probability
tending to one. Then the added-vertex secular polynomial captures exactly all new
eigenvalues in $K$. Uniform convergence to $\lambda-\Delta G_d$ and the derivative
condition $1-\Delta G_d'>0$ gives one limiting zero when that root exists. The zero is
simple except for the original bulk-edge case, which is outside the accepted scope.

## Checks run

- `python3 scripts/verify_moments.py` in the member workspace: all moments through
  degree 12 agreed for $d=3,4,5,6$.
- [Independent Cauchy and Perron evaluation](chebyshev_review.py), with [output](chebyshev_review.json).
  The first implementation had the reviewer's mistaken sign and factor conventions,
  corrected before the passing run. No member code was imported for that check.
- The local primary Friedman PDF was fetched and its Corollary 1.4, domination and
  uniform-simple discussion read, including the last passage on PDF page 4.
- The earlier m6 Monte Carlo route does not replace the need for analytic verification.
  Its own stochastic-Montel proof was returned for revision, not used here.
