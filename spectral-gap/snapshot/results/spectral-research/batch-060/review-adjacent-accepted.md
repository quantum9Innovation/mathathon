# Accepted clustered family: an adjacent attachment pair

## Decision

Accepted m4/d1 as the first complete clustered-attachment secular law.

For a uniformly random simple $d$-regular host, take a fixed centre label $c$ and its
least-labelled neighbour $u_n$. Add one new vertex connected to both. For every compact
real interval in $(2\sqrt{d-1},d)\cup(d,\infty)$, the off-diagonal resolvent limit is

$$-K_{\rm adj}(\lambda)=-\frac{2r(\lambda)}{1-r(\lambda)}
=-G_d(\lambda)(2+2r(\lambda)).$$

This is proved with the marked-tree embedding and rank-one Perron expansion. It is not
transferred from the separated-label theorem.

## Root and eigenvalue outcome

The pattern limit $\Phi_{\rm adj}(\lambda)=\lambda-K_{\rm adj}(\lambda)$ is strictly
increasing on the physical exterior branch. The edge kernel is

$$K_{\rm adj}(2\sqrt{d-1})=\frac{2}{\sqrt{d-1}-1}.$$

Thus, among integer $d\ge3$, a unique simple exterior root exists **only at $d=3$**:

$$r_*^3+\tfrac12r_*-\tfrac12=0,\qquad
\lambda_*=2r_*+1/r_*=2.8751297941627788\ldots$$

Equivalently $\lambda_*^3-\lambda_*^2-4\lambda_*-4=0$.

For $d=3$, $\lambda_2(G_n')\to\lambda_*$ and $\lambda_1(G_n')\to3$.
For $d\ge4$, there is no exterior root and $\lambda_2(G_n')\to2\sqrt{d-1}$.

The positive root of the elimination cubic at $d\ge4$ is spurious: it belongs to the
large root of $(d-1)r+1/r$, not the physical root. The reviewer checked this difference
in [the independent branch audit](review-adjacent.py) and [JSON output](review-adjacent.json).

## Perron correction

$$\Phi_{\rm adj}(d)=\frac{d^2-2d-2}{d-2}\ne0,\qquad
n(\lambda_1(G_n')-d)\to\frac4{\Phi_{\rm adj}(d)}
=\frac{4(d-2)}{d^2-2d-2}.$$

At $d=3,4$ this gives $4,4/3$, genuinely different from the separated-pair constants
$12/5,16/13$. The dominant $0.0467$ second-eigenvalue shift at $d=3$ is qualitative
evidence that degree alone is not the right pattern invariant.

## Review errata and preservation

- The new batch target's edge expression is wrong by $\sqrt{d-1}$. The correct kernel
  and revised degree classification are recorded above, not silently inherited.
- The frozen identity in `m2/proof.md` is missing $+P/\lambda$ in its displayed
  resolvent series. Its one-term repair was verified in exact rational arithmetic
  against a tail bound. The old files are unchanged and a separate erratum preserves
  them. No separated limit or finite-size constant changes.
- The frozen m6 diagonal $r(\lambda-\Delta r+r)/(\lambda-\Delta r)$ is algebraically
  identical to $r+r^2/(\lambda-\Delta r)$. It is not defective. The incorrect
  diagonal in the new target must not be used to accuse that earlier accepted formula.

## Executed checks

- m4's three exact-check scripts all completed with no failures.
- `check_rank_one_identity.py` found and fixes exactly the missing scalar.
- The independent [root audit](review-adjacent.py) passed the physical-cubic-root and
  spurious-branch checks, including $\Phi>1$ on the spurious branch for $d=4,5,6$.
- m4's fixed-seed direct comparisons and m1's independent seed rows are preserved.
  At $n=8000$, measured adjacent-pair averages sit within about 0.001 of the theorem's
  limiting root. Numerics remain corroboration only.

Scope: the adjacent pair at fixed $d\ge3$. No general-pattern, bulk, growing-defect or
novelty certification is inferred from this acceptance.
