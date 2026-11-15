# Gate A decision

**Status: passed with a corrected scope, at about 47 minutes of swarm elapsed time.**

The deterministic fixed-label hypothesis survives with an explicit separation condition.
On the required high-probability tree-like event, vertices at a fixed label set have
disjoint history forests. The old finite-pattern degree reading is not retained without
that separation.

## Surviving model

The host is a uniform random simple $d$-regular graph with fixed integer $d\ge3$. The
attachment set $T$ is deterministic with fixed $\Delta=|T|$. With probability tending
to one, its short-radius neighbourhoods are trees and pairwise distances at scale
$L=c\log_{d-1}n$ exceed $2L$. Then the exterior resolvent limit is the full
Kesten-McKay diagonal sum, not the one-sided branch.

Two independent accepted arguments establish this limit in probability, with the
uniform-on-compact version valid on intervals strictly away from the tree bulk and the
Perron eigenvalue. The moment/Chebyshev route supplies a fixed-energy power rate in
$n$, not an edge-uniform rate.

The finite-root reduction gives the limiting first and second eigenvalue formulas for
this separated model, including the limiting bulk edge for $\Delta\le2(d-2)$.
Critical $\lambda_f=d$ requires nonintegral $\Delta$ for every integer $d\ge3$, so the
flawed generic treatment of that case in m5 is excluded explicitly.

## Replaced overclaim

Bounded-diameter patterns create persistent off-diagonal tree terms. Adjacent
attachment vertices and $T=N(c)$ have resolvent equal to tree coordinates weighted by
$r^{\operatorname{dist}(s,t)}$. Therefore $\Delta>2(d-2)$ and a degree-only census
interpretation must not be used for those clustered sets.

## Review position at this gate

Three submissions are accepted with documented scope. Three members remain active on
independent nonbacktracking, scaling and adversarial routes. No batch state, swarm
verdict or calculation has exceeded its fixed deadline. Gate A does not close the
batch, and it does not turn the accepted theorem into an edge, $1/n$, clustered or
general-growth result.
