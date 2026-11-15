# Host-pole analysis after the exterior resolvent limit

## Purpose

This supplement isolates what is needed to pass from the fixed-set resolvent limit to
the two leading eigenvalues of a regular graph with one added vertex. It distinguishes
the simple exterior root from the root near the host Perron pole and from the bulk
subcritical case. It is a proof aid for independent judging, not a second swarm.

## Notation and deterministic framework

Let $G$ be connected, simple and $d$-regular, let $T$ have fixed size $\Delta$, and let
$G'$ add one vertex adjacent to exactly $T$. Put

$$F_n(\lambda)=\lambda+\mathbf1_T^T(A-\lambda I)^{-1}\mathbf1_T,
\qquad h(\lambda)=\lambda-\Delta G_d(\lambda).$$

Whenever $\lambda\notin\sigma(A)$, the eigenvalues of $G'$ captured by the exact factor
$p_G(\lambda)F_n(\lambda)$ agree with zeros of $F_n$ with their corresponding
multiplicities. On an event where the non-Perron spectrum lies in $[-b,b]$,
$b>2\sqrt{d-1}$, a uniform resolvent approximation on a compact avoiding $d$ gives

$$F_n(\lambda)=h(\lambda)+\frac{\Delta^2}{n(d-\lambda)}+o(1),$$

uniformly on that compact. Its poles are the removed host eigenvalues.

Two elementary tree facts govern the discussion:

- for $\lambda>2\sqrt{d-1}$, $-G_d'(\lambda)>0$, so $h'(\lambda)>1$,
- $\Delta>2(d-2)$ if and only if $h$ has exactly one root
  $\lambda_f>2\sqrt{d-1}$, and that root is simple,
- $\Delta G_d(d)>d$ if and only if $\Delta>d^2(d-2)/(d-1)$. Thus $\lambda_f>d$
  precisely beyond that second threshold. Equality gives $\lambda_f=d$.

For $\Delta\le2(d-2)$ there is no $h$ root above the tree bulk, including when
$\Delta=2(d-2)$ except for the endpoint root itself.

## Why the root near $d$ cannot be ignored

Since $G$ is connected, its top eigenvalue $d$ is simple. Every removed set $T$ has
its old degrees increased by one, so $G'$ is not $d$-regular and its average degree
strictly exceeds $d$. Hence $\lambda_1(G')>d$.

Cauchy interlacing after removing the new vertex gives
$\lambda_1(G')\ge d\ge\lambda_2(G')$. There is consequently **exactly one eigenvalue
strictly above $d$**. It must be near $d$ when $\lambda_f<d$, and cannot be confused
with a fixed exterior root below $d$. This already supplies the top-two ordering in
that case.

## The two sides of the pole

Choose $b$ and compact intervals on each side of $d$ with positive distance from the
bulk. To avoid the shrinking Perron pole, also choose $\sigma_n\to0$ with
$n\sigma_n\to\infty$, for example $\sigma_n=n^{-1/4}$. The host has no spectrum in
those intervals except its simple eigenvalue at $d$.

### Above $d$

At $\lambda=d-\sigma_n$, $h(d-\sigma_n)$ approaches $h(d)$, and the Perron term is
positive of order $1/(n\sigma_n)$. At $\lambda=d+\sigma_n$ it is negative of the same
order. No fixed resolvent error below $O(1)$ can defeat this pole term.

Suppose first $\Delta G_d(d)<d$. Then $h(d)>0$. Pick a small fixed $\eta>0$ so that
$h(d+\eta)>0$. The secular function is positive at $d+\eta$, and is negative at
$d+\sigma_n$ for all large $n$. Hence there is one root between
$d+\sigma_n$ and $d+\eta$. Since no other root can occur farther away from $d$ without
being the simple exterior root, and $\lambda_f<d$ here, that root is the leading
eigenvalue. Therefore $\lambda_1\to d$.

Alternatively, keeping a pole-sized window (which is not necessary for the leading
limit) and expanding $h$ at $d$ gives the formal refinement

$$\lambda_1-d\sim\frac{\Delta^2}{n(d-\Delta G_d(d))},$$

provided the resolvent error and Taylor remainder are $o(1/n)$. That refinement is not
proved by the accepted resolvent limit and should not be claimed merely by keeping the
Perron term.

### Below $d$

If $\Delta G_d(d)>d$, then $h(d)<0$. Pick fixed $\eta>0$ so that $h(d-\eta)<0$. The
Perron term is positive and dominant at $d-\sigma_n$, while the value at $d-\eta$ is
negative. So there is a root between $d-\eta$ and $d-\sigma_n$, which lies in
$(d-2\sigma_n,d-\sigma_n]$ for large $n$. The unique above-$d$ root is instead the
fixed exterior root $\lambda_f>d$. Consequently $\lambda_2\to d$ and
$\lambda_1\to\lambda_f$.

The analogous possible finite-size refinement below $d$ is

$$d-\lambda_2\sim\frac{\Delta^2}{n(\Delta G_d(d)-d)},$$

again only with $o(1/n)$ error control.

### The critical case $\Delta G_d(d)=d$

Here $h(d)=0$ but $h'(d)>1$. The same two-sided bracket gives a root above $d$ within
$o(1)$ and a root below $d$ within $o(1)$. No linearisation of the finite-size law
around $d$ is required to conclude $\lambda_1,\lambda_2\to d$. It would be
unjustified to assert a leading $1/n$ correction at this critical parameter. The
externally imposed finite root from $\lambda=\Delta G_d$ is not simple as a root with
respect to the whole enlarged model when one also includes the host pole, and must be
handled by these two-sided bounds rather than labelled a simple zero of the full
polynomial.

**Integer model qualification.** This critical case does not actually occur when
$d\ge3$ and $\Delta$ are integers. Requiring $\lambda_f=d$ forces
$\Delta=d^2(d-2)/(d-1)$, which is not integral because $d-1$ does not divide $d-2$.
The bracket clarifies the pole geometry but is unnecessary for the fixed integer
model. Its two actual cases are $\lambda_f<d$ and $\lambda_f>d$.

## Combining with the simple exterior root

If $\lambda_f$ lies in a compact $K\subset(2\sqrt{d-1},d)$, the host event excludes
its spectrum from $K$, the exact secular factor captures precisely the new eigenvalues
there, and $h'>1$ proves root simplicity. Uniform convergence then gives exactly one
eigenvalue of $G'$ in $K$ eventually, converging to $\lambda_f$.

Combining this with the pole-side calculations gives, for separated fixed labels and
$\Delta>2(d-2)$,

$$\lambda_1(G'_n)\to\max(d,\lambda_f),
\qquad \lambda_2(G'_n)\to\min(d,\lambda_f)$$

in probability, including the equality case $\lambda_f=d$.

This uses the resolvent limit only on fixed compacta. The shrinking root windows are
confirmed by the explicit Perron term, not asserted as part of uniform convergence.

## What remains distinct

For $\Delta\le2(d-2)$, excluded roots above the bulk show that no fixed eigenvalue
separates into $(2\sqrt{d-1}+\eta,d)$ for any fixed $\eta>0$ with $d$ outside that
interval. This gives the upper half of a statement $\lambda_2\to2\sqrt{d-1}$.
A matching lower bound is available without another resolvent estimate. Cauchy
interlacing gives $\lambda_2(G')\ge\lambda_2(G)$, and the known regular-host two-sided
edge law gives $\lambda_2(G)\to2\sqrt{d-1}$. This is the argument checked in the m5
submission, not an inference from $F_n$ off compact sets.

Similarly, the accepted resolvent limit does not obtain a $1/n$ correction, an edge
law, clustered-attachment corrections or growing-$\Delta$ asymptotics. The adjacent
and neighbour patterns in m6 require different resolvent sums. Their source-level
finite-pattern calculation must be coordinated with this ordering argument rather
than forcing the separated-set threshold on every attachment configuration.
