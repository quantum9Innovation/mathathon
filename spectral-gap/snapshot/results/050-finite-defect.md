# Batch 050: finite-defect resolvent and limiting eigenvalues

## State

**Done: proof-level results accepted for the stated fixed-degree, fixed-label
setting.** Swarm `smwgwbyn9` is solved with six accepted submissions. Two submissions
were returned for revision before acceptance. No live members or background jobs
remain. Every mathematical claim below is bounded by the stated scope.

This is a referee report, not a comprehensive novelty claim or proof-assistant
certificate. The strongest results are the exterior resolvent theorem, the limiting
top-two-eigenvalue formula, and a rigorously proved leading $1/n$ correction.

## 1. Main theorem

Fix integers $d\ge3$ and $\Delta\ge1$. Let $G_n$ be a uniformly random simple
$d$-regular graph on $[n]$, and let $T=\{1,\ldots,\Delta\}$ be a deterministic label
set. Add one vertex adjacent exactly to $T$, obtaining $G_n'$. Write $A_n$ for the
host adjacency and $\lambda_1,\lambda_2$ for the two largest eigenvalues by value.

Let $G_d$ be the full Kesten-McKay Stieltjes transform of the $d$-regular tree. For
$\lambda>2\sqrt{d-1}$,
$$
r(\lambda)=\frac{\lambda-\sqrt{\lambda^2-4(d-1)}}{2(d-1)},
\qquad G_d(\lambda)=\frac{r(\lambda)}{1-r(\lambda)^2}.
$$
This is not the one-sided tree resolvent $r$. Let $f(\lambda)=\lambda-\Delta G_d(\lambda)$.
If $\Delta>2(d-2)$, $f$ has a unique simple exterior root $\lambda_f$, satisfying
$$
\lambda_f^2=\frac{d^2-(d-2)\Delta+
\sqrt{(d^2-(d-2)\Delta)^2+4(d-1)\Delta^2}}{2}.
$$
Otherwise set $\lambda_f=2\sqrt{d-1}$.

### Resolvent limit

For every compact real interval
$K\subset(2\sqrt{d-1},d)\cup(d,\infty)$,
$$
\sup_{\lambda\in K}
\left|\mathbf1_T^T(A_n-\lambda I)^{-1}\mathbf1_T+\Delta G_d(\lambda)\right|
\longrightarrow0
$$
in probability. This holds for fixed $d$, $T$ and degree $d_n=d$ in the graph,
not a growing-degree or empirical-measure statement. Pairwise label distances grow
logarithmically at the required scale with high probability.

### Limiting eigenvalues

In probability,
$$
\lambda_1(G'_n)\to\max(d,\lambda_f),\qquad
\lambda_2(G'_n)\to\min(d,\lambda_f).
$$
For $\Delta\le2(d-2)$, this includes $\lambda_2\to2\sqrt{d-1}$, using host
interlacing for the lower bound. The exact host-Perron multiplicity and root
branches are controlled. For integer $d\ge3$,
$\Delta=d^2(d-2)/(d-1)$ cannot occur, since that value is nonintegral. Thus
$\lambda_f=d$ is excluded rather than being attached to an invalid critical-size
argument.

### The $1/n$ correction near $d$

When $\Delta G_d(d)>d$, equivalently $\Delta>d^2(d-2)/(d-1)$,
$$
n(d-\lambda_2(G_n'))\longrightarrow
\frac{\Delta^2}{\Delta G_d(d)-d}
$$
in probability. The proof establishes the stronger scaled error
$O(\log n/n)$ about the limiting value.

For the complementary root above $d$, one similarly obtains
$$
n(\lambda_1(G_n')-d)\longrightarrow
\frac{\Delta^2}{d-\Delta G_d(d)},
$$
where $G_d(d)=(d-1)/(d(d-2))$. The first correction holds when $\lambda_f>d$,
the second when $\lambda_f<d$.

## 2. The proof mechanism that closed the problem

The decisive input is an exact rank-one splitting, $A'=A-dP$ with
$P=\mathbf1\mathbf1^T/n$. Then $PA'=A'P=0$, and for $k\ge1$,
$$
(A'^k)_{yy'}=(A^k)_{yy'}-\frac{d^k}{n}.
$$
Consequently
$$
(A-\lambda I)^{-1}=\frac{P}{d-\lambda}
-\sum_{k\ge0}\frac{A'^k}{\lambda^{k+1}},
$$
with norm convergence whenever $\lambda>\|A'\|$. Friedman's fixed-degree theorem,
with Bordenave's subsequent proof, makes $\|A'\|<2\sqrt{d-1}+\varepsilon$ with high
probability. Thus the exterior domain is directly accessible. No bulk local-law
limit or general second-moment heuristic is required.

The other key probability estimate is radius-$L$ tree-likeness and separation at
fixed labels, with failure probability $O((d-1)^{2L}/n)$ in the pairing model.
Conditioning on simplicity gives the uniform simple graph, exactly because every
simple $d$-regular graph has $(d!)^n$ pairings. Simplicity then has a positive limit
probability by the cited enumeration theorem.

At $\lambda=d-s/n$ with bounded $s>0$ and $\Delta G_d(d)>d$, the secular function
has expansion
$$
\Sigma_n(d-s/n)=f(d-s/n)+\frac{\Delta^2}{s}+O(\log n/n).
$$
The operator-tail and tree-tail terms are geometric. The finite rank-one correction
terms are $O(L/n)$. Taylor expansion of the continuous $C^1$ function $f$, itself a
finite integral of smooth real-energy functions away from the bulk branch cut, plus
uniqueness of the gap root gives the $1/n$ eigenvalue correction.

Two independent accepted approaches corroborate the exterior limit: a
Chebyshev-moment approximation and an analytic walk/Vitali argument. They were not
needed for the final near-$d$ estimate.

## 3. Corrections established by the batch

1. **Separated versus clustered attachment sets.** On the regular tree,
   $(\lambda-A)^{-1}_{st}=G_d(\lambda)r(\lambda)^{\operatorname{dist}(s,t)}$.
   Hence bounded-diameter patterns retain off-diagonal terms. The limit
   $-\Delta G_d$ is for fixed labels with asymptotically separated positions, not
   adjacent pairs or neighbours of one centre. The latter needs the corrected
   sum of all ordered pair distances.
2. **The secular Perron sign.** The exact term is
   $\Delta^2/(n(d-\lambda))$, not $\Delta^2/(n(\lambda-d))$, when $\Sigma_n$ is
   written with the resolvent factor $\lambda+\mathbf1_T^T(A-\lambda I)^{-1}\mathbf1_T$.
3. **The full versus one-sided transform.** Using $r$ in place of $G_d=r/(1-r^2)$
   moves the threshold from $2(d-2)$ to the different tree threshold $2(d-1)$.
4. **Hölder edge scaling.** As $\Delta\downarrow2(d-2)$,
   $\lambda_f-2\sqrt{d-1}\sim
   \frac{\sqrt{d-1}}{4d^2}(\Delta-2(d-2))^2$.
5. **Host multiplicity sharpening.** Orthogonality of $\mathbf1_T$ to a host
   eigenspace does not necessarily preserve its multiplicity. There is an exact
   pseudoinverse criterion for increasing it by one, in addition to the expected
   eigenvalue-loss case.

The first m6 Montel proof was initially rejected for invalid tightness handling.
It was revised to use a genuine continuous resolvent bound on the spectral event.
The first m3 Harnack proof was rejected for a boundedness/domain gap and an unjustified
near-$d$ bound. The revision fixed the bounded-domain step and withdrew the rate
claim. The stronger rank-one proof above supplies that rate independently.

## 4. What was actually verified

- [m1 moment review](spectral-research/batch-050/review-m1-accepted.md): exact moments, source checks and accepted interior root.
- [m2 rank-one and finite-size review](spectral-research/batch-050/review-m2-accepted.md): the strongest theorem, exact algebra and the scaled error.
- [m3 revised analytic proof](spectral-research/batch-050/review-m3-revised-accepted.md): repaired bounded-domain continuation and withdrawal of the unproved near-$d$ estimate.
- [m4 scalar near-$d$ review](spectral-research/batch-050/review-m4-accepted.md): exact affine root equation and threshold expansion.
- [m5 finite-root review](spectral-research/batch-050/review-m5-accepted.md): interlacing, exact multiplicity cases and both root orderings.
- [m6 revised pattern review](spectral-research/batch-050/review-m6-revised-accepted.md): bounded-pattern resolvent values and repaired stochastic-Vitali proof.
- [host-pole analysis](spectral-research/batch-050/host-pole-analysis.md) and [Gate A record](spectral-research/batch-050/gate-A.md).

Executed checks included exact transform identities, all 149009 host-pole
multiplicity comparisons with zero mismatches, five affine-root/eigensolver
comparisons with maximum error $1.5\times10^{-11}$, and reimplemented
Cauchy-kernel checks in `chebyshev_review.py`. The official Bordenave and Friedman
statements were inspected at the actual applicable places.

The completed background numerical run `jmwgyi9le` gave, at $(d,\Delta)=(3,6)$,
$$n(d-\lambda_2)=30.7732,\ 33.7244,\ 35.9384,\ 36.1716$$
for $n=1000,2000,4000,8000$, approaching the predicted $36$. Direct eigenvalue and
secular-root discrepancies were at most $4.02\times10^{-11}$.

Numerics are corroboration, not the source of any theorem here. No Lean verification
was run. No exhaustive forward-and-backward citation audit establishes novelty.

## 5. What remains open

- A full resolvent and root theory for clustered attachment patterns, not merely
  their tree-coordinate formulas.
- Rates uniform up to the bulk edge and a bulk-edge fluctuation theorem.
- Growing defect sets, multi-defect interactions and general random attachment.
- Exhaustive literature comparison for the assembled results. They are theorem-level
  advances over the previous conditional dossier, not automatically new to the field.

## Next action

Write a precise publication-style proof of the rank-one theorem and its scaled
finite-size corollary, while independently reproducing all input hypotheses. Do not
spend the next batch on bulk resolvent theory merely because it is available. The
cleanest remaining direction is a complete clustered-pattern secular law, starting
with an adjacent pair and $T=N(c)$ and verifying the analogous root calculation.
