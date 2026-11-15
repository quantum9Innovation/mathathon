# Batch 050 source baseline

## Purpose of this note

These are the exact primary theorem hooks checked during preparation. They are starting
points for proof adaptation and source rejection, not evidence that the proposed
fixed-degree resolvent limit is already known.

## Sources

1. Roland Bauerschmidt, Jiaoyang Huang and Horng-Tzer Yau,
   [Local Kesten-McKay law for random regular graphs](https://arxiv.org/abs/1609.09052v3),
   arXiv:1609.09052v3, 20 December 2016.
   [Local PDF](sources/local-kesten-mckay.pdf) and [extracted text](sources/local-kesten-mckay.txt).
   PDF SHA256 `911a36cd598132f8916e98a74479829c6f3f9bca2f485cafabb237c253a87b35`.

2. Roland Bauerschmidt, Antti Knowles and Horng-Tzer Yau,
   [Local semicircle law for random regular graphs](https://arxiv.org/abs/1503.08702v5),
   arXiv:1503.08702v5, 12 February 2017.
   [Local PDF](sources/local-semicircle.pdf) and [extracted text](sources/local-semicircle.txt).
   PDF SHA256 `0b027c2b73541aeaa1da3a7d1c1acfc1516a46d2c92cc365da80a58c9b38b302`.

Downloads were made from the official arXiv PDF URLs during batch preparation. The text
was extracted with `pdftotext -layout`. The PDFs, rather than the text reflow, control
any disputed formula.

## Exact theorem hooks and limitations

### Fixed-degree local Kesten-McKay argument

In arXiv:1609.09052v3, PDF page 10, Theorem 2.4 estimates the difference between graph
and localized tree-extension Green functions by $|m_{\rm sc}(z)|q(z)^{r_*}$, with high
probability. Its stated domain $D$ is defined on PDF page 4 as

$$z\in\mathbb C_+,\qquad \operatorname{Im}z\ge(\log N)^{48\alpha+1}/N,
\qquad |z\pm2|\ge(\log N)^{-\alpha/2+1}.$$

The theorem includes a fixed-degree lower threshold tied to $\alpha$ and $\omega$. Its
error tends to zero as $N\to\infty$ for fixed $d$ in that domain. This is not the desired
real-energy interval outside the bulk. One must first obtain the corresponding statement
at $\operatorname{Im}z\to0$ beyond the bulk edge. Taking an informal limit through the
excluded neighbourhood of $\pm2$ is not an argument.

The same paper explicitly warns after Theorem 1.1 that individual fixed-degree Green
function entries need not concentrate because bounded cycles have nonvanishing
probabilities. This directly motivates Gate A. The warning must be analyzed in the
exterior real-energy regime, not merely quoted as a proof of nonconvergence there.

An initial-estimate step elsewhere in the source treats large $|z|$. That does not prove
the full fixed-degree theorem in the required exterior window. Any extension must
identify the proof ingredient that controls the required approach to the real line.

### Growing-degree local semicircle input

In arXiv:1503.08702v5, Theorem 1.1 on PDF page 4 concerns
$H=(d-1)^{-1/2}A-dee^*$ and

$$G(z)=(H-z)^{-1},\qquad z=E+i\eta\in\mathbb C_+.$$

Under the parameters specified there, it gives errors of the form $F_z(\xi\Phi(z))$
on $\eta\gg\xi^2/N$. The theorem's degree condition $D\gg\xi^2$ imposes a growing-degree
regime. It is not a theorem for fixed $d\ge3$.

At exterior energy, the statement may offer a route through $d\to\infty$, but every
error parameter, rank-one Perron removal, rescaling and limit to the real line must be
spelled out. Weak Kesten-McKay convergence in the fixed-degree theorem background does
not give fixed-point resolvent control.

## Earlier defect results to preserve

The m5 dossier's exact added-vertex determinant identity and its exact spiked-tree
spectrum are accepted with the documented scope. Its finite-host prediction is explicitly
conjectural. Do not confuse the infinite tree's one-sided branch parameter with the full
Kesten-McKay transform, and do not replace the finite host's Perron pole with the tree
spectrum.

The accepted review is [here](../reviews/d3-first-review.md). The synthesis emphasizing
the open problem is [here](../../030-spectral-research-synthesis.md).

## Literature task still outstanding

The preparation checked these sources and conducted a targeted search. It did not
conduct a comprehensive forward-and-backward citation audit of exterior resolvent laws,
finite-rank deformations of random regular graphs or related community-detection work.
The source-applicability member must do that before any novelty claim.
