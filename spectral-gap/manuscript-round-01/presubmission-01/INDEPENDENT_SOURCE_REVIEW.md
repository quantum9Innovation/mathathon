# Independent source review for problem 21

Checked 15 November 2026 UTC. Scope: the published conditioning formula behind Section 7 and the newly identified paper arXiv:2611.07104v1. This supplements the frozen priority audit without changing it. The earlier check of arXiv:2610.36320 was not repeated.

Both Section 7 counterexamples apply to the published formula exactly. A material attribution addition is needed for the elementary falling-factorial bound used in the mixed theorem. No duplicate of the refined mixed estimate or the diagonal transition statements was found in the newly inspected paper. This is a bounded source comparison, not a certificate of historical priority.

## 1. Published Bordenave article

Source: Charles Bordenave, *A new proof of Friedman's second eigenvalue theorem and its extension to random lifts*, Annales scientifiques de l'École normale supérieure, series 4, 53(6), 2020, pages 1393 to 1439. [Publisher DOI](https://doi.org/10.24033/asens.2450).

The supplied full publisher PDF has 50 PDF pages and SHA256 `3525c6b35737292db97d165ca38bdead95a991cef27a8d7a1e39d86b27fa58bc`. Its cover and article opening identify the journal version. Printed pages 1426, 1427 and 1428 are PDF pages 36, 37 and 38. All PDF page numbers here are one-based.

| Location | Relevant content checked |
| --- | --- |
| Printed 1426, Proposition 28 | The hypotheses allow arbitrary repeated or inconsistent requested cells and require $1\leq k_0\leq k\leq\sqrt n$. |
| Printed 1427, proof steps 1 and 2 | Reduction to a single uniform permutation, followed by definitions of the distinct cells, $T,T^*,S$, and $Q$. |
| Printed 1428, equation (62) | The conditional assertion is stated for every $t\in[a]$. Its conditioning includes both images and preimages. |
| Printed 1428, equation (64) | A raw factor is subsequently bounded by $1/(n-a+1)$ under the same conditioning. |

In the manuscript's notation the conditioning is

\[
\mathcal F_t=\sigma\bigl(\sigma(i_s),\sigma^{-1}(j_s):s\ne t\bigr).
\]

The published equation (62) is

\[
\mathbb P(M_{i_tj_t}=1\mid\mathcal F_t)
=\frac{\mathbf 1_{\Omega_t^c}}{n_t}
\leq\frac1{n-a+1},
\qquad
n_t=n-\bigl|\{\sigma(i_s):s\ne t\}\bigr|,
\]

where \(\Omega_t\) occurs when some \(s\ne t\) has \(\sigma(i_s)=j_t\) or \(\sigma^{-1}(j_s)=i_t\). There is no displayed restriction here to unexposed cells or to cells in a particular auxiliary set. The formula and definitions match those tested in Section 7.

### 1.1 Shared row

Take $n=4$, $y_1=(1,1)$, and $y_2=(1,2)$. The sigma algebra \(\mathcal F_1\) contains \(\sigma(1)\), so the target indicator is measurable. On \(\sigma(1)=1\), its conditional expectation is one. This event has probability $1/4$. The event \(\Omega_1\) holds and the formula gives zero. The proposed upper bound is $1/3$.

The event is a union of three atoms of \(\mathcal F_1\), distinguished by \(\sigma^{-1}(2)\in\{2,3,4\}\). Each atom contains two of the 24 permutations and has actual conditional probability one. Thus the conclusion is an almost-sure conditional statement on a positive-probability event, with no substitution of a coarser conditioning.

### 1.2 Two exposed arrows

Take $n=4$, $y_1=(1,1)$, and $y_2=(2,2)$. The atom

\[
\sigma(2)=3,\qquad \sigma^{-1}(2)=4
\]

fixes $2\mapsto3$ and $4\mapsto2$. It contains two permutations and has probability $1/12$. The two remaining rows are 1 and 3, and the two remaining columns are 1 and 4. Exactly one of the two completions has \(\sigma(1)=1\), so the conditional probability is $1/2$. Neither clause of \(\Omega_1\) holds. The published denominator counts only the image \(\sigma(2)=3\), giving $n_t=3$. Both the asserted value and the asserted upper bound are therefore $1/3$.

This example tests an unexposed target. Its failure comes from omitting the second arrow revealed by a preimage.

### 1.3 Compatibility with the proof's auxiliary sets

Both examples have $a=k=2\leq\sqrt4$. They can also be realized within the $Q$ stage of the published proof. Put the centered factor at $y_2$ first and the raw factor at $y_1$ second, so $k_0=1$. The tested cell $y_1$ is raw and therefore is not in $T$, $T^*$, or $S$. It belongs to $Q$. The same events then violate the conditional bound (64) for this raw factor.

This realization avoids relying on the all-centered consistent case, in which the tested cell can belong to $T^*$. It is a supplementary check. The manuscript's narrower conclusion about equation (62) is already correct.

These observations refute the intermediate conditional assertion. They do not refute Proposition 28 or any spectral conclusion. The manuscript supplies a separate proof of the required mixed estimate.

All 24 permutations were independently enumerated by `reviewer/check_conditioning.py`. Exact rational outputs and the conditioning atoms are saved in `reviewer/conditioning_enumeration.json`. This enumeration corroborates the preceding direct calculation.

## 2. Bordenave and Zhu, arXiv:2611.07104v1

The verified title is *A second eigenvalue lower bound for the directed configuration model*, by Charles Bordenave and Yizhe Zhu. The abstract record lists only v1, submitted 4 November 2026 at 20:17:31 UTC, with 26 pages. No journal reference is displayed. [Version record](https://arxiv.org/abs/2611.07104v1), [versioned HTML](https://arxiv.org/html/2611.07104v1), [versioned PDF](https://arxiv.org/pdf/2611.07104v1).

Lemma 2.1, PDF pages 6 and 7, retains the mixed singleton factor \((3k/\sqrt N)^{a_1}\) in (2.1), citing Bordenave's Proposition 28. Its (2.2) gives relative error at most $2k/N$ around $1/(N)_a$ when every consistent centered edge has multiplicity at least two. Equation (2.3), PDF page 7, explicitly proves, with $F_N(q)=N^q/(N)_q$,

\[
0\leq\log F_N(a)
\leq\frac{a(a-1)}{2(N-a+1)}\leq\frac12,
\qquad a\leq k\leq\sqrt N.
\]

The following proof also uses the affine expansion of powers of a centered indicator. Section 2.6, beginning on PDF page 18, derives Gaussian moments for modified traces. Lemma 2.15, PDF page 19, fixes the moment order $p$ while the trace power grows.

### 2.1 Contribution assessment

The exact factorial inequality establishing $F_N(a)\leq\sqrt e$ is prior. Its use in a new bound does not make that scalar inequality a new contribution. The affine reduction for powers of an indicator is also not a novelty candidate.

The current manuscript's refined mixed conclusion, with $h$ consistent centered singletons and $b$ inconsistent centered singletons among $a$ distinct cells, is

\[
|\mathbb EP|\leq 2^b N^{-a}\beta^h F_N(a-h),
\qquad
\beta=\frac{\sqrt{a-1}}{\sqrt N-\sqrt{a-1}}.
\]

The potentially distinct content is the improved consistent-singleton dependence, the dependence on the number of distinct cells, and the factor with index $a-h$. The newly inspected statement does not supply these. Its repeated-edge asymptotic excludes singleton cells, so it does not settle the manuscript's diagonal product of distinct centered indicators.

No statement of the manuscript's exact cubic criterion, parity-dependent hyperbolic transition, relative window $k=o(\sqrt N)$, or boundary ratio $\exp(d/4)$ was located in the inspected paper. The trace moment limit concerns a different observable and fixes its moment order. This comparison is evidence against an exact duplication in this paper, not evidence that the broader literature has been exhausted.

Suggested attribution language:

> The mixed estimate refines the consistent-singleton dependence in Bordenave's Proposition 28. The falling-factorial inequality used to obtain its \(\sqrt e\) corollary already appears in Bordenave and Zhu, Lemma 2.1, equation (2.3). Their repeated-edge estimate concerns products with every multiplicity at least two. The diagonal results here concern distinct centered cells and quantify the cubic transition and its extension toward the square-root scale.

The optimal universal prefactor claim should refer to the manuscript's complete mixed inequality and its lower-bound witness. It should not describe the scalar bound $F_N(a)\leq\sqrt e$ itself as newly discovered.

## 3. Access and scope limits

The full Bordenave journal PDF was available locally and the relevant three pages were checked both through text extraction and rendered page images. This closes the old audit's specific limitation that the journal proof had not been inspected.

The new paper's complete versioned HTML and PDF text were accessible through the web reader. PDF and HTML equation numbering diverge later in the paper, so the page references above use the PDF. Lemma 2.1 and equations (2.1) through (2.3) agree between the two formats. A direct local PDF download failed because the local command could not resolve arxiv.org. Web screenshot requests also failed. Accordingly, no local PDF hash or visual PDF verification is claimed for this paper.

The focused comparison read the main statements, Section 2.1, and Section 2.6, and searched the full HTML for `cosh`, `sinh`, `cubic`, `Laguerre`, `Kummer`, and `diagonal`. These searches returned no matches. Absence of those words is only a locating aid. The conclusion rests on the observables and assumptions of the statements inspected, not on keyword absence alone. No audit of the new paper's full spectral proof was attempted.

This pass did not repeat the broader searches or reclassify all prior candidates in the frozen priority audit. A new public paper, an unindexed result, or a specialist's identification of an equivalent asymptotic could change the historical assessment.

## 4. Minimal bibliography addition

Bordenave, Charles, and Yizhe Zhu. *A second eigenvalue lower bound for the directed configuration model*. arXiv:2611.07104v1, 4 November 2026. [Primary record](https://arxiv.org/abs/2611.07104v1).

For the conditioning discussion, cite the existing Bordenave journal entry with equation (62), printed page 1428, and Proposition 28, printed page 1426. The arXiv version 4 page number may be retained as an additional locator, not the sole locator.
