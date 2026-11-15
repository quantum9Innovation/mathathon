# Bounded priority assessment of the mixed envelope and diagonal extensions

Revision 1. Examined 15 November 2026 UTC. This is a source assessment, not a proof review or an exhaustive historical-priority determination. The original mixed packet and all earlier priority records remain frozen.

## 1. Conclusions and inspected targets

The exact attainable mixed envelope remains a defensible contribution candidate in this bounded search. The closely related centered-matrix theorem of Han and Niles-Weed does apply to the diagonal moments through an explicit specialization. It should be credited as related work. Its inspected estimate does not identify the exact mixed maximum over cell patterns, powers and independent colors.

The full range diagonal approximation reaches parameter values already treated by classical negative-parameter Laguerre asymptotics. No new macroscopic special-function regime should be claimed. The specific parity-sensitive formula, its uniform connection to small orders and its stated remainders are the candidate contributions. Their historical status remains subject to the separate special-function review, including the Whittaker route.

The mathematical targets were frozen as follows.

| Target | File | SHA256 |
| --- | --- | --- |
| Exact attainable mixed envelope SG-E3-A and scalar corollary | `../sharp-mixed-envelope-v1.md` | `878a139aee3caf6040debcc0f9b476e5fa0dd283c70c2a75a48ceaaea38d6b4d` |
| Signed correction and exact worst-case constant U1 and U2 | `../../root/uniform-first-correction-v1.md` | `14ba2a74f0a51bd63bc622a30f0ad4f1bcf0c0c5cc95faa14d3f38e5ae920d5a` |
| Full range exact-denominator approximation GLOBAL-1 | `../../rate/global/proof-v1.md` | `35d5d3e26de77e71dd666996d0e936c616abcce3a4f83ba2acb2164ea6ea9566` |

These hashes fix the claims being compared. They do not assert historical priority. Earlier attribution of the Collins and Nagatsu recurrence and normalization, the classical Laguerre identity, and the Bordenave and Zhu scalar factorial inequality remains in force.

## 2. Han and Niles-Weed's centered-matrix theorem

The primary source is [arXiv:2607.23836v1](https://arxiv.org/abs/2607.23836v1), submitted 26 July 2026. The 14-page PDF has a title-page date of 28 July 2026. The inspected theorem is Theorem 1.2, following equation (2), on PDF page 3. The [HTML](https://arxiv.org/html/2607.23836v1) and [PDF text](https://arxiv.org/pdf/2607.23836v1) agree on its normalization.

For a matrix $A$, their quantity is

\[
e_h(A)=\frac1{h!}\sum_{|S|=|T|=h}\operatorname{Perm}(A_{S,T}).
\]

If $A$ has zero row and column sums and $\|A\|_F=n$, their theorem gives

\[
|e_h(A)|\le B^h\binom nh,\qquad B=8e^2
\]

as an admissible universal constant. This general matrix inequality has a direct connection to the present diagonal moments.

### Direct specialization, with proof

Let $n\ge2$, let $J$ be the all-ones matrix and set $B_n=nI-J$. For $1\le h\le n$, use the mixed proof's normalization

\[
\mu_h(n,0)=\mathbb E_\sigma\prod_{i=1}^h(n\mathbf1_{\{\sigma(i)=i\}}-1),
\qquad \sigma\text{ uniform on }S_n.
\]

Then

\[
\boxed{e_h(B_n)=\binom nh^2\mu_h(n,0).}
\tag{P1}
\]

Indeed, fix a row set $S$ of size $h$. Summing $\operatorname{Perm}((B_n)_{S,T})$ over column sets $T$ sums the product over every injection from $S$ to $[n]$ exactly once. The restriction of a uniform permutation is uniform over these $(n)_h$ injections. Its product expectation equals $\mu_h(n,0)$ by simultaneous relabeling of rows and columns. Thus the fixed-row sum is $(n)_h\mu_h(n,0)$. Sum over the $\binom nh$ row sets and divide by $h!$. Since $(n)_h/h!=\binom nh$, this proves (P1).

Both row and column sums of $B_n$ vanish, and

\[
\|B_n\|_F^2=n(n-1)^2+n(n-1)=n^2(n-1).
\]

Applying the theorem to $B_n/\sqrt{n-1}$ and using homogeneity gives

\[
0\le\mu_h(n,0)
\le \frac{(8e^2)^h(n-1)^{h/2}}{\binom nh}.
\tag{P2}
\]

Nonnegativity follows independently from the positive coefficient identity in the mixed proof. Formula (P2) is therefore a valid prior bound for the same zero-depletion moments. For example, $\mu_2(n,0)=1/(n-1)$ follows directly by expanding its two factors, whereas (P2) gives $2(8e^2)^2/n$. This comparison identifies the specialization as coarse without comparing the two theorems on their different full domains.

For positive depletion $r$, the natural remaining matrix is $nI_{n-r}-J_{n-r}$, whose row and column sums are $r$. The zero-sum hypotheses do not apply to this matrix as written. This observation does not rule out an indirect deduction after a decomposition. The inspected theorem does not state the sharp maximum

\[
\frac{n^{-h}D_h(n,a-h)}{(n)_a}
\]

over the mixed proof's entire class with $b=0$. The merging argument across independent colors and the attainment statement must remain visible as parts of the contribution.

## 3. The earlier permutation-mixture paper

The inspected primary version is [arXiv:2408.09341v3](https://arxiv.org/abs/2408.09341v3), revised 16 September 2025. Its 61-page PDF has a title-page date of 17 September 2025. The first version was submitted 18 August 2024. The newer paper's reference [HN26] confirms the journal identity: *The Annals of Statistics* 54(3) (2026), 1594 to 1621. Journal theorem numbering was not checked.

In the inspected [preprint](https://arxiv.org/pdf/2408.09341v3), Theorem 4.3 is on pages 20 and 21, equation (29) and Lemma 5.3 are on page 23, and Lemma 5.5 is on page 25. These give centered-vector inequalities and bounds for homogeneous parts of a normalized permanent. They do not present the present mixed extremum or the diagonal parity limits.

### Direct permanent connection, with proof

Set $\mu_0(n,0)=1$. For $0\le t<1$, put

\[
M(t)=\frac{J+tB_n}{n}.
\]

This is doubly stochastic and positive semidefinite. Its eigenvalues are $1,t,\ldots,t$, because $J/n$ is the projection onto the constants and $B_n/n$ is its complementary projection. Expanding the permanent gives

\[
\frac{n^n}{n!}\operatorname{Perm}(M(t))
=\mathbb E_\sigma\prod_{i=1}^n(1+t(B_n)_{i,\sigma(i)})
=\sum_{h=0}^n\binom nh\mu_h(n,0)t^h.
\tag{P3}
\]

The last equality follows by choosing the $h$ factors contributing $t$ and using the same permutation symmetry as in (P1). Thus the degree-$h$ term $S_h$ in their equation (29) is exactly $\binom nh\mu_h(n,0)t^h$ for this family. Their Lemma 5.5 gives

\[
\mu_h(n,0)
\le 3\sqrt{h+1}\,
\frac{\binom{n+h-2}{h}}{\binom nh},
\tag{P4}
\]

because there are $\binom{n+h-2}{h}$ weak compositions of $h$ into $n-1$ parts. To justify the count, insert $n-2$ separators into a string of $h$ identical marks. The separator positions determine the composition. Apply the lemma at any $t>0$ and cancel $t^h$.

The older permanent framework therefore also contains the diagonal moments. It should not be dismissed as unrelated merely because its motivating problem concerns statistical mixtures. Bounds (P2) and (P4) are deductions made here from the inspected prior statements, not statements quoted from those papers.

## 4. Dunster 2001 and the negative-parameter range

The publisher verifies T. M. Dunster, *Uniform Asymptotic Expansions for the Reverse Generalized Bessel Polynomials, and Related Functions*, *SIAM Journal on Mathematical Analysis* 32(5) (2001), 987 to 1013, [DOI 10.1137/S0036141099359068](https://epubs.siam.org/doi/10.1137/S0036141099359068). The [author's publication list](https://tmdunster.sdsu.edu/) independently agrees.

The publisher abstract states uniform expansions subject to $a=O(d)$ as the degree $d$ grows, with the generalized Bessel parameter $a$ separated from $-d$ and $-2d$. The complete article body was not accessible. The PDF route redirected to the abstract and access page. Consequently, this note compares the announced scope, not an unread theorem.

The exact change of parameters comes from Kuijlaars and McLaughlin, [equation (1.12)](https://arxiv.org/html/math/0204248v1):

\[
y_k(z,a)=(-1)^k k!\left(\frac z2\right)^k
L_k^{(-2k-a+1)}(2/z).
\]

Setting $a=N-2k+2$ and $z=-2/N$ makes the Laguerre parameter $-N-1$ and the argument $-N$, exactly the present specialization. This is an algebraic substitution, valid for the polynomial identity. If $k=o(N)$, then $a/k=N/k-2+2/k\to\infty$, so the announced condition $a=O(k)$ fails. If $k/N\to\rho\in(0,1)$, then $a/k\to1/\rho-2$, a finite value different from $-1$ and $-2$. That interior parameter range overlaps the announced classical regime. At $k=N$, the ratio tends to $-1$, a boundary excluded by the stated separation condition.

This comparison does not rule out a limiting argument based on other classical expansions. It also does not establish that the present formula is historically new in every sublinear regime. The separate special-function review addresses that question more broadly.

## 5. Calibrated contribution language

The mixed moment estimate retains the number of consistent centered singletons and the amount of conditioning separately. It gives an attainable finite envelope over arbitrary permitted powers and independent permutation colors when there are no inconsistent centered singletons. Its positive polynomial is a classical Laguerre specialization. Related centered-matrix and permanent inequalities of Han and Niles-Weed yield bounds for the same diagonal moments, while the exact mixed maximum requires the additional monotonicity, merging and attainment arguments given here. On the diagonal, the parity-sensitive critical laws and their uniform corrections connect the cubic transition, the square-root scale and an exact-denominator approximation through all orders. The interior proportional-degree range overlaps classical negative-parameter Laguerre asymptotics. The claimed contribution there is the stated uniform connection and error control, not a new special-function parameter regime.

No exact duplicate of the attainable mixed envelope or the stated signed uniform correction was identified in the statements inspected for this pass. This is a bounded search outcome. It is not an assertion that no such result exists.

## 6. Access and version limits

- Both Han and Niles-Weed preprints were read in primary HTML and PDF text. No local PDF bytes or visual page rendering were inspected in this pass. All page locators above refer to the specified preprint PDFs, not the journal.
- The older paper's journal metadata is confirmed by the authors' later primary bibliography. Its publisher page returned an access challenge. The DOI resolver and Crossref endpoint did not provide usable metadata through this reader. The DOI is therefore omitted from this pass's minimal bibliography rather than treated as independently verified here.
- Dunster 2001 was inspected at the publisher abstract and metadata level. Its PDF route returned the abstract page. No statement about the uninspected contents is inferred from that limitation.
- The complementary review owns the full Kuijlaars and McLaughlin and Whittaker analysis. This note uses only the exact identity (1.12) and records the already verified finite-ratio overlap. The earlier Dai and Wong assessment remains publisher-abstract only.
- The integrator reports full preprint inspection of Dunster, Gil and Segura, arXiv:1705.01190v1, and publisher and author-page verification of *Advances in Computational Mathematics* 44(5) (2018), 1441 to 1474, DOI 10.1007/s10444-018-9589-5. Its journal body was subscription restricted and the public shared link returned a script challenge. Those are inherited access facts, not new inspection claims by this note.
- The integrator reports publisher verification of Diaz-Mendoza and Orive, *Journal of Mathematical Analysis and Applications* 379(1) (2011), 305 to 315, DOI 10.1016/j.jmaa.2010.12.053. Its recorded $\alpha/k\to-1$ zero-distribution scope and truncated-exponential endpoint identity do not justify claiming the endpoint as new.

Searches and source routes are recorded in `SEARCH_LOG-v1.md`. The bibliography is in `references-v1.bib`.
