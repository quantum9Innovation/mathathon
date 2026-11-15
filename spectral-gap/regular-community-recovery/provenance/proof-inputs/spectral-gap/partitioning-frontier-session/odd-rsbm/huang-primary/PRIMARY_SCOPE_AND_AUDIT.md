# Huang input, exact scope, and the needed extension

Date: 2026-11-15. All writes for this task are in this directory. The frozen even-block note was read without modification.

## Primary source finding

[Jiaoyang Huang, *Invertibility of adjacency matrices for random d-regular graphs*, arXiv:1807.06465v2](https://arxiv.org/abs/1807.06465) defines the undirected configuration model whenever dN is even, so it includes odd N when d is even. Theorem 1.1, equation (1.2), gives

\[
 \sum_{v\ne0}\Pr(Cv=0)=1+\mathbf1_{p=2}+o(1),
\]

under gcd(p,d)=1 and p much smaller than N raised to min{1/8,(d-2)/(5d-6)}. Its consequences are unshifted singularity bounds. Proposition 2.2 and Section 4 enumerate and estimate the zero-target event. These are not a stated all-target atom-mixing theorem and do not directly imply estimates for C-delta I or Cx=delta x+b.

The author’s [publication list](https://jiaoyang.github.io/publications.html) records publication in Duke Mathematical Journal 170(18), 3977–4032 (2021). The actual version audited here is the cited preprint. The publisher full text was not accessible through the attempted DOI route; no claim that every journal revision was inspected is made.

[Mészáros, arXiv:1806.03736v4](https://arxiv.org/abs/1806.03736) Theorem 1.6 is the required sum of maximum-atom errors, but the undirected model is a union of perfect matchings on an even vertex set. [Nguyen–Wood, arXiv:1806.10068v2](https://arxiv.org/abs/1806.10068) uses that mixing model and its even-size contiguity transfer. Neither cited statement supplies the missing odd-size prescribed-output theorem.

Inspection coverage: Huang pp. 1–8, Section 4.1 pp. 20–27, Proposition 4.3 and its rate-function argument pp. 28–30, and theorem/proposition search through the full extracted source; Mészáros model and Theorems 1.5–1.6, Section 7 theorem dependencies; Nguyen–Wood definitions and Sections 3–4. This is not a claim to have independently verified every proof in these papers.

Source PDF hashes:

| File | SHA256 |
|---|---|
| huang2018.pdf | b910005db135e52160eed299e0af742a1fa5e1cc1f06d061f45c4a916f32323a |
| meszaros2020.pdf | d65525afbe7e2a0f614feceb6fad833c518184a22ec1acedf94336f0c1c1cfbf |
| nguyenwood2018.pdf | 4ef6d77fe737ce59fe133743e7a1bedc1305c460e42e4640cc39b9d16607f0e2 |

## Directly proved extension in this directory

`configuration-arbitrary-target-tails.tex/pdf` proves:

1. Exact prescribed-output enumeration for all q,r, including loops counted twice.
2. A row generating-function inequality uniform over the output target, including its equality cases.
3. The uniform Taylor coefficient -(d-1)p/(2d) at the uniform probability vector.
4. The exact entropy normalization for fixed input and for summed input profiles.
5. An N^{-A} bound for the summed maximum atoms outside a shrinking central type window, after nearconstants are excluded.

The proof only assumes dN even and keeps d,p fixed. It is a direct adaptation proved here, not a theorem quoted from Huang. Historical priority of this extension has not been established. This note does not claim the complete strong mixing theorem or the RSBM conclusion by itself.

## Independent actual-source checks of the companion ingredients

The nearconstant source inspected in full is
`../parity-reduction/nearconstant-configuration-atoms.tex`, SHA256
`27e8488717aab0875dcfa1bfeca6f8d63b3cd3254b34c00988ff024c09828632`.
Its adaptive binary-word proof passes this review. In particular, the conditional constrained-exposure bound remains valid after arbitrary past exposures; variable stopping only restricts the word event; and 2c-dk=J+R-F>=0 supplies at least dk/2 constrained steps. The geometric ratio gives the stated N^{1-d/2} summed bound. The loop-based lower example is correctly limited to the unconditioned model.

The central source inspected in full is
`../meszaros-extension/balanced-all-target-configuration.tex`, SHA256
`9a1a1d6254cd26829fb8a12e2f4a7cc7b22b19d0657cf73c077b86b13eabf557`.
This review reconstructed its proof and found no substantive gap. Checks included:

- The W(M), B(M), and total-pairing factors agree with exact stub enumeration.
- For d>=3, every pair of tuple positions is independent uniform under any prescribed sum. The common covariance is correct.
- The conditional row difference lattice has index p after deleting coordinate zero. Comparing any two positions gives every phase increment and excludes additional maximal characters.
- Real tilting converts the moderate-deviation calculation into a relative local limit theorem; the exponent remainder is O(log^3(n)/sqrt(n)), uniformly over target arrays.
- The far-character bound is uniform because the finite family has a common maximal-character set and tilted support weights remain bounded below.
- The noncentral pairing-type contribution is o(p^{-n}), rather than merely o(1).
- The matrices 2(e_j-e_0)(e_j-e_0)^T preserve row sums and even diagonal and span all allowed output-congruence differences because p is odd.
- The smooth factorial ratio and bounded-shift comparison equidistribute the p^{p-1} feasible congruence classes.
- The resulting normalization is p^{-n+p} times p^{-(p-1)}, giving p^{-n+1}.

The condition p odd is essential to this congruence-basis argument. No step inspected needs p coprime to d. This is a mathematical source review, not a formal proof or independent novelty certification. Hashes bind these checks to the exact supplied versions.
