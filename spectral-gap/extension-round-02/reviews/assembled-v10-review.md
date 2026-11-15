# Assembled revisions 9 and 10, final delta review

Date: November 14, 2026, America/Los_Angeles.

Decision: Accept the v8-to-v9 mathematical and editorial delta. Accept the v9-to-v10 source-attribution delta. Frozen v10 is accepted as the reviewed manuscript and guide within the proof and source scope stated below. No unresolved mathematical, integration or layout finding remains from this review.

This report distinguishes the two deltas. It does not certify universal historical priority or a complete graph eigenvalue theorem.

## Exact reviewed revisions

All 28 entries in each manifest match their frozen files.

| Artifact | SHA256 |
| --- | --- |
| Frozen v9 manifest | 7645f1e5af4c74929fdab620e274e2744ca1ce0c8e8c895cec192d0b4fc064ee |
| V9 main PDF, 41 pages | 399f20f489e6595ab44ec78d846054df740865ab5e355af572e27a6d681071e2 |
| V9 guide PDF, 8 pages | 2f3feb662d2aef4849ff4d1d78190f9b05576ce18a57098aac34d87606151448 |
| Frozen v10 manifest | 70d45e272ec4c32f79b7d630dea55ced37c7f95cb2e89b62c3719ed998737c4d |
| V10 main PDF, 41 pages | 7fc4f3d762123e906c1e35ab96141a3463a0e4e80ffa116f26970e8aec551a0f |
| V10 guide PDF, 8 pages | 8e839703f93bbe0260ed09249fe0121fbcaa15309adccac1475018a63506fb66 |
| Mixed source, identical in v9 and v10 | 062ebfa4e7536d1dd091dd09c7964a508259ac910b7992882bae0572842a110e |
| Asymptotics source, identical in v9 and v10 | 39c158b6622799cec3b55ea54e3ce2aeeecfdbaf3c83f22698b7d66fa0c03a0d |
| V9 discussion source | f370c3c1c7362603177d8a12ca624ddd31dfd6ba6a3f0bed0aab3af58349785f |
| V10 discussion source | b9066a654af41a0161ed10dc90ac84a6105c19aaddeac973d7975d37be589bcd |
| Guide source, identical in v9 and v10 | a469c6dafb7d12546cbf61ab966a5450d907f031ce26ca0fa58d4105451d6d64 |

The base v8 manifest is 4480fd2f51caf7cab2072a830520ffcb8f3c5fddea85e84f79958f0cde6c3d85. Its mathematical acceptance and three editorial findings are frozen in [the v8 review](assembled-v8-review.md), SHA256 739dca3b060eaced749ef2d5329d96f593c998458dd0450a9538e70911f824d1.

Prior exposure includes the base mixed proof and its integration draft, the original sublinear proof, the global extension, the one-conflict proof, and assembled reviews through v8. The MIX2 proof and compact candidate were independently reviewed and frozen before reading assembled v9. That review is [two-conflict-v1-review.md](two-conflict-v1-review.md), SHA256 b9361a2e466de16df63d89e2d455f95ad6dcb716d7ac3e03b5d20d34fb3a4295. The author's and integrator's MIX2 checkers were not used as evidence for that review.

No maintained or frozen manuscript file was edited.

## V8-to-v9 decision

### Exact two-conflict envelope

The independently accepted compact candidate, SHA256 cb4313258b9ac9e0e0dd8b458dc5a0a585678aba9349a3d9d27c792a7ad1e93f, is included byte-for-byte. Theorem 2.6 and its proof retain:

- The exact maximum for \(b=2\), over every permitted pattern, power assignment and collection of independent colors.
- The general \(2^{b-2}\) bound with no asserted sharpness for \(b>2\).
- Both forced-indicator cases, the mutually conflicting unforced case, and the compatible unforced case.
- The sign rewrite before merging colors in the mutually conflicting case.
- One omitted conflicting neighbor in the compatible case, including a neighbor shared by the two retained cells.
- The total-index bound \(a-1\), so the endpoint \(a=n\) stays inside every kernel domain.
- The affine treatment of all remaining factors and an explicit attaining pattern for every admissible \(n,a,h\).

The introduction, abstract, discussion and guide now agree that exact maxima are obtained for \(b=0,1,2\). They distinguish these statements from general bounds at larger \(b\). The guide gives the correct difference of two depleted kernels and explains the negative correlation of the retained pair.

The independent MIX2 record checks 20,204 original products, 63,916 selected supports and 84 attainment triples by exact rational arithmetic. These finite checks support the review but are not premises of the general proof.

### Resolution of the v8 findings

| Finding | Exact resolution in v9 and v10 |
| --- | --- |
| AV8-E1, shifted triple count | Main page 25 explicitly uses \(J-\epsilon\) and division by \(K\). Guide page 7 removes the compulsory odd triple, states that the shifted discrepancy stays bounded, and explains its suppression by \(K\). |
| AV8-E2, ambiguous rate in abstract | Main page 1 explicitly assigns the \(N^{-1/4}\) rate to the shorter quartically corrected hyperbolic approximation. |
| AV8-E3, almost empty contents page | The complete contents now fit on main page 1. The body begins on page 2. |

These findings remain part of the historical frozen v8 record. They are resolved in both successor revisions reviewed here. The corrected prose does not modify the SG-15 formulas or tail arguments.

### The larger-conflict counterexample

The stated example at \(n=a=b=8,h=0\) is valid. Use rows \(1,2,3,4\), giving row \(i\) its own two columns \(2i-1,2i\). Every cell is an inconsistent centered singleton.

For one row, the scaled two-cell product is
\[
(nM_{i,2i-1}-1)(nM_{i,2i}-1)
=1-n(M_{i,2i-1}+M_{i,2i}).
\]
Choosing \(j\) rows leaves \(2^j\) compatible match choices. The exact expansion is therefore
\[
n^8\mathbb EP
=\sum_{j=0}^4\binom4j(-2)^j\frac{8^j}{(8)_j}
=\frac{1121}{105}.
\]
For eight cells in one row, exactly one of the eight indicators equals one. The scaled centered product is always \(-7\), giving absolute value \(7\). Direct enumeration over all \(8!\) permutations independently confirms both values.

This refutes a general same-row extremizer. It does not identify the exact maximum for \(b=8\), and the manuscript does not claim to do so.

### Derangement-polynomial attribution

The publisher page and the actual journal PDF page 9 were inspected for Kim, Kim, Jang and Kwon, [A note on some identities of derangement polynomials](https://link.springer.com/article/10.1186/s13660-018-1636-8), Journal of Inequalities and Applications 2018, article 40. Equation (2.22) uses the exponential generating function
\[
(1-t)^{-r}e^{xt}
=\sum_{h\ge0}d_h^{(r)}(x)\frac{t^h}{h!},
\qquad r\in\mathbb N.
\]
The PDF SHA256 is b3a8705d4bd054703816bf7f057ebded92f137a05bb106e2462f82e77594c3ff.

For fixed admissible \(n,s,h\), indicator expansion gives
\[
\mathcal P_h(n,s)
=\sum_{j=0}^h\binom hj(-1)^{h-j}n^j
  \frac{(n-s-j)!}{(n-s-h)!}.
\]
If \(V\) has unit-scale Gamma shape \(r=n-s-h+1\), then
\[
\mathbb EV^{h-j}
=\frac{(n-s-j)!}{(n-s-h)!}.
\]
Consequently \(\mathcal P_h(n,s)=\mathbb E(n-V)^h\), and the published generating function yields
\[
\mathcal P_h(n,s)=(-1)^h d_h^{(n-s-h+1)}(-n).
\]

The shape is at least one throughout \(h+s\le n\), including full depletion. The order depends on the degree \(h\). The manuscript states this dependence and does not confuse the identity with equality of two generating functions at a fixed order. The exponential normalization and the sign are correct. An independent integer calculation confirms the identity in all 5,455 triples with \(1\le n\le30\), \(0\le h\le n\), \(0\le s\le n-h\).

The attribution concerns the polynomial family and this connection. It does not infer the full mixed optimization theorem from a polynomial definition.

## V9-to-v10 decision

The sole source-content change is the Collins and Nagatsu paragraph and display in discussion.tex. All 37 theorem, lemma, corollary, proof and example blocks are byte-identical between v9 and v10. The guide source is unchanged.

The actual published PDF of Collins and Nagatsu, [Weingarten calculus for centered random permutation matrices](https://doi.org/10.5802/alco.480), was inspected at printed page 478, PDF page 15. Remark 7.2 states exactly the centered product with powers \(2,2,1,1\) in four cells of one row and the value \(2n^{-5}-5n^{-6}\). The PDF SHA256 is c5b124655a495c03017b3866542ebd1f3289921cc4ed053244cc885cb8db017e.

The result can also be reconstructed directly. In the product scaled by \(n^6\), the two outcomes in columns one and two contribute \((n-1)^2\) each. The outcomes in columns three and four contribute \(-(n-1)\) each. The other \(n-4\) outcomes contribute one each. The uniform first-row mean is
\[
\frac{2(n-1)^2-2(n-1)+(n-4)}{n}=2n-5.
\]
This gives exactly the published value after dividing by \(n^6\). Direct permutation enumeration checks it again for \(n=4,5,6,7,8\).

The manuscript's classification \(a=4,h=0,b=2\) is correct. The first two cells are repeated centered factors and are not counted as centered singletons. The last two are inconsistent centered singletons. The added prose correctly distinguishes a known fixed-pattern evaluation from the maximum over all patterns, powers and independent colors.

No theorem or proof correction is needed.

## Preservation, numerical evidence and layout

All 35 theorem, lemma, corollary, proof and example blocks from v8 occur unchanged in v9. The two added blocks are the exact two-conflict theorem and its proof. All 37 remain unchanged in v10. The SG-15 appendix, the earlier square-root-rate theorem and its appendix are byte-identical to v8. The asymptotics section changes only the explanation resolving AV8-E1.

Both revisions have 144 distinct labels, no duplicate labels, and no unresolved internal references. The four TeX documents were independently rebuilt in isolated copies with three passes each. Each rebuilt PDF has extracted text identical to its frozen counterpart. The final logs contain no warnings, overfull boxes or underfull boxes.

Every v9 page was rendered and visually inspected through the six contact sheets. The new theorem pages 8 and 9, guide page 3, guide page 7, the corrected title/contents page, and the new discussion material received individual or enlarged inspection. All 49 v10 pages were also rendered and compared with v9. Only main pages 30, 31, 32 and 33 differ. Those pages were inspected. All eight guide-page rasters are identical between v9 and v10. No clipping, overlap or unreadable mathematical display was found.

The numerical data and all figure PNGs are unchanged from v8. The 60 global-error points were independently recomputed against frozen v10 using the exact integer \(Q_k\) recurrence and exact cancellation of the permutation denominator. The maximum discrepancy is \(2.3077702\times10^{-17}\). Independent bisection gives
\[
c_*=1.1654018731837499188618956314392033107904702911671\ldots,
\qquad
C_*=0.39549627009050769312029148337198010586163916963446\ldots.
\]
These match the figure data and stated rounded constants.

The portable build and algebra checker accepts a separate output directory so that reproduction need not alter frozen review evidence. Its successful second run in a temporary directory confirms that the saved evidence does not depend on the original review-output location.

## Accepted scope and remaining limits

Accepted scope includes the assembled exact mixed envelopes for \(b=0,1,2\), the stated general mixed bounds, the already reviewed diagonal threshold and approximation theorems, both sharp error-rate results, the guide's explanation, and the source additions inspected in this delta.

No exact maximum for prescribed \(b>2\) is accepted or asserted. No new graph eigenvalue theorem is asserted. The source audit verifies the cited equations and their actual mathematical specializations. It does not establish universal historical novelty. The earlier distinction between inspected DLMF formulas and an inaccessible original Olver journal body remains applicable and unchanged.

The final reading copy has no open finding from this review. The requested next action is to record the v9 and v10 delta acceptances against their exact manifests and use frozen v10 for the final archive.

