# Problem 21: submission-readiness note

Prepared November 14, 2026 Pacific. The package is prepared for the user's review and has not been submitted or published. Author details are deliberately left blank.

## How the manuscript answers problem 21

The requested bottleneck is an intuitive proof of Bordenave's Proposition 28 and an explanation of its use in the biregular spectral-gap argument. Manuscript Section 2 proves the mixed permutation-product estimate by retaining isolated centered factors, conditioning on a compatible prescribed matching, and using the remaining row sum before expanding the other factors. It handles repeated cells and independent permutation colors.

Section 6 identifies the uniform permutation of left and right half-edges used in Brito, Dumitriu and Harris, published Lemma 5.6, which is Lemma 7 in the preprint. It explains non-backtracking walks, norm moments, pattern counting, tangle remainders and the bridge to adjacency eigenvalues. The five-page guide provides the same mechanism through worked examples. The paper proves the probabilistic bottleneck and explains the surrounding theory. It does not claim to replace every part of the graph proof.

## Known ingredients and quantitative contributions

| Result | Prior work | Present contribution |
| --- | --- | --- |
| Mixed centered products | Bordenave's original estimate. The raw factorial inequality yielding sqrt(e) is also explicit in Bordenave and Zhu, equation (2.3) | A direct proof with singleton factor beta=sqrt(a-1)/(sqrt(n)-sqrt(a-1)), exact correction F_n(a-h), arbitrary multiplicities and colors, and optimality of the universal prefactor for this full class |
| Diagonal leading terms | Collins and Nagatsu's exact formula, recurrence, normalized parity recurrences and sufficient cubic range | Necessity of k^3/N tending to zero, bounded-comparability equivalence, and an optimal global lower-bound constant |
| Cubic transition | The published scale question is in Collins and Nagatsu, Remark 3.4 | Explicit even cosh and odd sinhc limits with a uniform finite critical-scale error |
| Larger relative range | Classical Kummer and Laguerre identities | Relative hyperbolic accuracy for k=o(sqrt N), finite bounds, and the exp(d/4) correction at k^2/N tending to d |
| Square-root range | Same classical identities | Uniform relative accuracy after including exp(k^2/(4N)) for bounded k/sqrt N. No explicit rate or assertion for unbounded k/sqrt N |

The manuscript makes no first-discovery claim for its standard identities, elementary raw factorial estimate or conditioning counterexamples. The [updated priority audit](PRIORITY_AUDIT_V2.md) found no exact duplicate of the refined statements within its inspected sources. This remains a bounded finding.

## Checks completed in this pass

- The complete published Bordenave article was retrieved. Proposition 28 and equation (62) have been checked at printed pages 1426 and 1428. Both conditional counterexamples apply to the published formula. Proposition 28 itself remains valid under the replacement proof.
- The earlier positive-parameter Laguerre source check was extended to its theorem text. A closer negative-parameter source was checked at its publisher's announced regime. Access limits are recorded rather than inferred away.
- Recent citation leads were inspected, including the prior raw-factorial estimate in Bordenave and Zhu. That overlap is now cited in the proof and contribution discussion.
- The abstract's wider-range referent now explicitly identifies the hyperbolic approximation. The new source citations do not change the established theorem statements.
- The revised PDFs and manuscript sources are frozen as revision 5. Exact review scope, compilation, visual checks and portable verification are recorded in [the verification record](../VERIFICATION.md). The archive's current integrity receipt is written separately as `checks/release-verification.json`. It is not embedded in the archive whose hash it records.

## What remains before an actual submission

1. Supply the agreed author names, affiliations, acknowledgments and any required declarations. Choose the destination and apply its final formatting and submission requirements.
2. Have a subject specialist assess the mathematical argument and novelty positioning if journal submission is intended. The recorded independent reviews are internal mathematical checks, not external peer review. In particular, the full Dai and Wong article was not available in this pass, and citation indexes were incomplete.
3. Refresh the short priority search if submission occurs substantially later or new relevant work is identified. Current wording already avoids a universal historical-priority claim.
4. Obtain the user's explicit instruction before uploading, submitting, contacting authors or editors, or publishing a preprint.

No additional unproved premise is currently identified in the stated theorem chain. An explicit square-root error rate, an extension beyond bounded square-root scales, and improved graph eigenvalue bounds would be further results, not prerequisites for these claims. Formalization is not claimed and is not presented as a missing conventional proof step.
