# Problem 21 readiness and remaining decisions

Prepared November 14, 2026 Pacific. The manuscript is being finalized for review. It has not been submitted, uploaded, published or sent to an author or editor.

## Exact answer to problem 21

The official target asks for an intuitive proof of Bordenave's Proposition 28, its use in the biregular spectral-gap argument, and the surrounding theory. Section 2 proves the matching-product estimate by preserving consistent centered singletons, conditioning on compatible prescribed matches and using the remaining row sum. It handles arbitrary multiplicities and independent permutation colors.

For a product with k factors, a distinct cells, h consistent centered singletons and b inconsistent centered singletons, the scalar consequence is

$$
|\mathbb E P|\le\sqrt e\,2^b n^{-a}
\left(\frac{\sqrt{a-1}}{\sqrt n-\sqrt{a-1}}\right)^h
\le\sqrt e\,2^b n^{-a}(3k/\sqrt n)^h
$$

when 2<=a<=k<=sqrt(n). The one-cell case is handled directly. Thus the requested proposition follows, with a stronger singleton factor. The exact mixed envelope additionally identifies the maximum when b is zero, one or two.

Section 8 maps a biregular matching to a uniform permutation of size L=n_L d_L=n_R d_R. The centering is 1/L. This is the input used in Brito, Dumitriu and Harris, preprint Lemma 7 and published Lemma 5.6. The section explains non-backtracking walks, trace moments, pattern counts, tangle remainders and the adjacency-eigenvalue bridge. It proves the probabilistic input and explains the remaining graph argument, without claiming a new graph spectral theorem.

## Mathematical and source status

The [ledger](../CLAIM_LEDGER.md) records SG-01 through SG-16 as proved, with their exact review scopes. These include the exact mixed envelope, cubic criterion, parity transition, sublinear correction hierarchy, explicit square-root error bound, sharp square-root error constant and a full-range approximation. The [assembled revision-6 review](reviews/assembled-v6-review.md) accepts their integration. The [revision-7 source review](reviews/assembled-v7-review.md) accepts the subsequent attribution and wording changes.

The b=1 extremum and full-range optimal error profile have separate accepted reviews. The b=2 extremum has both an integrator reconstruction and a separate independent acceptance, with distinct original-product checks. Frozen revision 10 integrates them in a 41-page manuscript and eight-page guide. It also repairs two explanatory sentences and the first-page contents layout found in the revision-8 review. The [final assembled review](reviews/assembled-v10-review.md) accepts the exact revision-10 manuscript and guide with no remaining mathematical, integration or layout finding. The archive's exact identity and clean-replay result are recorded separately in manuscript-round-01/checks/release-verification.json.
The full Bordenave journal check is complete. The [current priority assessment](PRIORITY_SYNTHESIS.md) credits substantial classical asymptotic overlap, the Han and Niles-Weed permanent bounds and Bordenave and Zhu's elementary factorial bound. Historical firstness of the diagonal formulas remains unverified. Some other journal bodies remain access limited, with exact inspection levels recorded.

## Before an actual submission

Later graph evidence: the supplied trajectory resolves batch-060 chronology. A separately reviewed replacement proof, SG-17, now repairs its critical cubic full-neighbourhood law. The [intake and repair record](../../../spectral-reconciliation-2026-11-14/remote-intake/README.md) is outside the frozen revision-10 package. Incorporating it into a publication requires a new assembly and an appropriately scoped source comparison. The existing moment package remains unchanged, and no broader graph or solver completion is implied.

Scope checkpoint after workspace reconciliation: readiness below applies to the accepted moment manuscript. It does not certify completion of the earlier K4 phase-sensitive lift and complex-Laplacian solver proposal. The [reconciliation record](../../../spectral-reconciliation-2026-11-14/README.md) identifies that unfinished program, the older graph results and unresolved source retrieval. Decide the intended submission scope against the full proposal and official wording before representing the whole spectral project as complete. The preserved revision-10 package predates this scope addendum and remains unchanged.

1. Supply the agreed author names, affiliations, acknowledgments and required declarations. Choose the destination and apply its format. No author or venue information is invented in this package.
2. Obtain subject-specialist assessment of the argument and narrowly framed novelty if journal submission is intended. Internal mathematical reviews are not external peer review. In particular, the access-limited sources should be checked directly if a priority claim depends on excluding them.
3. Refresh the literature comparison if submission is delayed substantially or a new relevant source appears.
4. Obtain the user's explicit instruction before any upload, publication, submission or external correspondence.

No additional unproved premise is identified in the accepted SG-01 through SG-16 theorem chain. Improving the graph eigenvalue theorem would require new circuit and tangle estimates and is a separate research problem. End-to-end formal verification is not claimed and is not a missing step of an ordinary written proof.
