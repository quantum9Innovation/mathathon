# SG-E3 independent review by saddle, revision 1

Date: November 14, 2026 Pacific

Task: SG-E3-REV

Reviewer: manuscript_referee

Recipient and integrator: root

## Decision and exact revision

**Accept the exact frozen SG-E3 revision 1 for its stated mathematical scope.** No unsupported inference or blocking domain error was found. The sharp envelope, its attainment for b=0, the scalar corollary, the fixed-count limit, the growing-count obstruction and the separate-dimension corollary are supported by their written proofs.

Reviewed source: extension-round-02/mixed/sharp-mixed-envelope-v1.md

Source SHA-256:

`878a139aee3caf6040debcc0f9b476e5fa0dd283c70c2a75a48ceaaea38d6b4d`

Reviewed manifest SHA-256:

`81736b099f7d6059a55ba12326c0c936004e3a6b095ce79a44b38fdcc98d3d99`

All five frozen output hashes and all three declared input hashes match. The review does not rely on a prior review or on the author's finite-check conclusions. The saddle attempt was already frozen before this packet was read.

## Reconstruction of the main proof

The coefficient normalization is correct. Multiplying the direct indicator expansion for the depleted moment by (n-s)_j/j! leaves the coefficient of z^j in (1-z)^(n-s) exp(nz/(1-z)). Its logarithmic coefficient at degree ell is ((ell-1)n+s)/ell. The labeled partition weight is consequently ((ell-1)n+s)(ell-1)!, including singleton weight s. This proves positivity within the moment domain and justifies the formal polynomial outside that domain without interpreting it as a moment.

Both monotonicity claims use positive denominators on their full stated domains. The depleted factorial (n-s)_j decreases with s. The scalar part of K has successive ratio n/(n-j-s), whose denominator is at least one whenever the next index is permitted. This includes the final step into j+s=n.

The color merge needs two distinct comparisons, and both are valid. Union of labeled partitions injects the product of the two partition sums into the merged sum, after increasing each block's depletion parameter to s_1+s_2. Separately, (n)_u(n)_v is at least (n)_(u+v). These comparisons have the correct directions for the quotient defining K. Every iterated merge is admissible because its total index is bounded by h+|S|, which is at most a and at most n.

The selected-term identity (4.3) has the correct powers of n. In one color, the exact term is the compatible-selection probability 1/(n)_s times n^(-h) times the depleted moment. Since K=F_n(s) mu_h, this equals n^(-h-s) K. Independence multiplies these identities across colors. Consistency of T guarantees that none of its rows or columns was exposed by the selected raw set.

For repeated cells, the affine coefficient d is nonnegative when n is at least two. The even and odd formulas for d+n|c| are correct, including n=2. Every factor outside T has weight at most one except an inconsistent centered singleton, whose weight is exactly two. After the kernel bound is substituted, summing the absolute affine coefficients gives exactly n^(-a) times the product of those weights. Incompatible selections may be included in that upper sum because its summands are nonnegative.

Attainment has no hidden loss from an earlier inequality. With one compatible color, h centered factors and a-h raw factors, the expansion contains only the full raw selection. Its exact conditional expectation is n^(-h) D_h(n,a-h)/(n)_a. It is nonnegative and equals the envelope for b=0. This proves an attained maximum over the full permitted class, even though many other configurations give smaller values.

## Endpoint audit

| Endpoint | Verified behavior |
| --- | --- |
| h=0 | D_0=mu_0=1. The b=0 envelope is 1/(n)_a and is attained by compatible raw cells. |
| h=1 | D_1(n,a-1)=a-1. The scalar factor is the exact depleted first moment (a-1)/(n-a+1). |
| a=h=1 | The centered expectation, D_1(n,0), and Gamma are all zero. No division by Gamma is used in this case. |
| h=a | Depletion is zero. The compatible all-centered product attains the envelope. Gamma equals beta for a at least two. |
| a=n, h=0 | Full depletion uses only the empty moment mu_0. The denominator (n)_n=n! is positive. |
| a=n, h>0 | The remaining dimension is h, so the top depleted moment is admissible and its factorial denominator is h!, not zero. |

The first-moment seed in Section 5 is only used after imposing h at least one and s+h at most n. Thus n-s is positive there. Section 2 separately gives the empty-product convention at full depletion.

## Scalar and asymptotic conclusions

The scalar induction is valid. Its constant denominator d is no larger than each recurrence denominator, while A and v dominate the corresponding numerator coefficients. The defining quadratic gives gamma at least A/d and hence at least the first-moment seed. The only zero-root case is s=0, h=1, and is handled before division. The root comparison with beta is strict for 1 at most h<a and is equality at h=a.

The fixed-h limit follows from a finite partition sum. Only singleton and pair blocks survive after scaling, including when rho=0 and the limiting odd polynomial vanishes. The later equivalences use rho=1, where the limiting polynomial is strictly positive. The comparison of full bounds is legitimate because their factorial and other prefactors are identical.

The growing-count obstruction is also valid. Pair partitions give the stated lower bound, and concavity of log on each unit interval gives the double-factorial estimate, including the integrable endpoint at zero. A fixed universal prefactor has a-th root tending to one. The separate a=2 argument correctly rules out a universal constant reduction of beta when the exact remaining prefactor is retained. Neither argument contradicts improvement at h<a.

For separate color dimensions, independence and the local theorem suffice. Attaining choices can be made simultaneously. No bound on the total support across colors is needed for that corollary.

## Independent finite corroboration

The review's separate checker uses an exponential-coefficient recurrence and direct evaluation of original factors over permutations. Exact integer and rational arithmetic passed:

- 161 depleted moments, including full depletion
- 11,622 color merges
- 559 moment monotonicity and 559 kernel monotonicity comparisons
- 6,357 affine-weight checks, including powers through 40
- 75 directly enumerated attaining products
- 960 sampled original mixed products with one to three colors

The exact ranges and limitations are recorded in mixed-by-saddle-check-results-v1.json. These checks corroborate the reconstructed general proofs. They do not establish claims outside their finite ranges and are not substitutes for those proofs. The author's checker was inspected but was not run, because it writes into the frozen author packet.

## Handoff and scope

Proposed status: SG-E3-A, SG-E3-B and SG-E3-C reviewed and accepted at the exact source hash above. No repair is requested and no finding remains open.

Acceptance does not assert sharpness of the factor 2^b or of the envelope for fixed b>0. It does not establish historical priority, alter the graph enumeration, or certify a new spectral theorem. The generating identity is independently derived within the proof, so its citation is not an unproved mathematical dependency.

No author proof, frozen manuscript or canonical ledger was edited. The next action is integration by root, with the accepted scope preserved.
