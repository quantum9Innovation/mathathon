# Assembled manuscript v6 mathematical audit

Date: November 14, 2026 Pacific

Reviewer: manuscript_referee

Recipient and integrator: root

## Decision

**Accept the mathematical arguments and stated approximation scopes of exact frozen revision 6.** No blocking proof, normalization, parity or domain error was found. The seven-page guide accurately describes the proved results. Two nonblocking wording clarifications are recorded below for the planned prose revision.

This is an audit of the assembled document, including the newly composed asymptotics section, the first signed correction and Appendix A. Prior involvement includes the original sublinear proof, the mixed-section draft, and the separate global review. That exposure is declared rather than treated as independent confirmation. The assembled statements and their dependencies were reconstructed again here.

Historical priority and the new literature-comparison prose remain outside this acceptance. They are subject to the ongoing primary-source pass. None of those comparisons is a premise of the mathematical arguments accepted here.

## Exact artifacts

Reviewed directory: manuscript-round-01/frozen-manuscript-v6

Manifest SHA-256:

`40999c65a266ec572b41e23824c9b2550c8e1e211b43180711c087f01d604165`

All 24 manifest entries were independently recomputed and match. Complete source hashes are in assembled-v6-evidence.json.

| Artifact | SHA-256 | Pages |
| --- | --- | --- |
| Main PDF | `4c508839fd86469fd7b258b4963dd4eaf9fa40c5bb0d231c73d39a4638369982` | 31 |
| Guide PDF | `85acabae490f559cfdd3ae9e189bccad1c5a7a8de895c8bafd76837e0903c920` | 7 |
| Asymptotics source | `48764f13c723a0caebe4f07545c4e81cd43182e6b46db57d5fd0fa79d977d6b5` | |
| Rates source | `a36939676c8b4c2aab572ea90c2055ba4cbad428593c52d1a1c496574cce5228` | |
| Appendix A source | `ba8e0ccfd926b3036f7b4542c426f203452d445e57a4b905ed9fc8a6f60a64f9` | |
| Mixed source | `791f8d24898aaef6c9056ea3bb13efefa46f49b45b1b3171507549cd94466e2a` | |
| Guide source | `fe8072c66c1504f3ba517d853175bf2cb347492c6ed3a5647d5e81206cfa8aaf` | |

The threshold, critical-limit and conditioning sources are byte-identical to accepted v5. The previous extension proof changes only its forward-looking prose. The mixed source is byte-identical to its frozen integration candidate. Its assembled references and surrounding scope were checked here.

## Proof scope and reconstruction

| Assembled result | Scope accepted |
| --- | --- |
| Theorem 2.1 and scalar corollaries | Exact attained envelope for b=0, valid upper bound with 2^b for general b, arbitrary multiplicities, compatible merging across colors, Gamma refinement, beta consequences and optimal universal square-root-range prefactor |
| Theorem 6.1 and Corollary 6.2 | Uniform full exponent on every sublinear upper range, exact necessity and boundedness criteria for each fixed truncation, and the boundary constants |
| Lemma 6.3 and Theorem 6.4 | Uniform coefficient bound through x=1 and a relative approximation throughout 2 at most k at most N, with the denominator retained exactly |
| Theorem 7.1 and Appendix A | Finite explicit rate for every C>0 under its displayed size condition, including fixed orders and small odd lambda |
| Theorem 7.2 | Uniform signed first correction down to the smallest orders and the sharp asymptotic supremum constant for every fixed C>0 |

The mixed proof preserves the exact factor n^(-h-|S|) in the selected-term identity. Its color merge combines positive partition weights with the correct falling-factorial inequality. The merging index never exceeds a, which is at most n. The affine factors have the required nonnegative indicator coefficient and total weights at most one, except for the retained factor two from an inconsistent centered singleton. The compatible one-color family attains the final bound for b=0. Full depletion uses only the empty moment, and the Gamma=0 case is handled before division. The scalar estimates in the graph section now correctly cite Corollary 2.5.

For the enlarged saddle estimate, r=x/(1+x) is at most one half. The derivative sums therefore have constants independent of N and K. Pair weights give the central Gaussian damping and the remaining-angle bound. Triple weights suppress the other peak by exp(-lambda/8). The local real-part and cosine estimates integrate to O(K^(-3/2)), giving relative error O(1/K). The lemma explicitly permits odd K, which is needed for its direct top-order coefficient calculation.

The normalization after the saddle estimate keeps the odd factor (1+x)/lambda. The logarithmic sublinear formula has the correct parity term of order sqrt(k/N). The sublinear theorem patches the large-lambda range to the already proved square-root theorem. Positive coefficients of G then prove necessity, boundedness and the successive thresholds. The coefficient 2/15 and the next coefficient 1/12 have the correct normalization.

The global formula keeps D_k exactly. It cancels in the relative quotient, so its large value near k=N does not amplify the saddle error. The lower-order patch retains the different quadratic cancellations for the two parities and the constants 19/30 and 5/6. The endpoint statement a_N=(2N!)^(-1)(1+O(1/N)) follows from the coefficient lemma with K=N and offset zero, without imposing evenness on N.

## Appendix A and the sharp first correction

The assembled appendix correctly retains parity conditioning of the triple count. At odd orders, shifting J to T=J-1 removes the compulsory triple. Its availability factor and its normalization agree with the earlier partition identity, including when lambda tends to zero.

I checked the moment table, the five-term second-moment estimate, the cubic availability remainder and the rounding into the displayed polynomial bound. The coefficients 67 and 245 dominate the stated unrounded coefficients. The aggregate tail includes every block size at least five, with the extra odd factor preserving the small-lambda normalization. Restoring the denominator gives the two displayed parity cancellations.

The extension of the finite estimate from C at least one to every C>0 is valid. The proof uses N at least 16C^2 only to ensure k at most N/4 and the other displayed scale bounds. No subsequent comparison requires C at least one. The explicit A_1(C) tends to zero with C, which is the key additional fact needed for the assembled first-correction theorem.

On each restricted interval d sqrt(N) at most k at most C sqrt(N), the logarithmic saddle error is uniformly O(N^(-1/2)). Expanding G and the parity factor gives the stated function psi. Exponentiating preserves that remainder at the required scale. Below d sqrt(N), the finite estimate gives limiting scaled error at most A_1(d), while psi is uniformly small. Sending d to zero closes the argument without assuming that every order has large lambda.

The odd function psi_1 is positive and increasing and dominates the absolute value of psi_0. The largest odd integer below C sqrt(N) supplies the matching lower bound for the supremum. Thus the sharp constant and the two signed values -11/30 and 19/30 are justified.

The proof dependencies are acyclic. The global theorem uses the finite rate, whose appendix proof uses positive partitions. The first-correction theorem uses the saddle expansion and that finite rate. It is not needed to prove either of its premises.

## Guide and rendered artifacts

The guide correctly restricts attainment to b=0 and explicitly excludes an optimality assertion for prescribed b>0. Its singleton example, fixed-h gain, growing-h obstruction, correction hierarchy and signed limits match the main statements. Its window table is expressly limited to the sublinear range. The guide retains the original-centering and full-depletion qualifications and separates the probability estimate from the graph enumeration.

The reading route matches the assembled section numbers. No reference label is missing or duplicated. There are 111 labels and 135 reference uses in the manuscript sources.

Fresh builds of both frozen sources produce exactly the same extracted text as the supplied PDFs. Final build logs report no warnings or overfull boxes. All 38 supplied pages were inspected in contact sheets, with individual-page inspection of the global theorem, sharp-rate proof, appendix moment table and guide hierarchy page. No clipping, overlap or unreadable mathematical content was found. The last manuscript page contains the final three references and substantial whitespace, an editorial pagination choice rather than a correctness defect.

All 240 points in the new figure's data file were independently recomputed to within 1e-12 using 80-digit arithmetic. Additional evaluations on 12 square-root ranges corroborate the signed correction and sharp-constant formula. These are finite checks, not proofs of the limits. Their exact scope is recorded in assembled-v6-check-results.json.

## Nonblocking precision notes

- AV6-E1: introduction.tex line 48 and discussion.tex line 7 describe strict Gamma improvement using h<a. Gamma is defined for h at least one. Writing 1 at most h<a makes the scope explicit and avoids suggesting an improvement of the empty singleton factor at h=0. The formal lemma and corollary already have the correct domain.
- AV6-E2: guide/reading-guide.tex line 216 calls the constant the exact worst-case constant. Adding the word asymptotic would make clear that it describes the scaled limiting supremum, not a finite-N exact bound. The surrounding limit and the main theorem already give the correct meaning.

Neither note changes a theorem or its proof. They can be handled with the forthcoming priority and prose revision.

## Handoff

Proposed status: frozen v6 mathematically accepted within the scopes above. No blocking finding remains. The next priority revision should receive a delta check of its source comparisons, claims of contribution, and any related abstract or guide wording. Any mathematical change beyond this frozen revision would make the corresponding acceptance stale.

This review does not certify historical novelty, sharpness of 2^b, optimality of the global approximation's rate, or a complete spectral graph theorem. No frozen or maintained manuscript file was edited.
