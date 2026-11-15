# Contribution and scope for problem 21

Latest graph result: [SG-29 and SG-30](structural-defects-round-01/README.md) establish a common attachment transition and the finer retuned cubic law. SG-29 allows fixed vector-polynomial ports with one simple local resonant channel and nonzero stationary coupling. Explicit local boundary data determine collective strength, pair strength and graph-space mass. The collective criterion m cubed/n tending to zero is necessary and sufficient throughout 1<=m=o(n). Critical lattice laws and dilute postcritical estimates extend across the class, including different simple unweighted motifs. SG-30 resolves the earlier retuned negative crossing at physical scale m/n. Eliminating complementary modes changes the apparent large-jump collective fluctuation into a bounded-jump law, and the leading signed pair coupling vanishes. Both results have separate exact-revision reviews.

The [priority audit and final scope](structural-defects-round-01/priority/FINAL_SCOPE-v1.md) credit established decoration, elimination, non-backtracking correspondence, growing-rank deformation and sparse localization results. No inspected theorem directly supplies this exact combination. Historical firstness and resolution of a named published open problem remain unverified. The conceptual contribution candidate is a common local-to-global resonance mechanism, not a claim to unify unrelated fields. Fifty-seven current-round finite declarations and 16 reused declarations pass a fresh source replay. Full probability and analytic transfer remain paper proofs. The cubic fine constants are not asserted for every attachment in SG-29.

The preceding [SG-27 and SG-28](critical-subspaces-round-01/README.md) identify the actual critical graph subspaces and resolve exact collective-pair resonance. Repeated lattice levels are handled as invariant subspaces, with explicit physical mass operators and concentration near pair endpoints. Positive avoided crossing occurs at physical scale n^(-1/2). Negative cancellation exposes a smaller logarithmic splitting. The then-open finite deterministic retuning is now resolved by SG-30, while finer bases inside repeated pair groups remain open. Twenty-four finite formal declarations support that prior round's algebra. Its frozen files remain unchanged.

The preceding [SG-25 and SG-26](critical-law-round-01/README.md) determine the entire critical H=0 defect law away from zero. A marked-pair Poisson theorem and a uniform spectral reduction produce collective levels and linked positive and negative pair levels. The integer-distance phase is retained in the eigenvalues. Distinct phases yield distinct top laws, and no full-sequence weak limit exists over all admissible sizes. The work connects geometric extremes to spectral resonances in this attachment model. Classical Poisson approximation, lattice distance laws, Poisson spectral-edge limits and max-semistable distributions remain credited prior methods. The [priority comparison](critical-law-round-01/priority/FINAL_SCOPE-v1.md) does not establish historical firstness or a universal law across models. Thirty finite formal declarations support the matrix steps, not the full random-graph theorem.

The preceding [SG-22 through SG-24](close-pair-transition-round-01/root/transition-synthesis-v1.md) prove the sharp collective criterion m=o(n^(1/3)), remove the logarithm through two distinct probability arguments, and identify the top displacement scale m^2/n for n^(1/3)<<m<<sqrt(n). Close pairs force actual eigenvalue deviations at criticality. The result extends across fixed degrees with the stated critical weights and bounded weak interactions. It is a structural transition theorem in this model, with historical priority still unverified and the full probability argument not formalized. The earlier growth range below remains part of the preserved previous-round statement.

November 15 graph continuation: [SG-19 through SG-21](growing-defects-round-01/README.md) add a quantitative growing-mark resolvent estimate, a reviewed collective-resonance theorem and eigenvector mass laws. The original cubic target is proved for m^3 log^2(n)/n tending to zero. A weighted fixed-degree extension handles arbitrary bounded weak interactions through one explicit effective matrix. Key finite matrix identities are checked in Lean, while the random-graph theorem remains a paper proof. Priority is qualified by comparison with existing growing-rank deformation theory. These are separate graph results and do not modify the frozen moment manuscript.

The [workspace-wide scope audit](../../spectral-reconciliation-2026-11-14/SCOPE_AUDIT.md) distinguishes the narrow problem-21 bottleneck addressed here from the earlier proposed graph-to-solver program. This manuscript does not establish the proposed phase-sensitive K4 lift bound, old/new-sector estimate or iterative-solver consequence. Historical finite-defect results and their errata require their own renewed audit. The separate older directed-regular-graph program is also outside this manuscript.

The manuscript proves the requested mixed-product estimate, explains its use in the biregular spectral argument, and supplies further finite extremal and uniform asymptotic results. The [claim ledger](CLAIM_LEDGER.md) identifies the exact proof revisions and separate reviews. The [current priority assessment](extension-round-02/PRIORITY_SYNTHESIS.md) separates established prior work from the contribution candidates.

## The direct answer

Separate graph continuation: the recovered remote campaign had later completed two clustered families. Fresh intake found a gap in the critical cubic full-neighbourhood proof. The [replacement argument and review](../../spectral-reconciliation-2026-11-14/remote-intake/README.md), now SG-17, repair it through a fixed-root resolvent estimate and prove the two square-root splitting constants. This is a reviewed graph-proof repair outside the frozen moment manuscript. It carries no historical-firstness claim and does not establish the K4 phase-sensitive solver target.

Problem 21 asks for an intuitive proof of Bordenave's Proposition 28 and an explanation of its role in the surrounding spectral-gap theory. The proof preserves isolated centered singletons, conditions only on compatible prescribed matches, and uses the remaining row sum before expanding the other factors. It allows arbitrary powers and independent permutation colors.

For a product with a distinct cells, h isolated centered singletons and b conflicting centered singletons, it gives

$$
|\mathbb E P|\le\sqrt e\,2^b n^{-a}
\left(\frac{\sqrt{a-1}}{\sqrt n-\sqrt{a-1}}\right)^h
\qquad(2\le a\le\sqrt n).
$$

If the original product has k factors, then a<=k and the singleton factor is at most 3k/sqrt(n) in the requested range. The one-cell case is treated directly. Thus the estimate implies Proposition 28 with a stronger singleton factor.

Section 8 identifies the biregular half-edge matching with a uniform permutation of size L=n_L d_L=n_R d_R, centered at 1/L. This is the input in Brito, Dumitriu and Harris, preprint Lemma 7 and published Lemma 5.6. The manuscript explains non-backtracking walks, norm moments, pattern counts, tangles and the adjacency-eigenvalue bridge. It proves the probability estimate and explains the other steps. It does not assert a new graph eigenvalue theorem.

The complete Bordenave journal article was checked. Two explicit examples refute an intermediate conditioning assertion in published equation (62), printed page 1428. They do not refute Proposition 28 or its spectral conclusion. The replacement proof avoids that assertion. See the [journal comparison](manuscript-round-01/presubmission-01/BORDENAVE_JOURNAL_CHECK.md) and its [independent review](manuscript-round-01/presubmission-01/INDEPENDENT_SOURCE_REVIEW.md). Discovery priority for this defect is not claimed.

## Exact finite extrema

Let P_h(n,r) be the positive polynomial whose labeled partition block of size j has weight ((j-1)n+r)(j-1)!. The complete mixed envelope is

$$
|\mathbb E P|\le 2^b\frac{n^{-h}P_h(n,a-h)}{(n)_a},
\qquad 2\le a\le n.
$$

At b=0 this is the exact maximum at fixed n,a,h, attained by h centered cells and a-h raw cells in distinct rows and columns of one permutation. Arbitrary powers and additional independent colors cannot increase it. The proof uses positive depletion weights, color merging and affine indicator bounds.

For b>=1 the stronger bound is

$$
|\mathbb E P|\le 2^{b-1}
\frac{n^{-h-1}P_h(n,a-h-1)}{(n)_{a-1}}.
$$

At b=1 it is again an attained exact maximum. One raw match forces the single conflicting centered indicator to zero. For b=2 the exact maximum is

$$
\frac{2n^{-h-1}P_h(n,a-h-1)}{(n)_{a-1}}
-\frac{n^{-h-2}P_h(n,a-h-2)}{(n)_{a-2}}.
$$

Two centered cells sharing one row attain it when all remaining cells are compatible with both. Multiplying this expression by 2^(b-2) gives a bound for b>=2. Exactness is not asserted beyond b=2, and an eight-cell counterexample shows that a single-row extremizer does not persist in general. Collins and Nagatsu already evaluate a particular repeated-power pattern in this b=2 class in published Remark 7.2. The maximum over all admissible supports, powers and colors is the additional claim here. These finite extremal conclusions are the clearest distinct contribution candidates, with historical priority still subject to the recorded search limitations.

The scalar factorial estimate by sqrt(e) is already explicit in Bordenave and Zhu, Lemma 2.1, equation (2.3). The manuscript credits it. The best universal prefactor for the full arbitrary mixed class is sqrt(e), but first discovery of the elementary factorial inequality is not claimed.

## Uniform diagonal results

For the centered product of k distinct diagonal cells, let R_k be the ratio to Collins and Nagatsu's parity-dependent leading term. Their recurrence, normalized recurrences and leading coefficients are prior work.

The proof shows R_k tends to one exactly when k^3/N tends to zero, and stays bounded exactly when k^3/N stays bounded. This answers their published optimal-scale question mathematically. At bounded cubic scale the limits are a hyperbolic cosine and a normalized hyperbolic sine, with parity retained.

The hyperbolic approximation H_k is accurate through k=o(sqrt(N)). The action

$$
G(t)=\sum_{j\ge4}\frac{2t^j}{j(j-2)}
$$

gives R_k asymptotic to H_k exp(NG(sqrt(k/N))) uniformly throughout every sublinear upper range. Successive truncations have sharp thresholds N^(1/2), N^(3/5), N^(2/3) and the stated general hierarchy. On bounded square-root ranges, the shorter quartic correction has an explicit finite error bound and an optimal N^(-1/4) error with a signed parity profile and exact supremum constant.

Keeping the permutation denominator and parity amplitude exact gives a formula valid for every 2<=k<=N. Its optimal worst relative error is C_* N^(-1/3)+o(N^(-1/3)), with C_* approximately 0.395496270091. A full uniform profile locates the largest error at odd orders near 1.16540187318 N^(1/3). This is a different approximation from the quartically corrected formula.

## Priority and remaining limits

The Laguerre identity, integral representations and saddle methods are classical. The source audit finds genuine overlap with classical Whittaker expansions, including the sublinear parameter range. The positive-square-root correction is derivable from those classical integrals. Han and Niles-Weed's permanent inequalities also give direct bounds for the same zero-depletion diagonal moments. These sources are credited and explicitly specialized.

A bounded search has not identified an exact duplicate of the attained mixed extrema or the complete collection of uniform probabilistic statements. That outcome is not a priority certificate. The diagonal results are presented as explicit uniform consequences and elementary proofs, without a claim of historical firstness.

The [readiness note](extension-round-02/SUBMISSION_READINESS.md) records current assembly and package checks, remaining source-access limitations, author metadata and destination decisions. No submission or external correspondence has been performed. Exact finite checks and numerical figures corroborate the written proofs, and do not establish an unrestricted theorem by themselves.
