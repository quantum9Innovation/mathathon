# Spectral gap selection report

Frozen: November 15, 2026, approximately 01:07 UTC. Global cutoff remains 08:21 UTC. No other current topic audit was read before this report.

## Strongest supported result

The direct problem target now has a self-contained proof. In addition, the audit establishes a sharp scale for relative asymptotics of centered permutation moments, answering the precise scaling question in Collins and Nagatsu's published Remark 3.4.

For a uniform $N\times N$ permutation matrix, set

$$a_k(N)=\mathbb E\prod_{i=1}^k(M_{ii}-1/N),\qquad
R_k(N)=a_k(N)/\widetilde a_k(N),$$

where $\widetilde a_k$ is the explicit even or odd leading term from that paper. The [frozen proof](sharp-scaling-v2.md) gives

$$\frac{2k^3}{27N}\le R_k(N)-1,
\qquad R_k(N)\le\exp(3k^3/N)\quad(2k\le N).$$

Thus $R_{k_N}\to1$ exactly when $k_N^3/N\to0$. Bounded two-sided comparability holds exactly when $k_N^3/N=O(1)$. The integrator independently reconstructed revision 1's recurrences, polynomial identities, lower bounds, and upper bound without finding a gap. Revision 2 adds the immediate bounded-comparability corollary and clearer attribution.

## Why the proof is understandable

Every centered permutation row sums to zero. A product of entries using new rows and columns can therefore be expressed in terms of collisions. Two entries in one column cannot both equal one, so a collision removes one or two factors. This gives a positive recurrence.

After dividing by the known leading term, the recurrence has an unavoidable positive error of order $j^2/N$ at the $j$th pair of entries. Summing approximately $k/2$ such errors gives order $k^3/N$. The lower bound follows by keeping these positive contributions. They cannot cancel.

As a worked case,

$$a_4(N)=\frac{3(N+6)}{N^4(N-1)(N-2)(N-3)},
\qquad \widetilde a_4(N)=3N^{-6}.$$

Hence $R_4=1+12/N+O(N^{-2})$. The lower-bound proof gives the exact inequality $R_4-1\ge12/N$.

## Fit to problem 21

The [direct proof](permutation-proof-v2.md) treats mixed centered and uncentered products, repeated cells, inconsistent cells, and independent base-edge permutations. It proves

$$|\mathbb EP|\le e\,2^b n^{-a}
\left(\frac{\sqrt{a-1}}{\sqrt n-\sqrt{a-1}}\right)^h,
\qquad 2\le a\le\sqrt n.$$

This implies Bordenave Proposition 28 and its use in Brito, Dumitriu, and Harris Lemma 7. The connection is exact: the bipartite matching matrix has one uniform permutation as its off-diagonal block.

The [source audit](source-findings-v2.md) gives two exact counterexamples to the conditional assertion in Bordenave equation (62), page 38. These are defects in that displayed argument, not counterexamples to the proposition. Expanding to compatible prescribed cells before conditioning avoids both defects.

## Literature and novelty boundary

- Bordenave's original product estimate and Collins-Nagatsu's row-sum recurrence are prior results. The normalized error recurrences also appear in Collins-Nagatsu's proof and are credited explicitly.
- The final 2026 Collins-Nagatsu paper still asks the scaling question on page 473. The argument here supplies a necessary lower bound, and a simple independent sufficient upper bound, for the exact stated moments.
- The newly posted [Bordenave-Zhu paper, arXiv:2611.07104v1](https://arxiv.org/html/2611.07104v1), was inspected at its matching estimate, Lemma 2.1. It retains the factor $3k/\sqrt N$, cites Proposition 28 and Collins-Nagatsu, and adds a repeated-cell approximation. That lemma does not contain the cubic-scale necessity result.
- Collins and Nagatsu's [February 2026 paper, arXiv:2602.04614v1](https://arxiv.org/html/2602.04614v1), studies smooth multi-trace statistics for Gaussian ensembles and Haar classical groups. Its stated results do not address this centered diagonal permutation moment.
- The search was targeted, not exhaustive. The defensible claim is a proof answering the published question at its precise scope. A claim of first discovery across all literature is not established.

## Evidence

The exact checks passed: 19,319 finite-difference recurrences, 4,416 direct averages over all 24 permutations of four elements, 9,585 incidence-pattern cases, and 3,645 multicolor products. The scale proof additionally passed 999 polynomial-identity checks, 7,140 exact lower-bound cases, and 7,021 normalized-recurrence checks. These are corroboration. The general results rest on the written proofs.

The primary source PDFs and hashes are preserved. The original imported snapshot was not modified. All new files are confined to this audit directory.

## Finite-defect assessment

The imported separated-defect theorem and adjacent-pair family remain worthwhile separate research. The adjacent-pair review correctly distinguishes the physical resolvent branch and the cubic root. This run did not independently certify all finite-defect convergence and finite-size assertions, and it did not find a stronger new defect result. The direct permutation proof and the cubic-scale theorem are more responsive to the official problem, so they took priority.

## Recommendation and remaining work

Treat this as a serious selection candidate on mathematical contribution and direct problem fit. The submission can lead with the row-sum proof of Proposition 28, show the explicit conditioning issue it avoids, and conclude with the sharp cubic-scale consequence.

Remaining work: a clean final exposition, a final independent check of the bounded-comparability wording, and limited additional priority checking. Critical-scale formulas involving hyperbolic functions remain exploratory and are excluded from the supported result.
