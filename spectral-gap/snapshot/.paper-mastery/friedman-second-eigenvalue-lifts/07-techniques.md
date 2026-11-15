# Reusable techniques

## 1. Quadratic spectral transfer

- **Where:** Ihara-Bass in Eq. 12 and the quantitative conversion in Section 2.2.
- **Problem solved:** Non-backtracking paths are easier to enumerate, but the motivating theorem concerns adjacency eigenvalues.
- **Why the paper needs it:** It turns $\lambda^2-\mu\lambda+(d-1)=0$ into an exact dictionary with separate control of the $\pm1$ spectrum.
- **Status:** Standard cited theorem, used with a sharp elementary inversion.
- **Reusable pattern:** Prove an operator adapted to local path combinatorics first, then transfer its spectrum through a determinant identity. Preserve the quantitative inversion, not only the limiting threshold.
- **Possible alternative:** Work directly with adjacency walks. The paper's introduction explains why this is harder here, especially at walk lengths much greater than $\log n$.

## 2. Rank-one Perron removal for a nonnormal operator

- **Where:** Lemma 3 and Eq. 14.
- **Problem solved:** $B$ has no guaranteed orthonormal eigenbasis, so ordinary symmetric trace or min-max arguments do not directly apply.
- **Why the paper needs it:** Only the eigenvalue $d-1$ associated with $\chi$ should be discarded.
- **Status:** Elementary linear algebra, central to the proof's formulation.
- **Reusable pattern:** Find $S$ containing the unwanted spectral part, verify $\operatorname{im}S\subset\ker R$ and $\operatorname{im}S^*\subset\ker R$, then bound all new eigenvalues by $S+R$ restricted to $\ker S$.
- **Possible alternative:** A Schur complement or resolvent calculation could encode the same separation, but would add machinery without improving this step.

## 3. Transfer through positive-probability conditioning

- **Where:** Eq. 7 and the deduction of Theorem 1 from Theorem 2.
- **Problem solved:** Uniform random matchings permit explicit probabilities, while the desired model is uniform over simple graphs.
- **Why the paper needs it:** Conditional on simplicity, every simple graph is equally likely because each has the same number of half-edge matchings.
- **Status:** Standard configuration-model method, invoked with a cited simplicity limit.
- **Reusable pattern:** If a computationally convenient law conditioned on an event $H$ gives the target law and $\mathbb P(H)$ does not vanish, bad-event probabilities transfer by division by $\mathbb P(H)$.
- **Possible alternative:** Direct labeled-graph enumeration. This would sacrifice the clean matching computations used throughout Section 2.4.

## 4. Delete bad supports before taking expectations

- **Where:** Definitions of $B^{(\ell)}$ and $\underline B^{(\ell)}$ in Eqs. 18 and 19.
- **Problem solved:** Polynomially rare tangles dominate very high moments even though they do not affect the typical desired spectral event.
- **Why the paper needs it:** It decouples the whp spectral statement from the failing naive expected trace.
- **Status:** Standard rare-event truncation in spirit, sharpened into a graph-support operation where tangles are the relevant objects.
- **Reusable pattern:** Identify a typical event on which an exact matrix identity holds. Delete path contributions outside that event before centering or taking expectations. Bound the event's failure separately.
- **Possible alternative:** Uniform expectation bounds on the full path family would reintroduce precisely the obstruction demonstrated on page 3.

## 5. Delete before centering, then telescoping with an exact remainder

- **Where:** Lemma 7, Eq. 22, and Figure 2.
- **Problem solved:** Centered weights simplify expectations, but restricting paths and replacing matrix entries do not commute.
- **Why the paper needs it:** To compare $B^{(\ell)}$ and $\underline B^{(\ell)}$ on $\chi^\perp$ without pretending they are equal.
- **Status:** Algebraic telescoping plus a paper-specific graph remainder.
- **Reusable pattern:** Apply $\prod x_s=\prod y_s+\sum_k(\prod_{s<k}y_s)(x_k-y_k)(\prod_{s>k}x_s)$, then classify which indexed sums factor into lower-order operators and which remain.
- **Possible alternative:** Ignore the non-factorable paths. Figure 2 shows why that is false. The remainder is mandatory.

## 6. Consistency types for dependent matching products

- **Where:** Definition 10 and Proposition 11, adapted in Proposition 28.
- **Problem solved:** Long products of matching or permutation indicators have complicated dependencies and signs after centering.
- **Why the paper needs it:** A uniform crude bound on every edge forfeits the extra cancellation on clean, once-visited consistent edges.
- **Status:** Paper-specific organization of conditional moment calculations.
- **Reusable pattern:** Classify combinatorial occurrences by multiplicity and shared endpoints. Isolate the clean class, compute its alternating conditional expectation exactly, and control exceptional collisions separately by a union tail.
- **Possible alternative:** Treat the entries as independent centered variables. They are not independent, so this is only a heuristic and can miss both magnitude and sign.

## 7. Finite-difference annihilation of polynomial terms

- **Where:** Lemma 12, Eqs. 24 through 26.
- **Problem solved:** A binomial alternating product contains a confluent hypergeometric form whose asymptotics the paper wants to derive directly.
- **Why the paper needs it:** It converts exact polynomial cancellations into a quantitative bound suitable for Proposition 11.
- **Status:** Classical finite differences inside a tailored two-regime estimate.
- **Reusable pattern:** Expand into terms $P_s(t)$ with controlled degree, use $\sum_t\binom kt(-1)^tP(t)=0$ for $\deg P<k$, bound high-degree terms directly, and truncate the remaining signed factor to expose cancellation.
- **Possible alternative:** Cite hypergeometric asymptotics directly. The paper explicitly chooses a self-contained derivation.

## 8. Alternating high trace

- **Where:** Eqs. 35 through 38 and Figure 3.
- **Problem solved:** Operator norms do not expand directly into matrix powers unless they are normal, but $\operatorname{tr}((CC^*)^m)$ is always available.
- **Why the paper needs it:** It turns a norm estimate into $2m$ concrete path sums.
- **Status:** Standard moment method, with a paper-specific path-circuit geometry.
- **Reusable pattern:** Use $\|C\|^{2m}\leq\operatorname{tr}((CC^*)^m)$, reverse even strands, assign boundary multiplicities, and count the resulting closed circuits by their isomorphism types.
- **Possible alternative:** Resolvent or Stieltjes-transform methods do not naturally exploit the paper's finite tangle-free path restriction.

## 9. Canonicalization and three-factor path accounting

- **Where:** Lemmas 15 through 17 and their lift analogues.
- **Problem solved:** Path families are huge, but many paths are relabelings with identical expected weight.
- **Why the paper needs it:** Expected weight depends on the unlabeled visited support, not on vertex names or local half-edge names.
- **Status:** Standard graph-enumeration strategy, with paper-specific bounds.
- **Reusable pattern:** Group paths into isomorphism classes, then multiply three terms: labelings per class, number of canonical classes, and expected weight per class. Change variables to $s$, $a$, and $g=a-s+1$ before summing.
- **Possible alternative:** Count labeled paths directly. This hides the cancellation between $n^s$ label choices and $(dn)^{-a}$ matching costs.

## 10. Cycle-rank compression of repeated excursions

- **Where:** Lemma 16 and Figure 4.
- **Problem solved:** A path can revisit an excess edge arbitrarily often, generating too many important times for a naive encoding.
- **Why the paper needs it:** Entropy must depend on cycle rank $g$, not the unbounded number of repeats.
- **Status:** The central combinatorial encoding tailored to tangle-free paths.
- **Reusable pattern:** Build a spanning tree, split visits into first, important, short-cycling, long-cycling, and superfluous times, then store enhanced marks only for cycle-changing events. Let uniqueness of the cycle absorb repeated excursions.
- **Possible alternative:** Store all return times. That simple encoding fails to provide the exponent needed for the final moment sum.

## 11. Spanning forests for remainder paths

- **Where:** $G_\gamma^k$ and Lemmas 20, 21, 35, and 36.
- **Problem solved:** Omitting the $k_i$-th pair on each strand can disconnect the used support.
- **Why the paper needs it:** The connected-tree excess count $g=a-s+1$ must be replaced by a forest calculation with $p$ components.
- **Status:** A careful adaptation of the main canonical encoding.
- **Reusable pattern:** Use $a-s+p$ total excess forest edges and note that each remainder component contains a cycle. This yields $a\geq s$ and removes the global factor of $n$ seen in the centered trace sum.
- **Possible alternative:** Force connectivity by adding back the omitted pairs. That loses the sharper support-specific probability bound.

## 12. Two logarithmic scales

- **Where:** Choices of $\ell$ in Section 2.6 and $m$ in Eqs. 41, 47, 74, and 77.
- **Problem solved:** Spectral roots, tangle probability, matching asymptotics, and moment tails impose different requirements.
- **Why the paper needs it:** $\ell\asymp\log n$ suppresses polylogarithmic norm overestimates, while $m\asymp\log n/\log\log n$ makes $(c\ell m)^{O(m)}/n$ geometrically small without violating $2\ell m\leq\sqrt{dn}$.
- **Status:** Standard high-moment calibration, executed cleanly.
- **Reusable pattern:** Keep the path-block length and trace-moment parameter conceptually separate. Check every intermediate length hypothesis after choosing them, rather than focusing only on the final limit.
- **Possible alternative:** Directly choose the total trace length without a block decomposition. This loses the ability to delete tangles before the long-path moment calculation.

## 13. Gelfand growth as a path-enumeration budget

- **Where:** Eq. 67 and Lemma 31 for random lifts.
- **Problem solved:** An irregular base graph has no uniform branching factor $d-1$.
- **Why the paper needs it:** Base projections of first-exit segments must be counted with the correct exponential growth rate.
- **Status:** Standard spectral-radius estimate, adapted as a combinatorial counting tool.
- **Reusable pattern:** Fix $\rho$ above the spectral radius, dominate finite initial segments by $c_\rho\rho^s$, and multiply segment budgets using the total count of newly discovered vertices. Only afterward let $\rho$ approach the true radius.
- **Possible alternative:** Maximum-degree branching gives a simpler but generally nonsharp bound and would not produce $\sqrt{\rho_1}$ in Theorem 23.

## Technique hierarchy

The most reusable sequence is:

1. Reformulate the spectral problem on the path-adapted operator.
2. Remove inherited or trivial directions with an algebraic restriction.
3. Define a typical good event through path supports.
4. Delete bad paths before moment centering.
5. Expand with exact algebraic remainders.
6. Evaluate random weights by support types and conditional cancellation.
7. Circuit-trace, canonicalize, and sum in cycle-rank variables.
8. Take roots at logarithmic scales and transfer back to the original spectrum.

The details that make this paper work, rather than a generic high-trace sketch, are steps 3 through 6 and Figure 4's cycle compression.
