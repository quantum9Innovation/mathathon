# Reusable techniques

**Label convention.** Appearances and originality assessments attributed to the authors are **Paper**. Generalizations and alternatives are **Derived** or **Interpretation**, not novelty claims verified against a broader literature.

## 1. Hashimoto trace before adjacency trace

- **Where:** Sections 1.1.2, 1.2.3, and 2.3.
- **Problem solved:** Arbitrary backtracking walks are hard to classify by skeletal type and edge multiplicity. Strict non-backtracking closed walks become $\operatorname{Tr}(H_G^k)$.
- **Why needed:** Non-backtracking forces complete traversal of each beaded path, so type compression preserves useful multiplicity data.
- **Standard or specific:** Standard operator, with the paper emphasizing the improved adjacency bounds obtained by doing the trace estimate before applying Ihara-Bass.
- **Reusable pattern:** Choose a walk operator whose combinatorics matches the desired structural classification, then translate spectra afterward.
- **Alternative:** Direct adjacency-trace combinatorics, discussed as unresolved in Section 3.6.2 because backtracking permits partial path traversal and unequal multiplicities.

## 2. Fibrewise old-new orthogonal decomposition

- **Where:** Equation (0.2), Definitions 1.1.16 and 1.1.18.
- **Problem solved:** Removes deterministic base eigenvalues before estimating random directions.
- **Why needed:** The trace method estimates all walks, while the theorem concerns only new eigenvalues.
- **Reusable pattern:** Decompose a lifted representation or function space into a pullback summand and a fibre-zero complement, then subtract the pullback trace once.
- **Dimensional warning:** The old space has the dimension of the base function space, independent of cover degree.

## 3. Permutation specialization as an algebraic expectation engine

- **Where:** Propositions 1.1.12, 2.3.8, and 2.5.6.
- **Problem solved:** Converts geometric walk and subgraph constraints into exact products of falling factorials.
- **Why needed:** Such products expand algebraically in $1/n$, unlike generic empirical random-model assumptions.
- **Reusable pattern:** Count labels by $(n)_b$ and fixed permutation constraints by $1/(n)_a$. Add order-$r$ truncation for uniformity.
- **Alternative:** Moments computed by case-specific inclusion-exclusion become cumbersome and usually hide the common order variable.

## 4. Order as a simultaneous topological and probabilistic index

- **Where:** Definitions 1.2.3 and 2.3.3, Lemma 1.3.5, Theorem 2.4.7.
- **Problem solved:** Groups infinitely many walk shapes by the power of $n$ at which they first matter.
- **Why needed:** One fixed order unit gives one extra $n^{-1}$ from an additional edge constraint relative to vertex choice.
- **Reusable pattern:** For permutation-governed random structures, identify the Euler characteristic or constraint deficit of a realization as its probability exponent.
- **Alternative:** Direct enumeration by graph size loses this relationship and generates unnecessary case divisions.

## 5. Coincidence-based remainder bounds

- **Where:** Lemma 1.3.5 and Theorem 2.3.13.
- **Problem solved:** Discards all walks of order at least $r$ with error $Ck^{2r+2}R^kn^{-r}$.
- **Why needed:** It allows exact finite combinatorics below a cutoff and a crude bound above it.
- **Reusable pattern:** Locate events where fresh randomness must hit an already visited state. Each such event supplies a factor near $k/n$.
- **Hidden cost:** Constants grow with $r$, and $k/n$ must be controlled.

## 6. Type-form factorization of walk sums

- **Where:** Sections 2.1.1 and 2.3.4.
- **Problem solved:** Separates finitely many discrete skeletons from continuously varying integer path lengths.
- **Why needed:** A fixed-order expansion contains finitely many types but infinitely many forms.
- **Reusable pattern:** Contract forced degree-two arcs, label local external data, then restore weighted length variables.
- **Alternative:** Classify only unlabelled graph isomorphism types. This loses traversal ordering and base lettering needed for exact probabilities and polyexponential sums.

## 7. Polyexponential and error convolution calculus

- **Where:** Section 2.2, especially Theorems 2.2.6, 2.2.10, and 2.2.14.
- **Problem solved:** Multiplies local length contributions while retaining a useful global exponential classification.
- **Why needed:** Type-form coefficients are weighted convolutions of base-walk statistics.
- **Reusable pattern:** Isolate finitely many exact exponential bases, permit a slightly subcritical error, then use weight inequalities and geometric tails to show closure.
- **Alternative:** Insist on one exact polyexponential formula. Weighted examples show that residue classes may be necessary, motivating mod-$S$ functions in Section 3.5.

## 8. Certification by a strict spectral inequality

- **Where:** Definitions 1.4.1 and 2.4.25 through 2.4.27.
- **Problem solved:** Raw higher-order trace coefficients need not be $B$-Ramanujan because tangling subgraphs create excessive growth.
- **Why needed:** Removing those graphs alone does not automatically simplify the sum over remaining realizations.
- **Paper-specific innovation:** Restrict to $\rho_H(\operatorname{Graph}(w))<R^{1/2}$ and fixed order cutoff. The authors present this as a simpler replacement for selective traces.
- **Reusable pattern:** Define an admissibility rule whose monotonicity and growth estimates are both tailored to the later algebraic decomposition.
- **Alternative:** The paper describes selective traces as more cumbersome and does not know how to obtain the main result directly from expected certified traces without tangle indicators.

## 9. Finitely generated upper sets and Möbius cone decomposition

- **Where:** Section 2.4.3 and Proposition 2.4.28.
- **Problem solved:** Converts an irregular admissible length set into finitely many lower-bounded regions.
- **Why needed:** Cone sums align with weighted convolutions and geometric series.
- **Reusable pattern:** Show path-lengthening monotonicity, use componentwise order, take minimal certificates, and intersect cones by componentwise maxima.
- **Standard or specific:** Product-order Noetherianity is standard in spirit. Its particular use to certify non-backtracking walk traces is tailored to this paper.
- **Failure warning:** Absolute convergence and stable cone intersections are necessary for the infinite rearrangement.

## 10. Short-long multiplicity splitting

- **Where:** Lemma 2.4.32 and Lemma 2.4.34.
- **Problem solved:** Controls $W_{\mathcal T}(\mathbf m)P(\mathbf k)$ over all certified length and multiplicity vectors.
- **Why needed:** Large multiplicities force $\sum k_f$ to be small, while small multiplicities have finitely many patterns.
- **Reusable pattern:** Choose a fixed threshold after the desired exponential error is named. Bound high-weight terms by decay, then use finite convolution closure on low-weight terms.
- **Alternative:** Splitting merely into multiplicity $1$ and multiplicity at least $2$ forces sharper polynomial prefactor estimates. The authors explicitly use the larger threshold to simplify these bounds.

## 11. Generalized $\Omega$-types and tangle-indicator subtraction

- **Where:** Section 2.5.
- **Problem solved:** Expands certified traces restricted to graphs containing specified tangles.
- **Why needed:** The desired tangle-free expectation is the difference of total and tangle-present certified expectations.
- **Reusable pattern:** Enrich the type with the retained obstruction, re-run local factorial expansions, then invert inclusion indicators with finite Möbius coefficients.
- **Alternative:** Direct conditioning changes coefficients and the authors explicitly note that they cannot show the required vanishing for a conditional raw trace expansion.

## 12. Shift-operator side-stepping

- **Where:** Section 2.6.
- **Problem solved:** Uses $B$-Ramanujan expansions without explicitly knowing their polynomial coefficients.
- **Why needed:** Unknown polyexponential terms can dominate a naive single-moment estimate.
- **Reusable pattern:** Let $Q(S)$ annihilate all finite bases, keep even powers nonnegative on real outliers, choose logarithmic moments, then use $Q_{\ell,D}$ to isolate one base and its occurrence exponent.
- **Alternative:** Explicitly compute all coefficients. The paper notes that this is cumbersome and sometimes unavailable. Simple vanishing-polynomial inference would require stronger high-probability input than is initially available.

## 13. Spreading to remove dominant-base concentrations

- **Where:** Sections 3.2 and 3.3.
- **Problem solved:** Controls near-$d$ and near-$(-d)$ adjacency eigenvalues, or near-$\pm(d-1)$ Hashimoto eigenvalues.
- **Why needed:** Side-stepping localizes outliers near base values but does not by itself make those concentrations rare enough below the fundamental order.
- **Reusable pattern:** Reduce a structured cover to a bouquet by spanning-tree contraction, apply entropy and permutation estimates, then transfer spectral gaps back through walk powers.
- **Alternative:** There is no substitute developed in this paper for the Ramanujan refinement.

## 14. Algebraic decidability for strict spectral comparisons

- **Where:** Proposition 3.3.3.
- **Problem solved:** Makes fundamental-order computation finite rather than merely existential.
- **Why needed:** An algorithm cannot decide $\rho(H_L)>R^{1/2}$ only by uncontrolled floating-point approximation.
- **Reusable pattern:** Enumerate finitely many integer-matrix candidates, compute algebraic degree and coefficient bounds, and use separation of nonzero algebraic numbers.
- **Alternative:** Practical calculations can sometimes exploit special structure, but the paper supplies no uniform efficient algorithm.

## Technique selection guide

**Interpretation.** To reproduce the main theorem, prioritize techniques 1 through 12. Technique 13 is necessary only for the sharper Ramanujan exponent, and technique 14 is about computing that exponent. Partition sections by function: D2 to D4 build expansions, D5 to D8 make coefficients tractable, D9 to D10 turn them into spectral bounds, and D11 to D12 refine the rare-event exponent.
