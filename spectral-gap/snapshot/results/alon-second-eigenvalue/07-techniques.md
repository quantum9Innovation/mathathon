# Reusable techniques

## 1. Non-backtracking trace calculus

- **Where:** Lemma 2.3, Section 3.6, Section 10.
- **Problem:** Ordinary adjacency powers mix forward walks and immediate backtracking, obscuring tree growth.
- **Why needed:** The Ramanujan barrier is controlled by non-backtracking branching $d-1$.
- **Status:** Standard spectral graph machinery, with paper-specific trace conventions.
- **Reusable pattern:** Define walk matrices recursively, evaluate them as polynomials of adjacency, and derive spectrum from the recurrence roots.
- **Alternative:** Work directly with the Hashimoto matrix and Ihara-Bass. That is compact abstractly, but the paper's explicit $q_k$ and $\widetilde q_k$ formulas expose parity and multiplicity details.

## 2. Two-test Rayleigh quotient obstruction

- **Where:** Lemma 2.9, Theorems 2.10, 2.11, and 4.2.
- **Problem:** A local subgraph gives one large Rayleigh quotient, but $\lambda_1$ already has the constant eigenvector.
- **Why needed:** One must prove a second large eigenvalue, not just a large operator norm.
- **Status:** Standard variational linear algebra, carefully adapted to graph locality.
- **Reusable pattern:** Pair a finitely supported defect test with a broad test on its distant complement. Make them orthogonal to each other's adjacency images and apply Courant-Fischer to their span.
- **Alternative:** Use disconnectedness when available. That is simpler but much less general and does not leverage an arbitrary tangle's tree completion.

## 3. Tree completion of a finite defect

- **Where:** Definition 3.12, Figure 1, Theorem 3.13, Theorem 4.2.
- **Problem:** Identify the worst spectral influence of a finite local pattern independently of the rest of a graph.
- **Why needed:** Hypercriticality must become a precise adjacency threshold.
- **Status:** Standard universal-cover idea with a paper-specific VLG and Perron implementation.
- **Reusable pattern:** Attach just enough trees to regularize degree, solve growth on the infinite completion, then truncate approximate eigenfunctions.
- **Alternative:** Optimize directly over finite balloons around a tangle. This may be possible but makes the limiting spectrum and clean threshold harder to identify.

## 4. Variable-length suppression and realization

- **Where:** Sections 3.2 to 3.5, Definitions 5.13 to 5.19.
- **Problem:** Long paths add many irrelevant degree-two vertices to enumeration.
- **Why needed:** Finitely many compressed types can represent infinitely many beaded forms.
- **Status:** Established constrained-coding and symbolic-dynamics machinery, specialized here.
- **Reusable pattern:** Suppress beads, retain total length and endpoint letters, and preserve Perron growth under subdivision.
- **Alternative:** Keep full forms. That avoids abstraction but destroys finite-type organization and makes generating function bounds unwieldy.

## 5. Walk generating functions and first Perron crossing

- **Where:** Theorems 3.5, 3.6, 3.13, and 6.6.
- **Problem:** Walk counts are combinatorial objects, while spectral gaps are analytic conditions.
- **Why needed:** The central input is convergence slightly beyond $q^{-1/2}$.
- **Status:** Standard Perron-Frobenius and generating function argument extended to VLG.
- **Reusable pattern:** Compute $Z_G(z)$, locate where it first reaches Perron eigenvalue 1, and equate $1/z$ with exponential walk growth.
- **Alternative:** Jordan-block asymptotics of a finite non-backtracking matrix. This handles finite graphs but not the uniform infinite and limiting objects used in Section 9.

## 6. Order-based factorial expansion

- **Where:** Sections 4 and 5 and Lemma 9.6.
- **Problem:** Expected walk or tangle counts depend on $n$ through many factorials.
- **Why needed:** The proof needs arbitrary finite expansions in $1/n$ with polynomial coefficient control.
- **Status:** Standard random permutation asymptotics, formalized in SSIIC collections.
- **Reusable pattern:** Pull out $n^{v-e}$, expand every finite product in inverse factorials, and bound discarded classes by marking coincidences.
- **Alternative:** Poisson approximation for each occurrence count. This can be intuitive at low order but does not replace algebraic control of all expansion coefficients as $k$ grows.

## 7. Inclusion counts versus occurrence probabilities

- **Where:** Theorem 4.7 and Section 9.
- **Problem:** Expected inclusions count repeated and automorphic embeddings, whereas $\chi_\Psi$ records only presence.
- **Why needed:** Conditional tangle strata require expectations of indicators, not inclusion totals.
- **Status:** Inclusion-exclusion for the lower occurrence bound and generalized Möbius inversion for exact expansion.
- **Reusable pattern:** Quotient by automorphisms, bound pair overlaps by order, and invert the finite inclusion matrix on derived tangles.
- **Alternative:** Truncate ordinary inclusion-exclusion. It becomes cumbersome with many overlapping tangle shapes, which is why Möbius inversion is cleaner here.

## 8. New types and fixed versus long decomposition

- **Where:** Definitions 5.18 and 5.19 and Sections 5.4 and 8.
- **Problem:** A type alone forgets where short dangerous subgraphs sit.
- **Why needed:** Selectivity depends on fixed labels and short edge lengths and must be constant within each enumeration class.
- **Status:** Paper-specific combinatorial refinement.
- **Reusable pattern:** Freeze bounded details exactly, mark only the remaining edges as long, and sum their lengths afterward.
- **Alternative:** Freeze every length. This gives finite individual cases but infinitely many classes and no uniform summation.

## 9. Selective trace surgery

- **Where:** Definitions 6.1 to 6.5 and Theorem 6.6.
- **Problem:** Ordinary trace expansions diverge because a few head growth rates exceed $\sqrt q$.
- **Why needed:** A strict base reduction to $\sqrt q-\eta$ makes the rest of the proof summable.
- **Status:** The central paper-specific construction.
- **Reusable pattern:** Reject any object containing a local configuration above the target spectral growth, then prove convergence slightly beyond the target inverse scale.
- **Alternative:** Assign weights to tangled walks instead of deleting them. That might retain more information, but the paper does not develop a suitable weighting. Directly analyzing unmodified traces is left open in Section 15.

## 10. Alternating-walk geometric majorants

- **Where:** Theorem 6.6's proof.
- **Problem:** Fixed low-growth blocks and long excursions can Alternate arbitrarily often.
- **Why needed:** A generating function bound must cover infinitely many alternations uniformly.
- **Status:** Standard geometric-series majorization, tailored to selective walks.
- **Reusable pattern:** Sum fixed-block series $h$, bound first long passages by a tail $\widetilde h^S$, and close the alternating decomposition with $(1-X)^{-1}$ after making $X(z_0)<1$.
- **Alternative:** Direct induction on the number of long edges. It may work but makes uniformity and constants harder to see than a scalar denominator.

## 11. d-Ramanujan functions and convolution

- **Where:** Definition 2.1, Section 7, and Section 8.
- **Problem:** Products of walk-length distributions generate convolutions, not just products.
- **Why needed:** The principal scale $q^k$ must be separated from error scale $q^{k/2}$ through infinite sums.
- **Status:** Standard exponential-polynomial spectral decomposition under a paper-specific name.
- **Reusable pattern:** Write $f_i=q^kp_i+e_i$. Convolve principal polynomials exactly, extend mixed sums to infinity, and bound tails using $q^{-k}$ normalization.
- **Alternative:** Generating functions for all word sums. The paper does use generating functions locally, but d-Ramanujan notation makes the final trace scale explicit.

## 12. Coefficient norms and geometric moment tails

- **Where:** Definition 8.4 and Lemma 8.8.
- **Problem:** Infinite sums $\sum_rQ(k-r)g(r)$ need to remain polynomial with controlled coefficients.
- **Why needed:** Sidestepping later exploits bounded degree and coefficient norms.
- **Status:** Standard finite-moment summation, packaged for the proof.
- **Reusable pattern:** Use $\sum r^j\rho^r<\infty$ for $\rho<1$ and estimate tails with $u^{2D}\rho^u$.
- **Alternative:** Pointwise polynomial bounds. They can obscure uniformity of degree and coefficient size needed in the final summation.

## 13. Strong trace finite differences

- **Where:** Sections 10 and 11.
- **Problem:** Unknown polynomials in $k$ contaminate a high-order trace expansion.
- **Why needed:** Coefficients cannot be determined explicitly, unlike the older short-expansion method.
- **Status:** Standard discrete calculus used in a tailored probabilistic way.
- **Reusable pattern:** Convert the trace to $\sum (1-\theta)^k$, apply $(\sigma-1)^s$, and use $(\sigma-1)^s(1-\theta)^k=(-\theta)^s(1-\theta)^k$.
- **Alternative:** Estimate coefficients by comparing many $k$ values directly. This introduces a linear system and requires the coefficient control the proof deliberately avoids.

## 14. Three-band spectral partitioning

- **Where:** Lemma 11.1.
- **Problem:** Different $\theta$ sizes require different inequalities, and complex values can cancel.
- **Why needed:** A single power comparison does not handle all regimes.
- **Status:** Paper-specific assembly of analytic and probabilistic estimates.
- **Reusable pattern:** Use Taylor expansion for tiny values, two-power comparison for intermediate values, and direct exponential decay for large values with reality ensuring sign control.
- **Alternative:** A one-step large-deviation approach would need individual spectral tail information not available here.

## 15. Polynomial recovery from an interval

- **Where:** Sublemma 11.2.
- **Problem:** Large powers control a polynomial only for large $k$.
- **Why needed:** Lemma 11.1's conclusion is needed for all $1\leq k\leq n^\gamma$.
- **Status:** Elementary finite-difference interpolation.
- **Reusable pattern:** Use $(\sigma-1)^sg=0$ to express a backward value as a binomial combination of values inside the controlled interval.
- **Alternative:** Lagrange interpolation. It is possible but gives less immediate stability constants than the paper's shift identity.

## 16. Magnification as a priori spectral separation

- **Where:** Section 12.
- **Problem:** The final trace argument requires all nontrivial $\mu$ to be bounded away from $q$.
- **Why needed:** Otherwise low but uncontrolled spectral values might contaminate the comparison.
- **Status:** Standard expansion-to-spectrum implication plus a model-specific counting proof.
- **Reusable pattern:** Bound a slight neighborhood containment event by factorial entropy, show its exponent grows faster than $C\log n$, and union bound over all sets.
- **Alternative:** A direct known expansion theorem from another paper. That would shorten this section but introduce a model-specific external hypothesis and would not supply the paper's polynomial failure rate.

## 17. Logarithmic trace closure

- **Where:** Section 13.
- **Problem:** Turn moment asymptotics into a high-probability bound on the largest nontrivial eigenvalue.
- **Why needed:** The theorem claims a fixed additive $\epsilon$ and a polynomial failure rate.
- **Status:** Standard high-trace method with careful new remainder control.
- **Reusable pattern:** Balance an outlier $(e^\eta\sqrt q)^k$ against a linear background $nq^{k/2}$ and choose $k\asymp\log n$ so both remainder terms share a polynomial scale.
- **Alternative:** Markov's inequality on one fixed power. That is exactly what is done after the difficult expansion work, but it is insufficient without Sections 8 to 12.

## Technique dependency worth retaining

The paper has many definitions, but three reusable ideas form its spine:

1. **Local spectral defect analysis** identifies which finite tangles matter.
2. **Selective generating function convergence** turns removal of those tangles into summable global trace estimates.
3. **Finite-difference spectral recovery** extracts an eigenvalue conclusion without knowing the expansion coefficients.

Everything else supports one of those three mechanisms.
