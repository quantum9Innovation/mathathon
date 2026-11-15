# Executive map

## 1. What problem does the paper solve, and why does it matter?

**Paper.** The paper gives a new proof that nontrivial adjacency eigenvalues of a uniform random $d$-regular graph are, with high probability, at most $2\sqrt{d-1}+o(1)$ in absolute value. This is Friedman's theorem, Theorem 1 on page 2. The same order of magnitude is unavoidable by Alon-Boppana, Eq. 1 on pages 1 and 2, so random regular graphs asymptotically achieve the best possible spectral gap up to a vanishing error.

The paper then proves an analogous upper bound for all **new** non-backtracking eigenvalues of a random lift of a fixed connected graph with more edges than vertices. Their limiting upper scale is $\sqrt{\rho_1}$, where $\rho_1$ is the Perron eigenvalue of the base graph's non-backtracking matrix. This is Theorem 23 on page 32. For a regular base graph, Ihara-Bass converts this into the $2\sqrt{d-1}+o(1)$ bound for new adjacency eigenvalues, Corollary 24 on page 32.

**Interpretation.** The central issue is not merely estimating a random matrix norm. Rare, polynomially unlikely subgraphs can dominate very high moments even while having negligible influence on the typical spectrum. The paper isolates those rare combinatorial objects before performing its moment calculation.

## 2. Main contribution in its simplest and strongest forms

### Simplest honest form

**Paper.** Replace the adjacency matrix by the non-backtracking matrix, discard walks whose visited graph has more than one cycle, center the remaining random path weights among zero-sum vectors, and estimate the centered and remainder operators separately. This yields a substantially shorter route to Friedman's theorem and extends to random lifts.

### Strongest form stated in the paper

For every $0<a<1$, there is a constant $c$ depending on $d$ and $a$ such that, for uniform simple $d$-regular graphs,

$$
\mathbb P\left(\mu_2\vee|\mu_n|\geq 2\sqrt{d-1}
+c\left(\frac{\log\log n}{\log n}\right)^2\right)\leq n^{-a}.
$$

This is Eq. 2 on page 2. For the configuration model's non-backtracking matrix, the corresponding additive scale is $c\log\log n/\log n$, Eq. 13 on page 7.

For random lifts of any finite connected base graph with $|E|>|V|$, the paper proves

$$
|\lambda_1|\leq \sqrt{\rho_1}+o(1)\quad\text{with high probability},
$$

where $\lambda_1$ is the largest new non-backtracking eigenvalue. No extra assumption on the base graph beyond the stated hypotheses is needed for Theorem 23. In the regular case, the same adjacency consequence is attributed to Friedman and Kohler in Corollary 24.

### What the contribution does not say

- It does not show that a typical graph is exactly Ramanujan, because the upper bound includes $o(1)$.
- It does not construct explicit Ramanujan graphs or certify an exact finite-$n$ optimal gap.
- It does not prove Friedman's general adjacency conjecture for lifts of irregular graphs. Theorem 23 concerns the non-backtracking operator, while Corollary 24 requires regularity for the Ihara-Bass conversion.
- It does not supply explicit finite-$n$ constants or an optimized rate for Theorem 23.

## 3. Main assumptions

**Paper.**

- $d\geq 3$ is fixed while the graph size tends to infinity.
- For Theorem 1, $nd$ is even and the graph is uniform among simple $d$-regular graphs.
- The workhorse configuration model permits loops and multiple edges. Its simplicity probability has a positive limit, which transfers high-probability statements to the uniform simple model.
- $\ell$ is small enough for local tangle-freeness, ultimately $\ell\sim\kappa\log_{d-1}n$ with $0<\kappa<1/4$.
- Trace exponents satisfy $2\ell m\leq\sqrt{dn}$ for the main centered estimate and comparable bounds for remainders and lifts. The explicit choices $m\asymp\log n/\log\log n$ satisfy them.
- For lifts, the base is finite and connected, $|E|>|V|$, and independent uniform fiber permutations generate the lift. The lift parameter $\rho$ is fixed with $\rho>\rho_1$ and later chosen arbitrarily close to $\rho_1$.

**Derived.** The condition $|E|>|V|$ rules out a connected graph of maximum degree at most $2$, since such a graph would be a path or cycle with $|E|\leq|V|$. Thus the maximum-degree condition $d\geq3$ used in Lemma 27 is compatible with Theorem 23's hypotheses.

## 4. Main techniques

1. **Ihara-Bass dictionary:** adjacency eigenvalues $\mu$ produce non-backtracking eigenvalues solving $\lambda^2-\mu\lambda+(d-1)=0$, Eq. 12 on page 6.
2. **Non-normal spectral reduction:** Lemma 3 on page 7 handles $B$ without assuming normality, using a rank-one Perron component and a restricted operator norm.
3. **Delete before centering:** $B^{(\ell)}$ and $\underline B^{(\ell)}$ restrict paths before replacing matching entries $M_{ef}$ by $\underline M_{ef}=M_{ef}-1/(dn)$, Eqs. 18 and 19 on page 9.
4. **Telescoping with remainders:** Lemma 7 and Figure 2 explain both the expansion and the matrices $R_k^{(\ell)}$, which account for locally tangle-free pieces forming a tangle together.
5. **Conditional moment cancellation:** Proposition 11 on page 13 distinguishes consistent and inconsistent path edges and extracts an extra $(3k/\sqrt{dn})^{a_1}$ factor from near-centered unique edges.
6. **Finite-difference cancellation:** Lemma 12 makes the hypergeometric estimate self-contained by annihilating low-degree polynomial terms.
7. **High trace with alternating path circuits:** Propositions 14 and 18 bound operator norms through traces of $CC^*$ powers. Figure 3 depicts the resulting $2m$-path circuit.
8. **Canonical path encoding:** excess edges $g=a-s+1$, short and long cycling marks, and isomorphism classes organize the sums. Figure 4 explains why repeated returns around one cycle need not generate many independent marks.
9. **Base-graph path growth for lifts:** Lemma 31 replaces regular-tree branching by $\|(B^*)^s\delta_e\|_1\leq c_\rho\rho^s$.

## 5. What mastery should let the user explain

- Why a naive expected trace of $A^k$ fails at the exponents relevant to Friedman's theorem.
- Why the threshold is $\sqrt{d-1}$ for non-backtracking eigenvalues and $2\sqrt{d-1}$ for adjacency eigenvalues.
- Why $B$ cannot be treated as a symmetric matrix, and how Lemma 3 circumvents this.
- The precise order of operations: restrict to tangle-free paths, then center, introduce $R_k^{(\ell)}$, and only afterward use the orthogonality of $\chi$.
- Why Figure 2 makes the remainder terms unavoidable.
- How Proposition 11 turns consistent unique edges into extra negative powers of $dn$.
- How Figure 4 compresses arbitrarily many superfluous returns into a short-cycle mark.
- Why $m\asymp\log n/\log\log n$ and $\ell\asymp\log n$ are compatible and useful.
- Why $\rho>\rho_1$ is used throughout the lift proof, then allowed to approach $\rho_1$ only at the end.
- How Figure 5 encodes a lift, and why inherited base eigenvalues must be removed before discussing new ones.
- Which claims are asymptotic upper bounds, which are quantitative, and which adjacency questions remain outside the theorem's scope.
