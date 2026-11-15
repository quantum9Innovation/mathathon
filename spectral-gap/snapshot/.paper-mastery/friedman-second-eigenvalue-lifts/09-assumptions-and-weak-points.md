# Assumptions, limitations, and weak points

This file separates structural assumptions from proof limitations and local source defects. A typographical problem is not automatically a mathematical gap. Conversely, a plausible typographical repair is not a substitute for checking the surrounding argument.

## A. Structural assumptions

### 1. Fixed degree $d\geq3$ and $nd$ even

- **Where:** Theorems 1 and 2 and the entire configuration model.
- **Why needed:** The matching exists only when $nd$ is even. The Perron and Ihara-Bass formulas use fixed regularity. Constants and the positive limiting simplicity probability depend on $d$.
- **Essential or technical:** $nd$ even is combinatorially necessary. Fixed $d$ is essential to the stated estimates as proved, though the core path-decomposition idea could be analyzed in other asymptotic regimes separately.
- **What breaks without it:** Constants need not be uniform, simplicity can become too rare, and the final logarithmic rates need rederivation.

### 2. Configuration model before uniform simple graphs

- **Where:** Eqs. 6 and 7 and Theorem 2.
- **Why needed:** Uniform perfect matchings make conditional product expectations tractable. Loops and multiple edges are therefore allowed in the workhorse model.
- **Essential or technical:** Technical route, backed by the uniform-conditioning property and a positive simplicity limit.
- **What breaks without it:** A vanishing simplicity probability would prevent transferring $o(1)$ or polynomial bad-event probabilities by a constant factor. New arguments would be required.

### 3. Local tangle-freeness

- **Where:** Definition 5, Lemma 9, Proposition 8, Lemma 27, and Proposition 26.
- **Why needed:** It gives the exact identity $B^\ell=B^{(\ell)}$, and per-strand tangle-freeness later controls cycle-encoding entropy.
- **Essential or technical:** Essential to this proof. It is also the reason for $\kappa<1/4$.
- **What breaks without it:** The deterministic decomposition no longer describes all of $B^\ell$ through only tangle-free paths, and the long-cycle estimates lose their main combinatorial control.

### 4. Short total path-length regimes

- **Where:** Proposition 11 requires $k\leq\sqrt{dn}$. Lemma 17 assumes $2\ell m\leq\sqrt{dn}$, while remainder and lift variants use comparable bounds such as $6\ell m\leq\sqrt n$.
- **Why needed:** Falling factorials must remain comparable with ordinary powers, conditional normalizers must be controlled, and Lemma 12's small-parameter hypotheses must hold.
- **Essential or technical:** Essential quantitative hypothesis for the estimates as stated.
- **What breaks without it:** Matching dependencies are no longer weak at the required scale and collision-tail series need not converge.
- **Check in this proof:** With $\ell\leq\log n$ and $m\asymp\log n/\log\log n$, $\ell m=O((\log n)^2)$, comfortably $o(\sqrt n)$.

### 5. Logarithmic block length and sublogarithmic moment order choices

- **Where:** $\ell\sim\kappa\log_{d-1}n$ and the explicit $m$ choices in Sections 2.5 and 4.3.
- **Why needed:** $\ell$ turns polylogarithmic norm losses into $1+O(\log\log n/\log n)$ roots. The $m$ choices make excess-support entropy divided by $n$ smaller than $1$ while keeping total length short.
- **Essential or technical:** Technical calibration, but crucial to closing the proof.
- **What breaks without it:** Too small $\ell$ leaves root errors. Too large $\ell$ increases tangles. Too large $m$ violates product-estimate hypotheses. Too small $m$ leaves an excessive $n^{1/(2m)}$ factor.

### 6. High-probability restrictions, not uniform deterministic norm bounds

- **Where:** Propositions 14, 18, 29, and 33.
- **Why needed:** The centered and remainder estimates are moment-derived and hold with high probability, not for every graph.
- **Essential or technical:** Essential interpretation issue.
- **What breaks without it:** Treating these as universal bounds would recapitulate the rare-subgraph obstruction. Theorem statements must retain their probabilistic qualifiers.

### 7. Random-lift model with independent uniform permutations

- **Where:** Definition 22 and Proposition 28.
- **Why needed:** Independence across undirected base edges factorizes the expectation. Fiberwise centering removes the base spectrum.
- **Essential or technical:** Essential for the distributional calculations.
- **What breaks without it:** General dependent permutations or nonuniform lifts require a new replacement for Proposition 28 and for tangle-probability estimates.

### 8. Connected finite base with $|E|>|V|$

- **Where:** Theorem 23.
- **Why needed:** It yields irreducibility and $\rho_1>1$ as invoked from the cited lift literature. It also implies maximum degree at least $3$, used in Lemma 27, and makes the universal cover nontrivial.
- **Essential or technical:** Essential to the stated Perron setup and growth scale.
- **What breaks without it:** Trees and unicyclic bases have different finite or periodic non-backtracking behavior and do not fit the claims about this $\rho_1>1$ regime.

### 9. Strict $\rho>\rho_1$ during lift estimates

- **Where:** Eq. 67 and Propositions 29 and 33.
- **Why needed:** Gelfand's formula supplies exponential bounds at every strictly larger rate with one finite constant valid over the finite base.
- **Essential or technical:** Technical device. The limit $\rho\downarrow\rho_1$ is taken only at the end.
- **What breaks without it:** Polynomial or transient factors at $\rho=\rho_1$ need more detailed invariant-subspace analysis, which the paper avoids.

### 10. Regularity for the adjacency corollary

- **Where:** Corollary 24.
- **Why needed:** The simple regular Ihara-Bass dictionary converts $\sqrt{d-1}$ to $2\sqrt{d-1}$.
- **Essential or technical:** Essential to this corollary's proof.
- **What breaks without it:** Theorem 23 remains a non-backtracking statement, but it does not by itself prove the irregular adjacency conjecture described on page 32.

## B. Cited inputs not proved in this paper

For a self-contained assessment, the following are imported facts:

1. The configuration model's positive limiting simplicity probability in Eq. 7, cited to Bollobás.
2. Ihara-Bass in Eq. 12, cited to Kotani-Sunada and Terras.
3. Irreducibility and $\rho_1>1$ under the lift base hypotheses, cited to Friedman-Kohler.
4. Identification of $\sqrt{\rho_1}$ with non-backtracking spectral radius on the universal cover, cited to Angel-Friedman-Hoory.
5. Standard contiguity used only when deducing Theorem 1 again from a bouquet-lift version of Corollary 24, not used by the main new proof of Theorem 1.

**Assessment:** The first four are transparent dependencies, not unexplained steps hidden inside the proof. Their statements were not independently reproved in this one-paper digest. The universal covering tree identification is motivation for the sharp $\sqrt{\rho_1}$ threshold, while Theorem 23 is proved directly at the matrix level.

## C. Honest scope limitations

### 1. Asymptotic upper bounds, not exact Ramanujan graphs

The main claims allow $o(1)$ error. They do not say that a uniformly random graph is exactly Ramanujan with high probability, nor do they construct a particular graph.

### 2. No general irregular adjacency-lift theorem

Theorem 23 covers the non-backtracking operator on a general admissible base. Corollary 24 covers adjacency only in the regular case. The broader adjacency conjecture stated on page 32 remains outside this paper's proof.

### 3. Unoptimized finite-$n$ information

Eqs. 2 and 13 provide useful rates for the regular problem, but constants depend on $d$ and the probability exponent $a$, and polylogarithmic exponents are generous. Theorem 23 has no comparably explicit quantitative statement in the paper. Lack of optimization is a limitation of quantitative usefulness, not a logical defect.

### 4. Numerical or experimental evidence is absent

This is a theoretical paper with five proof diagrams. There are no simulations, datasets, empirical plots, or implementation benchmarks. The diagrams clarify definitions and combinatorics but do not constitute numerical verification.

### 5. Dense conditional-probability and encoding arguments remain the hardest verification burden

Proposition 11, Lemma 12, and Lemma 16 are much more than routine bookkeeping. A future use of this proof should independently audit the filtration choices, the injectivity and reconstructibility of the marks, and the alternation of centered factors on reversed remainder strands. This digest expands their architecture and key steps but does not claim a line-by-line formal proof audit.

### 6. No claim about every possible choice of parameters

The propositions use fixed ranges for $\ell,m,k,\rho$, and $n$ sufficiently large. Reading them with arbitrary $m$, unbounded $d$, $\rho=\rho_1$, or path lengths beyond square-root scale would exceed the actual statements.

## D. Local source defects noticed during close reading

These examples come from both the official PDF and its LaTeX source. The list is representative, not an exhaustive errata project.

### 1. Remark 4 on page 29: inverted rate

- **Printed:** $\varepsilon=c\log n/\log\log n$.
- **Problem:** Eq. 13 requires a vanishing allowance $c\log\log n/\log n$, and the preceding $\ell$-th root gives precisely that scale.
- **Derived repair:** Use $\eta=c\log\log n/\log n$ with sufficiently large $c$. This then yields Eq. 2 through the quadratic conversion in D1 of `06-derivations.md`.
- **Assessment:** Clear local typographical error. Literally following the printed formula breaks convergence to zero.

### 2. Page 18: wrong sign in a final geometric-series exponent

- **Printed:** After estimating $\mathbb P(|T\setminus T^*|\geq x)\lesssim(2a/\sqrt m)^x$, the last display ends with $\sum_x(2/3)^{-x}=3c$.
- **Problem:** That displayed series diverges.
- **Derived repair:** With $\varepsilon=3a/\sqrt m$, the preceding terms are $\varepsilon^{-x}(2\varepsilon/3)^x=(2/3)^x$, whose sum is $3$.
- **Assessment:** Clear typographical error in the last expression. The preceding bound already gives the convergent argument.

### 3. Page 39, Proposition 28 proof: similar geometric-series and denominator defects

- **Printed:** The concluding display contains $\sum_x(1/3)^{-x}=3c/2$. Several nearby power denominators use $m$ after the section has set its permutation dimension to $n$.
- **Problem:** The printed series diverges, and $m$ is not the current matrix dimension.
- **Derived repair:** The preceding estimate gives $\varepsilon^{-x}(\varepsilon/3)^x=(1/3)^x$, summing to $3/2$, and the dimension is $n$.
- **Assessment:** Local propagation of earlier notation and exponent errors. The intended final Proposition 28 bound is consistent with Proposition 11.

### 4. Equations 45 and 76 and nearby remainder notation: factor parity and half-edge indices

- **Printed:** The text defining $M^{\varepsilon_i}$ says “if $i$ is odd” in both cases. Some second products omit the second half-edge subscript. The notation also risks suggesting one centered or uncentered type for all positions of a strand.
- **Problem:** Eq. 44 has centered weights before the cut and uncentered weights after it on the original strand. Reversal on an even trace strand exchanges prefix and suffix. Eqs. 45 and 76 must reproduce that alternation if read literally.
- **Derived reading:** Reconstruct the weight convention from Eq. 44, the definition of $k_i$, and the original $p_k(\gamma)$. Centered and uncentered types alternate with strand parity and cut side. Merely copying the displayed shorthand can produce the wrong product.
- **Assessment:** This is more than a cosmetic typography issue for reproducibility, although the architecture of Proposition 18 is clear and Proposition 11 is designed for mixed centered and uncentered products. A careful reader should flag this passage for independent formula verification rather than silently transcribe it.

### 5. Page 28, Lemma 21 proof: numerical upper-bound typo

- **Printed:** $|E_i|\leq8(g+p-1)+8m\leq4g+24m$ after $p\leq2m$.
- **Problem:** The middle expression implies an upper bound with $8g$, not $4g$, before constants are absorbed.
- **Assessment:** The erroneous coefficient can be absorbed into the constant $c$ in Lemma 21's final bound $c^{g+m}(dn)^{-a}$. The displayed intermediate inequality itself is not justified as printed.

### 6. Page 43: sign of a geometric prefactor

- **Printed:** A bound for the first partial sum includes $\rho/(1-\rho)$, while $\rho>1$.
- **Problem:** That expression is negative and cannot be the stated positive summation prefactor.
- **Derived repair:** Use $\rho/(\rho-1)$, which also appears correctly in the analogous remainder calculation on page 46.
- **Assessment:** Clear typographical sign error. The subsequent geometric argument is otherwise unchanged.

### 7. Page 47: final lift polylogarithm differs from Proposition 29

- **Printed:** The final assembly uses $(\log n)^{15}\rho^{\ell/2}$, while Proposition 29 states $(\log n)^{20}\rho^{\ell/2}$.
- **Assessment:** Using exponent 20 gives the same asymptotic conclusion. This is a constant-exponent inconsistency, not a gap in the limiting theorem, but it matters when tracking explicit bounds.

### 8. Figure 4 discussion on page 22: exit-time indexing tension

- **Printed:** The caption sets $\hat t=12$, corresponding to the exit $3\to5$. The definition refers to the first time $\gamma_{i,2\hat t-1}$ is not in $C_i$.
- **Problem:** In the printed sequence, $\gamma_{2\hat t-1}$ at $\hat t=12$ is $(3,2)$, which is part of the already visited triangle. The newly exiting half-edge pair ends with $(5,1)$.
- **Derived reading:** The intended condition appears to be about the first traversed edge leaving $C_i$ or its second half-edge, not the first half-edge as printed.
- **Assessment:** Local index ambiguity. It does not change the visual principle that one short-cycle mark handles repeated tours, but a formal encoding proof should resolve it explicitly.

### 9. Gelfand display on page 39: root-index mismatch

- **Printed:** The limit as $k\to\infty$ displays $\|(B^*)^k\delta_e\|_1^{1/\ell}$.
- **Problem:** Gelfand's formula for these fixed vector expressions requires the $k$-th root, not an $\ell$-th root independent of the limit variable.
- **Assessment:** Typographical error. The subsequent Eq. 67 uses the standard correct growth conclusion.

## E. Overall assessment

- **Mathematical contribution:** The paper presents a coherent proof architecture with a clear reason for every major ingredient. The sharp regular result follows from the interaction of tangle deletion, conditional matching cancellation, cycle-rank enumeration, and logarithmic root choices.
- **Presentation weakness:** Repeated formulas across the regular and lift sections contain several propagated notation and typographical errors, especially in remainder definitions and terminal one-line estimates. These increase the effort needed to check the argument.
- **Not established by this digest:** No complete formal verification, no exhaustive errata list, no independent proofs of cited external inputs, and no numerical checks. No fatal logical counterexample was found during the reading.
- **Strongest place to invest further scrutiny:** Reconstruct Eq. 45's mixed weights from first principles and verify Lemma 16's exact second encoding, including the exit-time convention illustrated by Figure 4.
