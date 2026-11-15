# Prerequisites

The labels below indicate likely fluency needs, not assumptions about the user. No background level was supplied.

## 1. Spectral graph theory

- **Concept:** Adjacency spectrum, Rayleigh quotients, variational characterization of $\lambda_2$.
- **Why here:** The target is an adjacency eigenvalue bound, while tangles are converted into vertex test functions.
- **Minimum:** A real symmetric $n\times n$ adjacency matrix has real eigenvalues. For a connected $d$-regular graph, the constant vector gives $\lambda_1=d$. A two-dimensional subspace with Rayleigh quotient at least $\rho$ everywhere forces $\lambda_2\geq\rho$.
- **Used in:** Section 1, Lemma 2.9, Theorems 2.10 and 2.11, Theorem 4.2, Section 12.
- **Likely known:** Yes, if comfortable with basic spectral graph theory.
- **Refresh:** Review the Courant-Fischer min-max formulas and the Perron eigenvector of a nonnegative regular adjacency matrix.

## 2. Non-backtracking walks and Chebyshev recurrences

- **Concept:** Irreducible walks, $G_{\mathrm{Irred}}$, strongly irreducible closed walks.
- **Why here:** Tree growth is governed by $d-1$ forward choices rather than $d$.
- **Minimum:** An irreducible walk never immediately reverses an edge. A strongly irreducible closed walk also does not reverse its first edge on its last step.
- **Used in:** Lemmas 2.3 and 2.4, Section 3.6, Sections 10 and 11.
- **Likely known:** Perhaps only informally. This is essential to learn precisely.
- **Refresh:** Derive $A_1=A$, $A_2=A^2-dI$, and $A_k=AA_{k-1}-(d-1)A_{k-2}$ before tackling the spectral formulas.

## 3. The infinite regular tree

- **Concept:** Spectral norm $2\sqrt{d-1}$ of the $d$-regular tree and radial test functions.
- **Why here:** This norm is exactly the Ramanujan barrier.
- **Minimum:** Understand the Cauchy-Schwarz estimate in Sublemma 2.5 and the exponential decay $f(v)=(d-1)^{-\operatorname{dist}(v,v_0)/2}$ used to approximate its action.
- **Used in:** Section 2, Figure 1, Theorem 3.13.
- **Likely known:** Perhaps not the operator-norm proof.
- **Refresh:** Work through the children-of-a-root decomposition on pages 11 and 12.

## 4. Trace method in random matrix and random graph theory

- **Concept:** $\operatorname{Tr}(A^k)=\sum_i\lambda_i^k$ equals the number of closed length-$k$ walks.
- **Why here:** A large eigenvalue causes exponential trace growth, while independence permits expected walk counts.
- **Minimum:** Understand why even powers avoid cancellation and why $k$ is ultimately chosen proportional to $\log n$.
- **Used in:** Sections 2, 5, 8 through 13.
- **Likely known:** Yes at a basic level.
- **Refresh:** Compute $\operatorname{Tr}(A^2)=nd$ for a $d$-regular graph and relate this to immediate reversals.

## 5. Asymptotic notation and probabilistic estimates

- **Concept:** $O$, $o$, expectations of indicators, inclusion-exclusion, factorial asymptotics, and geometric tails.
- **Why here:** Every expansion coefficient and failure probability depends on these manipulations.
- **Minimum:** $n!/(n-a)!=n^a(1+O(1/n))$ for fixed $a$, and $\Pr(\cup_iE_i)\geq\sum_i\Pr(E_i)-\frac12\sum_{i\neq j}\Pr(E_i\cap E_j)$.
- **Used in:** Theorems 2.10, 4.7, 5.5, 5.9, 12.3, and 13.
- **Likely known:** Yes.
- **Refresh:** Review how expectation counts occurrences even when the event of at least one occurrence needs inclusion-exclusion.

## 6. Permutations and matching models

- **Concept:** Uniform permutations, $n$-cycles, perfect matchings, near-perfect matchings, involutions, independent products.
- **Why here:** Model-specific factorial denominators produce different expansion polynomials and tangle feasibility.
- **Minimum:** Count $(n-1)!$ Hamiltonian cycles as permutations and $(n-1)!!$ perfect matchings for even $n$.
- **Used in:** Section 1, Sections 4 and 6, Sections 12 and 14.
- **Likely known:** Yes for permutations, perhaps not for odd factorials.
- **Refresh:** Compare $(n-a)!/n!$ with $(n-2a)!!/n!!$ for fixed $a$.

## 7. Graph morphisms, pruning, and contraction

- **Concept:** Label-preserving inclusion, automorphism, pruning, order $|E|-|V|$.
- **Why here:** Probability scales with order, and supercritical tangles are reduced to pruned representatives.
- **Minimum:** A connected unicyclic graph has order 0. A tree has order -1. Pruning preserves order. A whole-loop and a half-loop each count as one edge in the paper's convention.
- **Used in:** Sections 3 through 6 and 9.
- **Likely known:** Partly, with nonstandard loop conventions requiring care.
- **Refresh:** Read Definitions 4.1 through 4.6 and test them on one vertex with $m$ loops.

## 8. Variable-length graphs and realization

- **Concept:** Positive integer edge lengths, subdivision, suppression of degree-two vertices, realization onto a retained vertex set.
- **Why here:** Types are compressed variable-length objects whose Perron growth controls walk sums.
- **Minimum:** Suppressing a bead replaces a path by one edge whose length is the number of original edges. Realization can introduce infinitely many weighted walks or edges.
- **Used in:** Sections 3, 5, 6, and 9.
- **Likely known:** Not assumed. This is paper-specific terminology.
- **Refresh:** Read Definitions 3.2 through 3.4 together with Figure 2.

## 9. Perron-Frobenius theory and generating functions

- **Concept:** Perron value, radii of convergence, walk generating functions, majorants.
- **Why here:** Growth rates below $\sqrt{d-1}$ become convergence at some $z_0>(d-1)^{-1/2}$, which yields exponential coefficient bounds.
- **Minimum:** For nonnegative matrices, $\lambda_1$ controls walk growth. For a nonnegative series with majorant $g$ finite at $z_0$, $[z^k]f\leq g(z_0)z_0^{-k}$.
- **Used in:** Theorems 3.5, 3.6, 3.13, and 6.6.
- **Likely known:** Perron-Frobenius perhaps, VLG extensions probably not.
- **Refresh:** Read Sections 3.3 and 3.4, focusing on convergence rather than matrix diagonalization.

## 10. Ihara-Bass determinant relation

- **Concept:** $\det(I-yA+y^2(D-I))$ and the non-backtracking spectrum.
- **Why here:** It converts the local growth $\lambda_{\mathrm{Irred}}(\psi)$ into the adjacency norm of $\operatorname{Tree}_d(\psi)$ and later converts adjacency eigenvalues into $\mu_{1,2}(\lambda)$.
- **Minimum:** Recognize the quadratic $\mu^2-\lambda\mu+(d-1)=0$ and the additional $\pm1$ spectrum in the full Hashimoto matrix.
- **Used in:** Theorem 3.13 and Section 10.
- **Likely known:** Often not. Treat it as a cited input on first reading.
- **Refresh:** Derive the quadratic from $\det(I-\mu^{-1}A+\mu^{-2}(d-1)I)=0$ after specializing to $d$-regular graphs.

## 11. Generating function coefficient norms and finite differences

- **Concept:** Coefficient norm of a polynomial, shift $\sigma_k$, annihilation of polynomials, binomial-weight recovery.
- **Why here:** These let the proof estimate infinite convolution tails without knowing expansion coefficients.
- **Minimum:** $(\sigma_k-1)p(k)$ lowers polynomial degree by one, and $(\sigma_k-1)^s(1-\theta)^k=(-\theta)^s(1-\theta)^k$.
- **Used in:** Lemmas 8.8 and 11.1, Sublemma 11.2.
- **Likely known:** Basic finite differences perhaps, coefficient norm perhaps not.
- **Refresh:** Compute the first three finite differences of $k^2$ and of $x^k$.

## 12. Möbius inversion on a finite poset

- **Concept:** Solve $\sum_{\Omega\leq\Omega'}N(\Omega,\Omega')\mu_\Omega=1$ recursively.
- **Why here:** Expected inclusion counts are not the same as the probability that at least one tangle occurs.
- **Minimum:** Diagonal counts $N(\Omega,\Omega)$ are positive automorphism counts, and the inclusion relation has finite lower cones.
- **Used in:** Proposition 9.5 and Theorem 9.3.
- **Likely known:** Optional at first. The formula can be checked by substitution.
- **Refresh:** Try one inclusion minimal tangle $\Omega$, for which $\mu_\Omega=1/N(\Omega,\Omega)$.

## 13. Expansion and contiguity

- **Concept:** Magnifier, spreader, spectral separation, domination and contiguity of sequences of probability measures.
- **Why here:** Magnification bounds every nontrivial eigenvalue away from $d$, and contiguity transfers vanishing bad events between models.
- **Minimum:** A $\gamma$-spreader satisfies $|\Gamma(A)|\geq(1+\gamma)|A|$ for $|A|\leq n/2$. Domination means $\mu_n(E_n)\to0$ implies $\nu_n(E_n)\to0$.
- **Used in:** Corollary 1.4 and Section 12.
- **Likely known:** Expansion yes, contiguity perhaps no.
- **Refresh:** Read pages 4 and 99. Contiguity does not automatically preserve explicit polynomial exponents.

## Suggested preparation order

If preparing efficiently, learn non-backtracking recurrences first, then Rayleigh quotients and tangle order, then factorial walk expansions. VLG generating functions and finite differences are the next essential layer. Contiguity and generalized Möbius inversion can be reviewed exactly when reached.
