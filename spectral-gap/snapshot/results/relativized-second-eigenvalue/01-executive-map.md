# Executive map

**Labels.** Statements about the source are marked **Paper**. Consequences worked out here are **Derived**. Expository judgments are **Interpretation**.

## 1. What problem does the paper solve, and why does it matter?

**Paper.** Fix a finite $d$-regular graph $B$ with $d\ge 3$ and take a random degree-$n$ covering graph $G\to B$ in the Broder-Shamir permutation model $\mathcal C_n(B)$. Adjacency eigenfunctions on $G$ split into old functions, pulled back from $B$, and new functions, which sum to zero on every fibre. The problem is to control $\rho_B^{\mathrm{new}}(A_G)$, the largest absolute value among the new adjacency eigenvalues (Sections 0.1 and 1.1.3).

**Paper.** The desired threshold is $2\sqrt{d-1}$, the spectral radius of the adjacency operator on the infinite $d$-regular tree. This is the optimal asymptotic threshold for a $d$-regular base. Unlike a claim about individual degree-two covers, this concerns high-degree random covers and holds with probability tending to one.

**Interpretation.** The question asks whether the new directions introduced by lifting look locally tree-like spectrally, once the deterministic base directions are removed. An $O(n^{-1})$ exceptional probability is much stronger than merely proving convergence to zero, and the Ramanujan-base refinement identifies the leading combinatorial obstruction to spectral optimality.

## 2. Main contribution

### Simplest honest form

**Paper, Theorem 0.1.1, printed page 3.** For every fixed $\varepsilon>0$ there is a constant $C_{B,\varepsilon}$ such that

$$
\Pr_{G\in\mathcal C_n(B)}\!\left[\rho_B^{\mathrm{new}}(A_G)
\ge 2\sqrt{d-1}+\varepsilon\right]
\le C_{B,\varepsilon}n^{-1}.
$$

This applies to every $d$-regular base graph with $d\ge 3$, including graphs with multiple edges and, after Section 3.4, half-loops.

### Strongest form

**Paper, Theorem 0.1.3, printed page 4.** If $B$ is Ramanujan, there is a computable fundamental order $\eta_{\mathrm{fund}}(B)$ and a small $\varepsilon_0(B)>0$ such that the exceptional event has probability $C_1n^{-\eta_{\mathrm{fund}}(B)}$ from below at $\varepsilon_0$, and probability at most $C_2(\varepsilon)n^{-\eta_{\mathrm{fund}}(B)}$ for $0<\varepsilon<\varepsilon_0$. This is a two-sided order-of-magnitude statement, not an assertion that a normalized probability has a limit.

**Paper, Definition 2.4.8 and Section 3.3.** The exponent is intended to be the least order of a strict feasible tangle,

$$
\eta_{\mathrm{fund}}(B)
=\min\left\{\operatorname{ord}(L):
\rho(H_L)>\rho(H_B)^{1/2}\right\},
$$

where $L$ ranges over connected feasible $B$-graphs and $\operatorname{ord}(L)=-\chi(L)$. Minimal tangles are the rare finite subgraphs that force exceptional spectral behaviour.

**Source caution, Derived.** The additional universal inequality in Theorem 3.3.4, $\eta_{\mathrm{fund}}(B)>\sqrt{d-1}$, is not consistent with the paper's own definitions and bouquet example. It should not be repeated as a verified fact. See `09-assumptions-and-weak-points.md`.

### General spectral formulation

**Paper, Theorem 0.2.6, printed page 10.** For connected $B$ of negative Euler characteristic, if $\tau_0^2\ge\rho(H_B)$ and every non-real Hashimoto eigenvalue of every relevant cover has modulus at most $\tau_0$, then the probability of a new Hashimoto eigenvalue with modulus at least $\tau_0+\varepsilon$ is $O_\varepsilon(n^{-1})$. The regular theorem follows because every non-real Hashimoto root has modulus $\sqrt{d-1}$.

## 3. What the argument assumes

- **Paper:** $B$ is finite. Chapter 0 works with $d\ge3$ and the main core assumes a connected graph of negative Euler characteristic.
- **Paper:** $n$ tends to infinity while $B$, $d$, $\varepsilon$, and each chosen expansion order $r$ are fixed.
- **Paper:** The random model is $\mathcal C_n(B)$ or one of the algebraic variants described in Section 3.4. Non-half-loop edges receive independent uniform permutations, subject to inverse pairing. Half-loops receive appropriate random involutions.
- **Paper:** Chapter 2 first removes half-loops, then Section 3.4 explains the double-factorial and fixed-point modifications needed to restore them.
- **Paper:** Eigenvalues outside the critical disk must be real in the side-stepping setup. For $d$-regular graphs this follows from the Ihara quadratic.
- **Paper:** The Ramanujan refinement additionally uses spreading estimates and excludes the old dominant $d-1$, together with $1-d$ in the bipartite case.
- **Derived:** The results do not automatically apply to every distribution on degree-$n$ covers. A contiguity transfer would need its own theorem, and probability exponents can change between models.

## 4. Main techniques

1. **Hashimoto trace:** Count strictly non-backtracking closed walks using $\operatorname{Tr}(H_G^k)$ rather than analyzing arbitrary backtracking adjacency walks directly (Sections 1.1.2 and 1.2.3).
2. **Permutation specializations:** For a potential walk with $a_e$ specified edges over $e$ and $b_v$ distinct labels over $v$, compute its total trajectory-weighted probability exactly using falling factorials (Proposition 2.3.8).
3. **Order and coincidence counting:** Each additional order unit costs a factor $n^{-1}$. Walks of order at least $r$ form the expansion remainder (Sections 1.3 and 2.3).
4. **Types and forms:** Compress degree-two paths into finite skeletal data while retaining variable path lengths and base labels. There are only finitely many types below a fixed order (Sections 2.1.1 and 2.3.4).
5. **$B$-Ramanujan functions:** Allow polyexponential terms in the eigenvalues of $H_B$ plus errors smaller than roughly $\rho(H_B)^{k/2}$ up to an arbitrarily small exponential loss (Definition 1.3.6 and Section 2.2).
6. **Certified trace:** Admit a walk only if its traced graph is non-tangling and its order lies below the cutoff. This is the central new simplification (Definitions 1.4.1 and 2.4.25 through 2.4.27).
7. **Finite cone decomposition:** Monotonicity under lengthening beaded paths makes certificate vectors an upper set. The product order has finitely many minimal certificates, so inclusion-exclusion leaves finitely many cone sums (Section 2.4.3).
8. **Short and long multiplicities:** Split each certified sum by edge multiplicities at a fixed threshold $M$. Long multiplicities suppress extra Hashimoto growth, while short ones leave finitely many convolution cases (Section 2.4.5).
9. **Generalized types with tangles:** Expand both certified traces with and without tangle indicators, subtract them, and replace the certified trace by the actual trace on tangle-free graphs (Sections 2.5 and 2.7).
10. **Side-stepping:** Apply polynomials in the shift operator $S f(k)=f(k+1)$ to annihilate unknown polyexponential coefficients, localize exceptional eigenvalues, and read probability exponents from vanishing coefficients (Section 2.6).
11. **Spreading:** Rule out eigenvalues near $d-1$ and, in the bipartite case, near $1-d$ with the required probability. This is essential for the Ramanujan exponent (Section 3.2).

## 5. What mastery should let the user explain

After mastering this paper, the user should be able to:

- Define old and new spectra without inserting an erroneous factor of $n$ into $\operatorname{Tr}(A_G^k)-\operatorname{Tr}(A_B^k)$.
- Derive $\mu^2-\lambda\mu+(d-1)=0$ from Ihara's formula and explain why the critical Hashimoto modulus is $\sqrt{d-1}$.
- Reproduce Proposition 2.3.8 and obtain the exponent $n^{-\operatorname{ord}(\psi)}$ for subgraph occurrences.
- Explain why types are finite but forms have variable beaded-path lengths.
- State what a certified trace excludes and why those exclusions make the coefficient sums tractable.
- Prove that non-tangle certificate vectors form an upper set and invoke finite generation to obtain finitely many cone sums.
- Explain the role of both short and long multiplicities in the coefficient estimate.
- Perform a shift-operator calculation $Q(S)\mu^k=Q(\mu)\mu^k$ and show how $Q$ annihilates known bases.
- Distinguish a tangle-free expectation from a conditional expectation.
- Explain the separate role of spreading in the Ramanujan-base two-sided exponent.
- Identify the source's notation defects and avoid silently converting repaired statements into literal quotations.
- Explain why there is no missing figure analysis: the paper has no substantive numbered visuals, while its structured equation and index layouts have been directly inspected.

## One-paragraph proof map

**Derived.** Start with the exact factorial probability of a potential walk. Its leading power is $n^\chi$, so a fixed shape of order $s=-\chi$ supplies its first possible contribution at $n^{-s}$. Finite types compress degree-two paths and produce a general $1/n$ expansion. Raw trace coefficients need not be $B$-Ramanujan at high order, so replace the raw trace by a certified trace. Certificate vectors obey a componentwise upper-set condition, whose finite cone decomposition reduces coefficients to tractable polyexponential-convolution sums. Repeat the machinery with fixed tangle subgraphs and subtract to obtain the tangle-free true trace. Subtraction of the old trace kills the leading coefficient at the bases of $H_B$. Side-stepping then converts the first possible nonzero coefficient at level $j$ into an $O(n^{-j})$ spectral exception bound. For the general theorem, level zero vanishes and $j=1$. For Ramanujan bases, spreading removes dominant-base distractions and tangle occurrence asymptotics identify the precise fundamental exponent.
