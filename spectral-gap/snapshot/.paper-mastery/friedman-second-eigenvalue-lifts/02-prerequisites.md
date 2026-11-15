# Prerequisites

The user's background is unknown. This file assumes basic undergraduate linear algebra, probability, and graph theory. “Fluent” means needed throughout the paper. “Review on demand” means the relevant idea can be learned when it appears.

## 1. Finite graph spectra

- **Level:** Fluent.
- **Why it appears:** The main results concern eigenvalues of adjacency and non-backtracking matrices.
- **Minimum explanation:** A real symmetric $n\times n$ matrix $A$ has real eigenvalues and an orthonormal eigenbasis. For even $k$, $\operatorname{tr}(A^k)$ is the sum of $k$-th powers of its eigenvalues. The operator norm $\|C\|$ is the largest singular value of $C$, not necessarily its largest eigenvalue modulus when $C$ is not normal.
- **Used in:** Pages 1 to 4, Eq. 5, Lemma 3, and all trace estimates.
- **Quick refresh:** Diagonalize a symmetric $2\times2$ adjacency matrix, then compute the four eigenvalues of a directed non-backtracking matrix on a triangle. Check that singular-value and eigenvalue language differ for the latter.
- **Likely status:** Assumed known.

## 2. Regular graphs, adjacency matrices, and Alon-Boppana

- **Level:** Fluent at the definition level.
- **Why it appears:** The motivating threshold is $2\sqrt{d-1}$.
- **Minimum explanation:** A $d$-regular graph has adjacency eigenvalue $d$ with constant eigenvector. The quantities $\mu_2$ and $|\mu_n|$ control the two possible nontrivial extremes. A bipartite component gives eigenvalue $-d$.
- **Used in:** Theorem 1 and Ramanujan terminology on pages 1 and 2.
- **Quick refresh:** Compute the complete graph and cycle spectra at fixed small sizes. Read Eq. 1 as a lower bound that complements the theorem's asymptotic upper bound.
- **Likely status:** Assumed known.

## 3. Configuration model for random regular graphs

- **Level:** Review on demand.
- **Why it appears:** It permits explicit matching probabilities and, conditioned on simplicity, gives the uniform simple model.
- **Minimum explanation:** Start with $nd$ half-edges $(v,i)$ and choose a uniform fixed-point-free involution $\sigma$. Matched pairs form edges. The probability of a specified set of $a$ disjoint half-edge pairs is the reciprocal product of odd remaining pool sizes, of order $(dn)^{-a}$.
- **Used in:** Pages 5 and 6, Lemmas 9 and 12, and Proposition 11.
- **Quick refresh:** Derive $(M-1)!!$ matchings on $M$ even half-edges and the limiting $O(1/M)$ chance of one specified match.
- **Likely status:** Needs review if matchings and involutions are unfamiliar.

## 4. Non-backtracking walks and the Hashimoto matrix

- **Level:** Fluent by Section 2.3.
- **Why it appears:** Removing immediate reversals simplifies path counting and gives the sharp $\sqrt{d-1}$ scale.
- **Minimum explanation:** Directed edges $e$ and $f$ satisfy $B_{ef}=1$ when the endpoint of $e$ is the origin of $f$ but $f$ is not the reversal of $e$. $(B^\ell)_{ef}$ counts non-backtracking walks of length $\ell$. In the configuration model, $B=MN$, where $M$ performs the random matching and $N$ switches to another half-edge at the same vertex.
- **Used in:** Eq. 10 and every subsequent path argument.
- **Quick refresh:** Write out the $2\ell+1$ half-edge representation for $\ell=2$. Identify which odd-index transitions use $N$ and which even pairs use $M$.
- **Likely status:** The paper's representation needs careful reading even for experts.

## 5. Ihara-Bass and quadratic spectral correspondences

- **Level:** Review on demand. The formula is cited, not proved here.
- **Why it appears:** It transfers the non-backtracking estimate to adjacency eigenvalues.
- **Minimum explanation:** For $d$-regular graphs, nontrivial pairs satisfy $\lambda^2-\mu\lambda+(d-1)=0$. Outside $|\mu|<2\sqrt{d-1}$, this produces real $\lambda$ with modulus above $\sqrt{d-1}$.
- **Used in:** Pages 6 and 32, plus the derivation of Eq. 2.
- **Quick refresh:** Solve $\mu=\lambda+(d-1)/\lambda$ and differentiate the discriminant $\mu^2-4(d-1)$.
- **Likely status:** Can be learned in place.

## 6. Cycle rank and local graph neighborhoods

- **Level:** Fluent.
- **Why it appears:** Tangles, excess edges, canonical encodings, and the final summations all use cycle rank.
- **Minimum explanation:** For a connected graph with $s$ vertices and $a$ distinct edges, $g=a-s+1$ is the number of independent cycles. A spanning tree has $s-1$ edges, so $g$ counts distinct edges outside one. A tangle-free graph has at most one cycle, allowing loops and parallel edges as cycles.
- **Used in:** Definition 5, Lemma 9, and Lemmas 15 through 21.
- **Quick refresh:** Check $g$ for a tree, a simple cycle, a figure eight, and two cycles connected by a path.
- **Likely status:** Assumed known.

## 7. Conditional expectation and sequential matching exposure

- **Level:** Fluent.
- **Why it appears:** Local collisions and centered products are estimated by revealing only part of the random matching or permutation.
- **Minimum explanation:** If each successive collision has conditional probability at most $q$, then the chance of two collisions among $T$ trials is at most $\binom{T}{2}q^2\leq T^2q^2$. More generally, tower conditioning allows factors to be bounded one at a time under the complementary filtrations used in Lemma 13.
- **Used in:** Lemma 9, Lemma 13, and Propositions 11 and 28.
- **Quick refresh:** Prove the two-collision bound without claiming independence of the individual collision events.
- **Likely status:** Assumed known, but the exact filtrations require attention.

## 8. Markov's inequality and high moments

- **Level:** Fluent.
- **Why it appears:** High-probability norm bounds come from expected $2m$-moments.
- **Minimum explanation:** For nonnegative $X$, $\mathbb P(X\geq t)\leq t^{-1}\mathbb E X$. Applied to $\|C\|^{2m}$, a very large $m$ converts polylogarithmic losses per root into controlled tail probabilities.
- **Used in:** Eqs. 43 and 48, Propositions 14, 18, 29, and 33.
- **Quick refresh:** Derive Eq. 43 from Eq. 42 and check where the exponent $1/(2m)$ comes from.
- **Likely status:** Assumed known.

## 9. Trace versus norm

- **Level:** Fluent.
- **Why it appears:** Countable closed paths become available after using $CC^*$.
- **Minimum explanation:** For real square $C$, $CC^*$ is symmetric positive semidefinite. Thus $\|C\|^{2m}=\|CC^*\|^m=\lambda_{\max}(CC^*)^m\leq\operatorname{tr}((CC^*)^m)$.
- **Used in:** Eq. 35 and its lift analogue.
- **Quick refresh:** Test the inequality on a nonnormal $2\times2$ matrix and write its trace expansion with alternating $C$ and $C^*$ factors.
- **Likely status:** Assumed known.

## 10. Pochhammer symbols and finite differences

- **Level:** Review on demand.
- **Why it appears:** Exact matching counts and the self-contained proof of Lemma 12 use them.
- **Minimum explanation:** $(n)_k=n(n-1)\cdots(n-k+1)$. For every polynomial $P$ of degree at most $k-1$,

$$
\sum_{t=0}^{k}\binom{k}{t}(-1)^tP(t)=0.
$$

This follows by differentiating $(1+x)^k$ at $x=-1$ and using the falling-factorial basis.
- **Used in:** Eqs. 24 through 27 and the proof of Proposition 11.
- **Quick refresh:** Verify the identity for $P(t)=1,t,t^2$ with $k=3$.
- **Likely status:** Standard identity, but its use in Lemma 12 is one of the paper's hardest steps.

## 11. Perron theory and Gelfand's formula

- **Level:** Review on demand for the lift half.
- **Why it appears:** The base graph is no longer regular, so a single branching factor is insufficient.
- **Minimum explanation:** For the irreducible nonnegative base matrix $B$, $\rho_1$ is its Perron eigenvalue and spectral radius. Gelfand growth in any fixed vector norm gives, for each $\rho>\rho_1$, a finite $c_\rho$ such that $\|(B^*)^k\delta_e\|_1\leq c_\rho\rho^k$ uniformly over the finitely many base half-edges $e$.
- **Used in:** Pages 30 and 31, Eq. 67, and Lemma 31.
- **Quick refresh:** Distinguish the true asymptotic rate $\rho_1$ from the strict upper surrogate $\rho$ used to obtain a uniform geometric bound.
- **Likely status:** Can be learned in place.

## 12. Graph lifts and tensor products

- **Level:** Review on demand before Section 3.
- **Why it appears:** The second main theorem concerns new eigenvalues on fibers over a fixed base graph.
- **Minimum explanation:** Each base vertex and directed edge receives $n$ copies. A permutation $\sigma_e$ reconnects copies of a directed edge, with $\sigma_{\iota(e)}=\sigma_e^{-1}$. Vectors constant on each directed-edge fiber form $H$, which carries the inherited base spectrum. New eigenvalues live on $H^\perp$.
- **Used in:** Definition 22, Eqs. 50 through 56, and Theorem 23.
- **Quick refresh:** Verify every edge and loop in Figure 5 from $\sigma_a=(1\,2\,3)$ and $\sigma_c=(1)(2\,3)$.
- **Likely status:** The figure makes this concrete and should be studied with Definition 22.
