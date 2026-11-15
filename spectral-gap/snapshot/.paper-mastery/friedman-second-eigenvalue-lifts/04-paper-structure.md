# Paper structure and visual inventory

## Section-by-section map

### 1. Introduction, pages 1 and 2

- **Purpose:** Define nontrivial adjacency eigenvalues, Alon-Boppana, Ramanujan graphs, and Friedman's theorem.
- **Key material:** Theorem 1 and the probability-polynomial quantitative statement Eq. 2.
- **Dependencies:** Finite graph spectra and the configuration model introduced later.
- **Read carefully:** The difference between $\mu_2\vee|\mu_n|$ in Theorem 1 and $\mu=\max\{|\mu_i|:|\mu_i|<d\}$. On a connected graph these refer to the same nontrivial extremes, but the theorem's formula is explicit even when components exist.
- **Can skim:** Historical references on a first pass.

### 2.1. Overview of the proof, pages 3 through 5

- **Purpose:** Explain why a direct expected high-trace calculation fails and preview the workaround.
- **Key material:** Eqs. 3 and 4 as aspirational trace bounds, the complete-subgraph obstruction, Eq. 5 as the eventual norm-to-trace strategy.
- **Dependencies:** Spectral theorem, even-power traces, Markov's inequality.
- **Read carefully:** Rare events of probability $n^{-c}$ can dominate $d^k n^{-c}$ when $k\gg\log n$. The failure concerns expectation, not the desired high-probability statement.
- **Can skim:** The repeated roadmap after the logical distinction is clear.

### 2.2. Non-backtracking matrix of the configuration model, pages 5 and 6

- **Purpose:** Replace the uniform simple graph problem by Theorem 2 for the configuration model.
- **Key material:** Half-edges, matching involution, $B=MN$, Eq. 10, Perron eigenvector Eq. 11, Ihara-Bass Eq. 12, and Theorem 2.
- **Dependencies:** Uniformity after conditioning on simplicity and the positive limiting simplicity probability Eq. 7.
- **Read carefully:** $B$ is a matrix on $nd$ half-edges, and the irregular-looking ordering in Eq. 10 matches the paper's half-edge convention.
- **Can skim:** No part on a first technical pass, because all subsequent randomness uses this setup.

### 2.3. Path decomposition, pages 7 through 11

- **Purpose:** Derive a deterministic upper bound for $|\lambda_2|$ on $\ell$-tangle-free configurations.
- **Key material:** Lemma 3, Definitions 4 through 6, path matrices Eqs. 18 and 19, telescoping Lemma 7, remainder matrices Eq. 22, and Proposition 8.
- **Dependencies:** Non-backtracking products, rank-one projections, cycle rank.
- **Read carefully:** Deletion precedes centering. Figure 2 explains the strict inclusion $F^\ell\subset F_k^\ell$ and hence $R_k^{(\ell)}$.
- **Can skim:** The full verification of the matrix-product coefficient $(d-1)\underline B^{(k-1)}\chi\chi^*B^{(\ell-k)}$ only after doing one $k$ case by hand.

### 2.4. Computation on the configuration model, pages 11 through 19

- **Purpose:** Supply local tangle control and a sharp expectation bound for weighted path products.
- **Key material:** Lemma 9, consistency Definition 10, Proposition 11, hypergeometric Lemma 12, conditioning Lemma 13, and the sets $T,T^*,S$ used to prove Proposition 11.
- **Dependencies:** Sequential exposure, conditional expectation, Pochhammer symbols, finite differences.
- **Read carefully:** The extra $(3k/\sqrt{dn})^{a_1}$ factor in Proposition 11. It supplies cancellation beyond the generic $(dn)^{-a}$ matching cost.
- **Can skim:** Constant-chasing in Lemma 12 after understanding its polynomial-degree split into low and high $s$.

### 2.5.1. Operator norm of $\underline B^{(\ell)}$, pages 19 through 25

- **Purpose:** Prove Proposition 14, the centered norm bound of order $(d-1)^{\ell/2}$ up to polylogarithms.
- **Key material:** Trace expansion Eqs. 35 through 38, path circuit $W_{\ell,m}$, isomorphism Lemma 15, canonical class bound Lemma 16, expected contribution Lemma 17, and final sum Eq. 42.
- **Dependencies:** Proposition 11, cycle rank, high-moment Markov bounds.
- **Read carefully:** The product of three counts: labelings of an isomorphism class, number of canonical classes, and expected weight. Figure 3 explains $W_{\ell,m}$. Figure 4 explains the compression behind Lemma 16.
- **Can skim:** The three final regimes $S_1,S_2,S_3$ after checking their shared geometric ratios.

### 2.5.2. Operator norm of $R_k^{(\ell)}$, pages 25 through 29

- **Purpose:** Prove Proposition 18, the uncentered-scale bound on the total remainder.
- **Key material:** Alternating deletion positions $k_i$, modified support $G_\gamma^k$, and Lemmas 19 through 21.
- **Dependencies:** Same architecture as Section 2.5.1, with spanning forests replacing spanning trees.
- **Read carefully:** Every component of $G_\gamma^k$ has a cycle, giving $a\geq s$. This allows cancellation of all $n^s$ labeling powers without a global $n$ factor.
- **Can skim:** Repeated definitions after checking precisely what is deleted at position $k_i$.

### 2.6. Proof of Theorem 2, page 29

- **Purpose:** Choose $\ell$ and assemble tangle, centered, and remainder estimates.
- **Key material:** $0<\kappa<1/4$, $\ell\sim\kappa\log_{d-1}n$, the scalar $J$, and Remarks 1 through 4 for stronger probabilities.
- **Dependencies:** Lemma 9 and Propositions 8, 14, and 18.
- **Read carefully:** The $1/n$ in front of the remainder makes its nominal $(d-1)^\ell$ scale negligible. Remark 4 contains the reciprocal-rate typographical error discussed in the weak-points file.
- **Can skim:** Nothing. This is one page and closes the main argument.

### 3. New eigenvalues of random lifts, pages 30 through 32

- **Purpose:** Define abstract multigraphs, random lifts, and the new spectrum, then state Theorem 23 and Corollary 24.
- **Key material:** $B=SN$, Definition 22, $B_n=S_nN_n$, fiber-constant space $H$, and base path growth.
- **Dependencies:** Fiber permutations, tensor products, non-backtracking matrices.
- **Read carefully:** Eigenvalues inherited from the base are removed by restricting to $H^\perp$. Figure 5 makes the permutation convention unambiguous.
- **Can skim:** Discussion of related conjectures on a first proof-focused pass.

### 4.1. Lift path decomposition, pages 32 through 35

- **Purpose:** Adapt Lemma 3, tangle deletion, centering, and remainders to $H^\perp$.
- **Key material:** Definition 25, Eqs. 53 through 58, Proposition 26, fiberwise $\underline M_e=M_e-n^{-1}\chi\chi^*$.
- **Dependencies:** Sections 2.2 and 2.3, with new fiber notation.
- **Read carefully:** The term $(B\otimes\chi\chi^*)x$ vanishes for $x\in H^\perp$, replacing the regular proof's $\chi^*x=0$.
- **Can skim:** Algebraic steps identical to Section 2.3 after verifying one entry of $B_n^\ell$.

### 4.2. Computation on random lifts, pages 35 through 39

- **Purpose:** Prove local tangle-freeness and the permutation analogue of Proposition 11.
- **Key material:** Maximum degree $d$, Lemma 27, consistency, Proposition 28, reduction to one base edge and its single random permutation.
- **Dependencies:** Conditional expectation and Lemma 12.
- **Read carefully:** Independence across undirected base edges permits factorization before solving the one-permutation problem.
- **Can skim:** Conditional bounds that exactly parallel Proposition 11, while noting the dimension changes from $dn$ to $n$.

### 4.3.1. Operator norm of the centered lift matrix, pages 39 through 44

- **Purpose:** Prove Proposition 29 with scale $\rho^{\ell/2}$ for every fixed $\rho>\rho_1$.
- **Key material:** Gelfand bound Eq. 67, fiber-only isomorphism Lemma 30, base-path encoding Lemma 31, and mean-path Lemma 32.
- **Dependencies:** Perron and Gelfand growth, the regular trace architecture.
- **Read carefully:** The product of new-vertex path counts has total $\rho^{s-1}$ by Eq. 72. This replaces the regular branching calculation and is the main new combinatorial ingredient for lifts.
- **Can skim:** Final geometric sums once $d-1$ has been mentally replaced by $\rho$.

### 4.3.2. Operator norm of lift remainders, pages 44 through 47

- **Purpose:** Prove Proposition 33.
- **Key material:** Lemmas 34 through 36 and moment choice Eq. 77.
- **Dependencies:** Sections 2.5.2 and 4.3.1.
- **Read carefully:** Base-path marks again contribute $\rho^{s-1}$, while the $k_i$-omitted support retains each component's cycle.
- **Can skim:** Most of the repeated remainder encoding after the changes are clear.

### 4.4. Proof of Theorem 23, page 47

- **Purpose:** Choose $\rho$ close to $\rho_1$, choose $\ell$, and close the lift proof.
- **Key material:** $\sqrt\rho\leq\sqrt{\rho_1}+\varepsilon$, $\ell\sim\kappa\log_{d-1}n$, and the same negligible remainder mechanism.
- **Dependencies:** Lemma 27 and Propositions 26, 29, and 33.
- **Read carefully:** The final PDF prints $(\log n)^{15}$ in the assembly even though Proposition 29 has exponent 20. Any fixed polylogarithmic exponent supports the conclusion, so this changes no asymptotic result but should be noticed when tracking constants.

### References and address, pages 47 through 49

- **Purpose:** Bibliographic inputs.
- **Use in this digest:** Identify which major statements are cited rather than proved here, notably configuration simplicity, Ihara-Bass, and universal covering tree spectral radius.

## Complete visual inventory

There are five figures and no data tables, experimental plots, axes, or charts. All five were inspected directly from the rendered PDF, not reconstructed only from LaTeX.

### Figure 1, page 8: visited support of a non-backtracking path

[Rendered page 8](visuals/page-8.png)

- **What it encodes:** The sequence below the graph alternates half-edge incidences and matched pairs. Circled numbers $1$ through $5$ are vertices. Small numbers near the cyan lines are local half-edge labels. For example, $(1,1)(1,2)$ is a loop at vertex $1$, while $(3,2)(4,1)$ and $(4,2)(3,3)$ produce the two parallel edges between $3$ and $4$.
- **How to read it:** The cyan graph is the **distinct visited support** $G_\gamma$, not a step-by-step animation. Repeated traversals are collapsed in $E_\gamma$. The full sequence underneath is needed to recover order and multiplicity.
- **Main pattern:** The support contains a loop, a double edge, and a cycle through $2,3,4,5$. Thus it has more than one independent cycle and is tangled under Definition 5.
- **Claim supported:** It makes Definitions 4 and 10 concrete. It also illustrates inconsistency: $(1,1)$ participates in two distinct visited pairs, and $(4,2)$ participates in three. Such half-edges spoil the condition $m_\gamma(e)=m_\gamma(f)=m_\gamma(\{e,f\})$.
- **Visual ambiguity:** The support alone does not reveal which edges were repeated or which centered product receives extra cancellation. The caption and full sequence are required.
- **Dossier connection:** See Derivation D3 and the expectation mechanism in D5 of `06-derivations.md`.

### Figure 2, page 10: locally tangle-free pieces can form a tangle

[Rendered page 10](visuals/page-10.png)

- **What it encodes:** Three schematic ways to splice a prefix $\gamma'$, a short middle $\gamma''$, and a suffix $\gamma'''$. Orange marks the earlier tangle-free piece, cyan the later piece, and black the small joining segment around $\gamma_{2k-1},\gamma_{2k},\gamma_{2k+1}$.
- **How to read it:** A loop-shaped arc stands for a unicyclic walk or support, not necessarily one graph-theoretic loop. In the left picture, orange and cyan each have their own cycle. Joining them creates a support with two cycles. The other panels move one cycle into the joining structure or share a junction, with the same global conclusion.
- **Main pattern:** Every separate piece can have at most one cycle while their union has two.
- **Claim supported:** $F_k^\ell$ strictly enlarges $F^\ell$. The matrix-product term obtained by factoring the three pieces therefore overcounts. The overcount is exactly the source of $R_k^{(\ell)}$ in Eq. 22.
- **Visual ambiguity:** These are topological cartoons of cases, not a complete classification drawing. The proof only needs the inclusion and its consequences, not an exhaustive three-case theorem.
- **Dossier connection:** This figure is essential to Derivation D3 and to the definition of $W_{\ell,m}^k$ in the remainder count.

### Figure 3, page 20: alternating path circuit in $W_{\ell,m}$

[Rendered page 20](visuals/page-20.png)

- **What it encodes:** Twelve curved, directed cyan strands $\gamma_1,\ldots,\gamma_{12}$ forming a closed alternating circuit, the case $m=6$ of $W_{\ell,m}$. Arrows alternate around junctions. Labels identify endpoint or origin equalities from Eq. 37.
- **How to read it:** Each strand is an entire length-$\ell$ non-backtracking tangle-free path, not one graph edge. Odd and even strand pairs arise from $\underline B^{(\ell)}$ and its transpose. Even strands are reversed to make the product chain readable.
- **Main pattern:** The boundary identifications make the union connected and closed. At joins, the last endpoints of odd strands agree with those of their successor even strands, while the next odd strand starts from the preceding even strand's terminal half-edge. The $q(\gamma)$ factor counts the now-summed final half-edges at the $m$ odd-even joins.
- **Claim supported:** It explains the combinatorial support of $\operatorname{tr}((CC^*)^m)$ and why Lemmas 15 through 17 can parametrize circuits by $s=|V_\gamma|$, $a=|E_\gamma|$, and $g=a-s+1$.
- **Visual ambiguity:** The near-hexagonal layout has no metric or geometric meaning. Apparent interior junctions matter only where the text identifies half-edges or vertices. Unlabeled crossings or shapes should not be promoted to graph incidences.
- **Dossier connection:** Derivation D7 expands the corresponding trace norm.

### Figure 4, page 22: canonical path, first-return encoding, and spanning tree

[Rendered page 22](visuals/page-22.png)

- **What it encodes:** On the left, a path visits $1\to2\to3\to4\to2$, then repeats parts of the triangle $2,3,4$, and finally visits $5$. Small edge labels list traversal times. On the right, the spanning tree has edges $1-2$, $2-3$, $3-4$, and $3-5$, omitting the excess edge $4-2$.
- **How to read it:** First times $1,2,3,12$ discover new vertices and build the tree. Time $4$ first closes the unique cycle and is the short cycling time. Times $7$ and $10$ traverse that excess edge again but are called superfluous. The written half-edge sequence below is authoritative for reconstructing the route.
- **Main pattern:** A single excess edge can be visited many times. Naively storing a mark at every important time loses control of the count. Tangle-freeness says all these repetitions concern the same unique cycle, so one enhanced short-cycle mark captures them. Only other cycles require long-cycle marks, whose number is bounded using $g$.
- **Claim supported:** Lemma 16's bound $(4\ell m)^{6mg+6m}$ on canonical classes. Without compressing superfluous times, the exponent would grow with unbounded path length rather than cycle rank.
- **Visual ambiguity and source issue:** The caption sets $\hat t=12$, the exit $3\to5$. The displayed definition just below refers to $\gamma_{i,2\hat t-1}$ not lying in $C_i$. At $\hat t=12$, that first half-edge is $(3,2)$, which belongs to the already visited triangle. The intended exit condition appears to concern the new traversed pair or its second half-edge. This is a local indexing tension, recorded rather than silently corrected.
- **Dossier connection:** This is the key picture for Derivation D7 and for the reusable encoding technique.

### Figure 5, page 30: a two-vertex base graph and a 3-lift

[Rendered page 30](visuals/page-30.png)

- **What it encodes:** On the left, directed half-edges $a,b$ form an undirected edge between base vertices $1$ and $2$, while $c,d$ form a loop at $2$. Origins are $o(a)=1$ and $o(b)=o(c)=o(d)=2$. On the right, every base vertex $v$ has fiber $\{v1,v2,v3\}$.
- **How to read it:** For $\sigma_a=(1\,2\,3)$, the non-loop base edge connects $11$ to $22$, $12$ to $23$, and $13$ to $21$. For $\sigma_c=(1)(2\,3)$, the base loop lifts to one loop at $21$ and two parallel edges joining $22$ and $23$. The double arc between $22$ and $23$ is the lift of the base loop, not another copy of the $a,b$ edge.
- **Main pattern:** Fiber permutations reconnect half-edges without changing base projection or local degrees. A loop can lift to a mixture of fixed loops and cycles between distinct fiber vertices.
- **Claim supported:** Definition 22 and the matrix decomposition $B_n=S_nN_n$. It also prepares the distinction between $H$, vectors constant on each directed-edge fiber, and $H^\perp$, where the new spectrum lives.
- **Visual ambiguity:** Direction is encoded by half-edge labels and formulas, not by arrows in the diagram. The picture is one chosen lift, not a claim about the typical shape of a random lift.
- **Dossier connection:** See Derivation D9 and the lift walk-through in `08-intuition.md`.

## Visual reading conclusion

All five figures participate in the proof's logic. Figures 1 and 5 teach definitions, Figure 2 justifies an algebraic correction term, and Figures 3 and 4 expose the combinatorics that makes the trace bounds possible. None supplies numerical evidence, and none should be cited as a substitute for its corresponding equations.
