# Prerequisites

The checklist below gives the minimum background needed, why it appears, and a paper-local place to refresh it. User familiarity is unconfirmed, so the final column is an assumption to check during teaching rather than a claim about the user.

| Concept | Minimum needed here | Where used | Likely status |
| --- | --- | --- | --- |
| Adjacency matrix and spectrum | Eigenvalues of a real symmetric matrix are real. For $A=\begin{pmatrix}0&X\\X^*&0\end{pmatrix}$, eigenvalues come in pairs $\pm\xi$. | Equation 1, Sections 1.1 and 3 | Assumed known |
| Singular value decomposition | Singular values of $X$ are absolute adjacency eigenvalues. Rank equals the number of nonzero singular values, while $X^*$ has nullity $n-\operatorname{rank}(X)$. | Theorem 4(iii) and Lemma 2 | Assumed known, worth a short review |
| Bipartite biregular graphs | Left vertices have degree $d_1$, right vertices have degree $d_2$, and edge counting forces $nd_1=md_2$. | Figure 1 and Section 1.1 | New terminology but elementary |
| Non-backtracking walks | Consecutive oriented edges share a head-to-tail vertex, but the second is not the immediate reversal. $B$ indexes oriented edges, not vertices. | Section 2 | New for many readers, study carefully |
| Ihara-Bass formula | Accept the determinant identity as a black box initially. The paper's later algebra is what matters for this paper's conclusions. | Theorem 1 and Equations 4 to 8 | The formula can be treated as input |
| Perron-Frobenius behavior | For a connected nonnegative biregular non-backtracking graph, the positive leading root is $\sqrt{(d_1-1)(d_2-1)}$. Bipartiteness adds its negative. | Section 2 and derivation of $T$ | Standard background, non-normality is the key caution |
| Configuration model | Match labeled half-edges uniformly. Conditioning on a simple outcome gives the uniform simple biregular law. | Section 4.1 | New but easy to simulate conceptually |
| Conditioning on simplicity | If $F$ is a bad event and $S$ is simplicity with $\mathbb P(S)\geq c>0$, then $\mathbb P(F\mid S)\leq c^{-1}\mathbb P(F)$. | Transfer of all configuration-model estimates | Derived in `06-derivations.md` |
| Tangle-free graphs | An $\ell$-tangle-free graph has at most one cycle in every radius-$\ell$ ball. A locally minimal encoding then has controlled complexity. | Definition 1, Lemma 5, Section 5.4 | New and central |
| Tree excess | For a connected circuit graph, $\chi=\mathscr E-\mathscr V+1$. Trees have $\chi=0$, while one independent cycle gives $\chi=1$. | Sections 5.4 to 5.8 | Essential. Appendix A prints the wrong sign |
| Spectral norm and trace moments | For any real matrix $C$, $\Vert C\Vert ^{2k}\leq \operatorname{Tr}((CC^*)^k)$. Trace expands into circuits of matrix entries. | Equations 11 and 24 | Assumed linear algebra, derived explicitly in notes |
| Markov's inequality | A nonnegative $2k$th moment controls probability after dividing by the $2k$th power of the desired norm threshold. | Equations 34 and 36 | Assumed known |
| Union bounds with many terms | Simultaneous control of $\ell$ remainder matrices needs a common bound in $j$, not merely separate informal high-probability assertions. | Section 5.9 | Important proof-reading skill |
| Combinatorial encodings | Bound the number of walks by recording only endpoints of old tree paths, lengths of new excursions, and non-tree edges. | Lemmas 8 to 10, Figure 5 | New and technically central |
| Expander mixing | Sampled edge counts are close to density predictions, with an error proportional to $\eta$. | Code and matrix-completion applications | Needed only for applications |
| Frame graphs and Markov matrices | Class-wise constant degrees lift eigenvectors of the small frame to piecewise-constant eigenvectors of the large graph. | Section 6 and Figure 6 | New, but linear algebra is elementary |
| Factorization norm $\gamma_2$ | It minimizes a product of maximum row lengths over factorizations. Hadamard products satisfy $\gamma_2(A\circ B)\leq\gamma_2(A)\gamma_2(B)$. | Section 8 | New. Its use can be learned locally |
| Grothendieck comparison | The sign nuclear norm and $\gamma_2$ differ by at most a universal constant $K_G$. | Theorem 24 proof | Can be used as an imported fact |
| Tanner codes | Edge bits are codewords when local views at every vertex belong to specified local codes. | Section 7 | Coding definitions can be learned locally |

## Recommended learning order

1. Read `03-notation.md` alongside Figure 1.
2. Master the two-line matrix relation $B=MN$ and why $M$ contains the only randomness.
3. Work through the spectral transfer in `06-derivations.md` before attempting the moment proof.
4. Read Figures 4 and 5 before the formal path-counting lemmas.
5. Postpone the three applications until Theorem 4 feels easy to state and derive from Theorem 3.

## What is not a prerequisite

A prior course on expanders, random lifts, stochastic block models, LDPC codes, or matrix completion is not necessary for the main theorem. These provide motivation only. No external literature survey is needed for a first reading.
