# Techniques and reusable machinery

## Core spectral and probabilistic techniques

| Technique | Location | Problem it solves | Standard or paper-specific | Reusable pattern and possible alternative |
| --- | --- | --- | --- | --- |
| Block adjacency to singular values | Equation 1, page 2 | Converts a rectangular zero-one matrix problem into a symmetric spectral problem | Standard | Study $XX^*$ and $X^*X$ directly when no non-backtracking machinery is needed |
| Ihara-Bass bridge | Theorem 1 and Equations 4 to 8 | Links vertex adjacency eigenvalues to oriented-edge non-backtracking eigenvalues | Standard tool, carefully specialized to biregular degrees here | Compare block $D$ factors explicitly. A direct singular-value polynomial method works only after deriving the same transfer |
| Four-root case analysis | Equation 8, page 9 | Separates bulk, upper outliers, lower outliers, and rank loss | Paper-specific reading of a standard quadratic | Solve $y=x+ab/x+a+b$. Track real, imaginary, and circular branches before attempting probability |
| Nullspace forcing | Page 7 and Theorem 4(iii) | Converts rank loss into concrete large eigenvalues of $B$ | Elegant application of standard linear algebra | If $\operatorname{rank}X<n$, $\pm i\sqrt a$ appear. Rows' independence can alternatively be studied by anti-concentration, but that would be a different proof |
| Configuration model with conditioning | Section 4.1 | Makes the uniform simple graph ensemble computable by random matchings | Standard | Prove rare events in a permutation model, then divide by a bounded-below simplicity probability |
| Half-edge randomization separated from vertex geometry | Equation 9, $B=MN$ | Isolates random matching from deterministic non-backtracking restrictions | Standard in this proof tradition | Center $M$ rather than attempting to center dependencies in the graph directly |
| Local tangle-freeness | Definition 1, Lemma 5 | Reduces arbitrary walks to paths with at most one local cycle | Standard sparse random graph technique | A weaker typical-neighborhood theorem can be easier, but this argument needs all local neighborhoods with high probability |
| Dominant-eigenspace removal | Lemma 6 and Section 5.1 | Strips deterministic leading behavior without assuming normality | Standard imported lemma | In a Hermitian setting, orthogonal spectral projection would be simpler. Here both $T$ and $T^*$ range conditions matter |
| Selective tangle-free decomposition | Definitions 2 to 4 and Equation 17 | Allows each matrix-factor path to be simple while controlling globally tangled products separately | Established method adapted to biregular paths | Decompose first, then count main and remainder families with different expectations |
| Schatten-moment domination | Equations 11 and 24 | Controls a non-normal operator norm using real nonnegative trace quantities | Standard linear algebra | $\Vert C\Vert ^{2k}\leq\operatorname{Tr}((CC^*)^k)$. Alternative eigenvalue-power traces would fail for non-normal $C$ |
| Centered matching moments | Lemma 7 | Gives a small expectation penalty for consistent singleton patterns | Imported specific estimate | Keep consistency and multiplicity structured. Using only deterministic boundedness would lose the centering gain |
| Discovery-tree walk encoding | Lemmas 8 to 10 and Figure 5 | Bounds the number of circuits by topology and short descriptors rather than full paths | Adapted from related circuit-counting arguments | Encode old paths by endpoint, new paths by length, and non-tree edges by endpoint |
| Half-edge isomorphism counting | Lemma 11 | Translates graph-level paths back into configuration-model labels | Standard degree falling-factorial count | Assign factor $d_i$ at each vertex and $(d_i-1)$ for each later incident induced edge |
| Left-right imbalance tracking | Lemma 13 and Equation 26 | Prevents two degree-dependent scales from being confused | Particularly important in the biregular setting | Track $\psi=\mathscr R-\mathscr E/2$ explicitly. The audit in `09` flags unresolved sign and Corollary 12 issues |
| Three-regime trace partition | Section 5.8 | Matches each circuit geometry to the estimate that makes it small | Standard broad strategy, paper-specific partition | Separate repeated-edge dominant circuits, small excess circuits, and many-singleton circuits |
| Growing moment order | Equation 23 and Markov applications | Beats the polynomial trace multiplicity while preserving manageable entropy | Standard sophisticated moment-method parameter choice | $k\sim(\log n)^{1/3}$ gives denominator logarithm of order $(\log n)^{13/12}$ |
| $\ell$th-root compression | Section 5.9 | Turns logarithmic matrix-norm slack into vanishing spectral slack | Standard | Choose $\ell\asymp\log n$, then interpret stretched-exponential errors as asymptotically negligible |

## Application techniques

| Technique | Location | Reusable content |
| --- | --- | --- |
| Equitable frame lifting | Sections 6.1 and 6.2, Figure 6 | Class-wise constant degrees lift frame eigenvectors exactly by repeating coordinates over each class |
| Blockwise spectral control | Proposition 18 | Control every regular or biregular block, then bound the non-quotient spectrum through normalized block weights |
| Common degree scaling | Theorem 19 | Keep quotient Markov eigenvalues fixed while shrinking stochastic block contributions relative to them |
| Spectral tax on local code distance | Theorem 21 | Local code products give the positive term, and $\eta(\delta_1+\delta_2)/2$ subtracts a global consistency penalty |
| Deterministic sampling with expander mixing | Theorem 24 | Guarantees uniformly over target matrices once the fixed sampling graph is good, rather than averaging over fresh samples for each target |
| Grothendieck norm comparison | Theorem 24 | Converts general matrix discrepancy to sign-nuclear complexity and then to $\gamma_2$ complexity |
| Hadamard squaring of residuals | Theorems 24 and 25 | Converts mean-square error to a mean of $R=\Delta\circ\Delta$ and controls $\gamma_2(R)$ through submultiplicativity |
| Feasibility-bound replacement | Theorems 24 and 25 | Since $Y$ is feasible and $\hat Y$ minimizes, replace $\gamma_2(\hat Y)$ by $\gamma_2(Y)$ without solving the optimization explicitly |

## The reusable shortest pattern

A compact pattern for similar non-normal random operators is:

1. Isolate deterministic extremal modes.
2. Prove the local path family is combinatorially simple with high probability.
3. Center the random matching or independent entries.
4. Apply a Schatten trace moment with slowly growing order.
5. Partition circuits by repeated-edge and excess statistics.
6. Make the Markov denominator dominate both spectral scale and ambient dimension.
7. Transfer the conclusion back through an exact deterministic spectral identity.

In this paper, the delicate part is not the broad pattern. It is preserving the correct biregular degree powers throughout the circuit bookkeeping.
