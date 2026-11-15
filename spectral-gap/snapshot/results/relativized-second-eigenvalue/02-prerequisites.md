# Prerequisites

**Label convention.** The paper locations are **Paper**. The minimum explanations and study guidance are **Derived** or **Interpretation**, not claims that the paper itself teaches these subjects from scratch. No user background was supplied, so the last column is conditional rather than presumptive.

| Concept | Why it appears | Minimum working knowledge | Where used | Likely status and quick refresh |
| --- | --- | --- | --- | --- |
| Finite graph morphisms and multigraphs | The model allows multiple edges, whole-loops, and half-loops | A graph is a directed graph with a reversing involution. A half-loop is fixed by that involution, while a whole-loop has a distinct partner | Definitions 1.1.1 through 1.1.5 | Standard graph theory may be enough, but review these two loop conventions in Section 1.1 |
| Covering maps and étale maps | Random covers are the probability space, and feasible tangles are étale subgraphs | A covering is a bijection on incoming and outgoing local edge neighbourhoods. An étale map is an injection on those neighbourhoods | Section 1.1.3 and Proposition 1.2.2 | If unfamiliar, verify the definition on a single vertex and on a triangle before continuing |
| Fibrewise old and new functions | Relativization removes deterministic base eigenvectors | Old functions are constant on fibres. New functions have sum zero on each fibre. These spaces are orthogonal and adjacency-invariant | Definition 1.1.16 | Requires only elementary inner products. The old space has dimension $|V_B|$, not $n|V_B|$ |
| Adjacency spectra and trace | The final object is $\rho_B^{\mathrm{new}}(A_G)$ | Symmetric matrices have real eigenvalues. $\operatorname{Tr}(A^k)$ counts closed $k$-walks and equals $\sum\lambda^k$ | Sections 0.1 and 1.2 | Basic spectral theorem is sufficient |
| Hashimoto non-backtracking matrix | The proof's central matrix | Its indices are directed edges. A nonzero transition follows $e_1$ by $e_2$ exactly when $h(e_1)=t(e_2)$ and $e_2\ne e_1^{-1}$. Its $k$-trace counts strictly non-backtracking closed walks | Section 1.1.2 | Draw a three-vertex example by hand if the indexing is unfamiliar |
| Perron-Frobenius theory | Tangles compare spectral radii of nonnegative matrices | An irreducible nonnegative matrix has a positive dominant real eigenvalue equal to its spectral radius. Walk growth detects that radius | Sections 1.2.4 and 3.3 | Review the irreducible nonnegative version and the distinction between $\mu_1$ and all $\mu_i$ |
| Ihara-Bass determinant formula | Converts Hashimoto eigenvalue control into adjacency control | For $d$-regular $G$, each adjacency $\lambda$ gives roots of $\mu^2-\lambda\mu+(d-1)=0$, plus harmless $\pm1$ factors | Equations (0.9) and (1.1) | Treat the formula as an external input used by the paper. Memorize $\lambda=\mu+(d-1)/\mu$ |
| Independent uniform permutations | Define $\mathcal C_n(B)$ | For $a\le n$, fixing $a$ compatible values of a uniform permutation has probability $(n-a)!/n!$ | Sections 1.1.5 and 2.3 | This identity is the only specialized probability fact needed for the main engine |
| Matchings and involutions | Handles half-loops and odd degree | For even $n$, a fixed-point-free involution corresponds to a perfect matching. Odd $n$ uses one fixed point | Sections 1.1.5 and 3.4 | Review odd factorials separately from ordinary factorials |
| Euler characteristic and graph order | Determines $1/n$ exponents | In the no-half-loop setting, $\chi=|V|-|E|$ and $\operatorname{ord}=-\chi=|E|-|V|$. Trees have $\operatorname{ord}=-1$ and cycles have $\operatorname{ord}=0$ | Sections 1.2.4 and 2.2.1 | Be alert to the paper's erroneous tree sign, documented in `09-assumptions-and-weak-points.md` |
| Non-backtracking walks and beaded paths | Makes finite type compression possible | A beaded path has degree-two interior vertices. A non-backtracking walk that enters such a path must continue along it | Sections 1.3.5, 2.1.1, 2.3.4 | Review figure 8, barbell, and theta shapes verbally. The source has no drawings |
| Finite partial orders | Converts certification into finite sums | An upper set contains every element above each of its members. $\mathbb Z_{\ge1}^s$ uses componentwise order and componentwise maxima | Section 2.4.3 | Know that every upper set here has finitely many minimal elements |
| Inclusion-exclusion and Möbius inversion | Decomposes upper-set sums and tangle indicators | Intersect cones by taking componentwise maxima, then alternate signs. Absolute convergence permits rearrangement | Theorems 2.4.23, 2.4.24, and Lemma 2.5.11 | Ordinary finite inclusion-exclusion is enough to understand the infinite limiting argument |
| Generating functions and convolutions | Multiplies local length contributions | $(g_1*g_2)(k)=\sum_{j=0}^k g_1(j)g_2(k-j)$. Weighted versions use $\mathbf m\cdot\mathbf k=k$ | Section 2.2.2 through 2.2.4 | Review geometric and polynomial convolution identities |
| Jordan forms and polyexponentials | Matrix powers produce coefficients depending on $k$ | Entries of $M^k$ have the form $\sum_\nu \nu^k p_\nu(k)$. Jordan block sizes control polynomial degrees | Sections 2.1.1 and 2.2.5 | Diagonalizable intuition plus the Jordan-block correction is sufficient |
| Finite differences | Side-steps unknown coefficients | $(S-\mu)^D$ annihilates $\mu^k p(k)$ when $\deg p<D$ | Proposition 2.6.1 | Derive it from $\sum_{j=0}^D(-1)^{D-j}\binom Dj j^s=0$ for $s<D$ |
| Logarithmic trace method | Converts moment control to probability | An exceptional eigenvalue $\mu$ with $|\mu|>\tau$ is isolated using $\mu^k$ or even moments, then $k$ is chosen proportional to $\log n$ | Sections 1.2.1 and 2.6.3 | Understand why polynomial factors in $k$ become negligible after logarithmic choices |
| Expansion and spreaders | Removes eigenvalues near dominant base values | A $\gamma$-spreader has $|\Gamma(A)|\ge(1+\gamma)|A|$ for $|A|\le|V|/2$, and spread implies a spectral gap | Section 3.2 | Read after the main proof, not before it |
| Algebraic numbers and finite computation | Makes exact strict spectral comparisons decidable in principle | Algebraic integers with controlled degree and coefficients have effective separation from zero when nonzero | Proposition 3.3.3 | Only the decidability principle is needed, not computational algebraic-number expertise |

## Recommended reading order within the paper

1. Sections 0.1, 1.1.2, 1.1.3, and 1.2.3 for the spectral language.
2. Sections 1.3 and 2.3.1 through 2.3.3 for the probability engine.
3. Sections 1.4 and 2.4 for the certified trace, the conceptual center.
4. Sections 2.5 through 2.7 for recovering the main theorem.
5. Sections 3.2 and 3.3 only after spreading's separate purpose is clear.
6. Sections 3.4 through 3.6 as variants and open directions.
