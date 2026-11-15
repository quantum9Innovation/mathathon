# Notation

Locations are PDF page numbers. **Derived conventions** are local to this dossier and are not silently attributed to Friedman.

## Global parameters and spectrum

| Symbol | Meaning | Type or domain | Introduced | Common confusion |
| --- | --- | --- | --- | --- |
| $d$ | Fixed regular degree | Integer, usually $d\geq3$, even for $\mathcal G_{n,d}$ and $\mathcal H_{n,d}$ | Page 1 | It does not grow with $n$. The four models impose different parity conditions. |
| $n$ | Number of vertices, tending to infinity | Positive integer, with model-specific parity | Page 1 | $\mathcal J_{n,d}$ uses odd $n$. |
| $k$ | Walk or trace length | Positive integer | Page 5 | Sometimes an index vector entry $k_i$ is an edge length. The final proof takes $k\asymp\log n$. |
| $\epsilon$ | Fixed additive spectral allowance | Positive real | Page 2 | The theorem does not prove the case $\epsilon=0$. Section 8 also uses $\epsilon$ for a walk-growth gap. |
| $q$ | **Derived shorthand** for $d-1$ in this dossier | Integer greater than 1 | Not paper notation | It is not an edge length, probability, or expansion index. |
| $A$ | Adjacency matrix | $n\times n$ real symmetric | Page 1 | Whole-loops contribute 2, half-loops contribute 1. |
| $\lambda_i(G)$ | $i$-th largest adjacency eigenvalue | Real, $\lambda_1\geq\cdots\geq\lambda_n$ | Page 1 | The main bound controls $|\lambda_i|$ for every $i>1$, not just $\lambda_2$. |
| $\lambda_{\max}^{\mathrm{new}}$ | **Derived shorthand** for $\max_{i>1}|\lambda_i|$ | Nonnegative real | Not paper notation | This is a convenience, not a paper definition. |

## Random models and labels

| Symbol | Meaning | Type | Introduced | Common confusion |
| --- | --- | --- | --- | --- |
| $\mathcal G_{n,d}$ | Graph from $d/2$ independent uniform permutations | Random $d$-regular pseudograph | Page 2 | Multiple edges and whole-loops are allowed. |
| $\mathcal H_{n,d}$ | Like $\mathcal G_{n,d}$ but every permutation is an $n$-cycle | Random $d$-regular pseudograph | Page 3 | Each permutation has $(n-1)!$ possibilities. |
| $\mathcal I_{n,d}$ | Graph from $d$ independent perfect matchings | Random $d$-regular multigraph, $n$ even | Page 4 | Matching labels are self-inverse. |
| $\mathcal J_{n,d}$ | Graph from $d$ independent near-perfect matchings plus a half-loop | Random $d$-regular pseudograph, $n$ odd | Page 4 | Its detailed $\tau_{\mathrm{fund}}$ in Section 6 differs from the exponent imported in Theorem 1.3. |
| $\pi_j$ | $j$-th random permutation or matching | Random bijection or involution | Page 2 | In $\mathcal G_{n,d}$ and $\mathcal H_{n,d}$, both $\pi_j$ and $\pi_j^{-1}$ occur as edge directions. |
| $\Pi$ | Alphabet of edge labels $\pi_j$ and their inverses | Finite set of size $d$ for the permutation models | Pages 2 and 20 | Older papers may use $2d$ where this paper uses $d$. |
| whole-loop | Two directed self-loops paired with each other | Contributes 2 to adjacency degree | Page 20 | Counts as one undirected edge for tangle order. |
| half-loop | A directed self-loop paired with itself | Contributes 1 to adjacency degree | Page 20 | Counts as one edge for tangle order, not half an edge. |

## Walks and traces

| Symbol | Meaning | Type | Introduced | Common confusion |
| --- | --- | --- | --- | --- |
| irreducible word or walk | No consecutive letter or edge followed by its inverse | Word in $\Pi^*$ or graph walk | Pages 5 and 8 | Synonyms are reduced and non-backtracking. Half-loops cannot repeat consecutively. |
| strongly irreducible | Irreducible and last letter is not inverse of first | Closed word or walk | Page 89 | Stronger than closed and irreducible separately. |
| $\operatorname{IrredTr}(A,k)$ | Number of irreducible closed length-$k$ walks | Nonnegative integer | Page 8 | Not equal to $\operatorname{Tr}(A^k)$ without Chebyshev correction. |
| $\operatorname{IrSelTr}_{S,\Psi}(G,k)$ | Selective irreducible trace | Nonnegative integer | Page 59 | It discards walks with a forbidden short segment, even if the remainder is harmless. |
| $\operatorname{SIT}(G,k)$ | Strongly irreducible trace | Nonnegative integer | Page 89 | Half-loops require special treatment at $k=1$. |
| $\operatorname{SSIT}_{S,\Psi}(G,k)$ | Selective strongly irreducible trace | Nonnegative integer | Page 94 | This is the trace fed into Lemma 11.1. |
| $A_k$ | Matrix counting irreducible length-$k$ walks | $n\times n$ nonnegative integer matrix | Page 10 | This is not the power $A^k$. |
| $q_k$ | Polynomial with $A_k=q_k(A)$ | Degree-$k$ polynomial | Page 10 | It is not the tree shorthand $q=d-1$ used in this dossier. |
| $N_{k,i}$ | Number of length-$k$ words reducing to a fixed irreducible word of length $i$ | Nonnegative integer | Page 11 | Lemma 2.4 assumes $k,i$ even. |
| $G_{\mathrm{Irred}}$ | Directed edge graph encoding non-backtracking steps | Vertices are directed edges of $G$ | Page 27 | Its walk length is shifted relative to the original edge walk. |
| $\lambda_{\mathrm{Irred}}(G)$ | Perron growth or largest non-backtracking eigenvalue | Nonnegative real | Page 28 | It scales like effective branching, not like an adjacency eigenvalue. |
| $\mu_{1,2}(\lambda)$ | Roots of $\mu^2-\lambda\mu+(d-1)=0$ | Complex or real | Page 90 | Nonreal roots have modulus $\sqrt{d-1}$. Do not confuse with Möbius weights $\mu_\Omega$. |

## Variable-length and infinite graph objects

| Symbol | Meaning | Type | Introduced | Common confusion |
| --- | --- | --- | --- | --- |
| VLG | Variable-length graph | Positive integer length on each edge | Page 21 | It is not a probabilistic random length until a separate model says so. |
| bead | Degree-two non-loop vertex, or directed indegree and outdegree one | Vertex | Page 21 | The first vertex of a type need not have degree at least 3. |
| $G_{\mathrm{sbd}}$ | Subdivision of a VLG into unit-length paths | Ordinary graph | Page 21 | Suppression and subdivision are inverse in the intended setting. |
| $G\vert_W$ | Realization on retained vertices $W$ | Directed VLG | Page 22 | It may have infinitely many edges. |
| $c_G(u,v,k)$ | Number of length-$k$ walks from $u$ to $v$ | Nonnegative integer or weighted count | Page 22 | For a VLG, length sums edge lengths. |
| $\lambda_1(G)$ | Perron growth of a VLG | Nonnegative real | Page 23 | For a finite graph this agrees with adjacency Perron eigenvalue. On infinite graphs it is a growth or operator norm quantity. |
| $Z_G(z)$ | Edge-length generating matrix $Z_{uv}=\sum_e z^{\ell(e)}$ | Formal power-series matrix | Page 23 | It is not $I+Z+Z^2+\cdots$. |
| $M_G(z)$ | Walk generating matrix $I+Z_G+Z_G^2+\cdots$ | Formal power-series matrix | Page 24 | Entries count all $c_G(u,v,k)z^k$. |
| $S_d(z)$ | First-return series for an infinite rooted tree | $\frac{1-\sqrt{1-4(d-1)z^2}}2$ | Page 32 | The other quadratic root is not the series near zero. |
| $\operatorname{Tree}_d(\psi)$ | $d$-regular tree completion of $\psi$ | Infinite graph with $\psi$ inclusion | Page 31 | Figure 1 draws only a finite truncation. It is not the universal cover of an arbitrary graph without the stated inclusion category. |

## Tangles and orders

| Symbol | Meaning | Type or domain | Introduced | Common confusion |
| --- | --- | --- | --- | --- |
| $\psi,\Omega$ | Finite tangles, often $\Pi$-labelled | Connected graph occurring in some model graph | Pages 33 and 83 | $\Omega$ later records a forced tangle overlapping a walk form. |
| $\operatorname{ord}(\psi)$ | $|E_\psi|-|V_\psi|$ | Integer, usually at least -1 for connected graphs | Page 36 | It is cyclomatic number minus 1. Both loop kinds count as one edge. |
| critical | $\lambda_{\mathrm{Irred}}(\psi)=\sqrt{d-1}$ | Tangle class | Page 35 | Critical is included in supercritical. |
| supercritical | $\lambda_{\mathrm{Irred}}(\psi)\geq\sqrt{d-1}$ | Tangle class | Page 35 | It need not force a strict $\lambda_2>2\sqrt{d-1}$ bound when equality holds. |
| hypercritical | $\lambda_{\mathrm{Irred}}(\psi)>\sqrt{d-1}$ | Tangle class | Page 35 | Hypercritical is the strict subclass used for the lower failure bound. |
| $\tau_{\mathrm{fund}}$ | Smallest order of a supercritical tangle | Model-dependent nonnegative integer | Page 2 | It is model-specific. Section 6 must be checked rather than copied indiscriminately. |
| $s$ | Smallest order of a hypercritical tangle | Model-dependent integer | Page 3 | It can exceed $\tau_{\mathrm{fund}}$ by 1 at critical equality. |
| $\Psi_{\mathrm{ord}}(\tau)$ | All tangles of order at least $\tau$ | Tangle set | Page 60 | $\Psi_{\mathrm{ord}}(\tau_1,\tau_2)$ adds an upper bound. |
| $\Psi_{\mathrm{eig}}$ | All supercritical tangles | Infinite tangle set | Page 61 | $\Psi_{\mathrm{eig}}[r]$ restricts order at most $r$. |
| $\Psi_{\min}[r]$ | Inclusion-minimal members of $\Psi_{\mathrm{eig}}[r]$ | Finite set by Lemma 9.2 | Page 81 | Minimal refers to inclusion, not merely fewest edges. |
| $S$ | Maximum length of an inspected forbidden subpath | Positive integer | Page 59 | It is fixed sufficiently large before the final $n\to\infty$. |
| $B$ | Threshold for long new-type edges | Integer greater than $S$ | Page 55 | Fixed edges have length below $B$, long edges have length at least $B$. |
| $\chi_\Psi$ | Indicator that at least one $\Psi$-tangle occurs | $\{0,1\}$-valued graph function | Page 82 | Expected inclusion counts do not directly give $\mathbb E\chi_\Psi$. |

## Walk collections and new types

| Symbol | Meaning | Type | Introduced | Common confusion |
| --- | --- | --- | --- | --- |
| $(w,\vec t)$ | Weakly potential walk | Word $w=\sigma_1\cdots\sigma_k$, vertex vector $\vec t\in[n]^{k+1}$ | Page 42 | It becomes a potential walk only when feasible. |
| $P(w,\vec t)$ | Probability that $\sigma_i(t_{i-1})=t_i$ for all $i$ | Real in $[0,1]$ | Page 42 | Feasibility requires consistency with every permutation or involution. |
| $\mathcal W(k,n)$ | Walk collection | Set of potential walks | Page 43 | SSIIC means symmetric, size invariant, irreducible, closed. |
| $[\vec t]$ | Vertex-relabelling equivalence class | Finite up to symmetry for fixed $k$ | Page 44 | $[\vec t]_n$ additionally restricts coordinates to $[n]$. |
| $\operatorname{WalkSum}(\mathcal W,k,n)$ | Sum of $P(w,\vec t)$ over the collection | Real | Page 43 | It may equal an expectation only after including the intended normalizing walk count. |
| $E_{\mathrm{symm}}(w,\vec t)_n$ | Sum over one relabelling class | Real | Page 44 | Equals $n(n-1)\cdots(n-v+1)P(w,\vec t)$. |
| $\Gamma$ | Form traced by a potential walk | Oriented, labelled, numbered graph | Page 52 | Vertex and edge numberings remember first traversal order. |
| $T$ | Type | Compressed connected oriented graph | Page 54 | All vertices except possibly the first have degree at least 3. |
| $\widetilde T$ | $B$-new type | Lettered type plus long/fixed partition and fixed data | Page 55 | Figure 2 illustrates only form and old type, not the new-type decorations. |
| $W_\Gamma,W_T,W_{\widetilde T}$ | Counts of legal walks with restrictions | Nonnegative integers | Pages 53, 60, and 61 | Subscript changes signal which data determine the count. |
| $a_j$ | Number of determined values or edges labelled $\pi_j$ | Nonnegative integer | Page 45 | In a loop-model variation, fixed involution data need separate treatment. |
| $v$ | Number of distinct vertices | Positive integer | Page 44 | In an $\Omega$-type it may count vertices of $\Gamma\cup\Omega$. |
| $e$ | $\sum_j a_j$, total determined labelled edges | Nonnegative integer | Page 45 | Paper order is $e-v$ for a walk pair, whereas tangle order is $|E|-|V|$. |
| $p_i(a_1,\ldots,v)$ | Expansion polynomials | Polynomial | Page 45 | These are usually unknown and need not be computed. |
| $r$ | Requested finite expansion order | Positive integer | Page 48 | It is not an edge length or a tangle order. Later $r$ is chosen large enough for the final probability exponent. |
| $R_{T,L}$ | Word or polynomial sum over compatible edge labels | Function of edge lengths | Page 73 | Theorem 8.3 reduces it to tractable exponential and polynomial factors. |
| $\vec m$ | Traversal multiplicities of type edges | Positive integer vector | Page 56 | $m_i$ counts traversals, not beaded-path length. |
| $M_1,M_2$ | Multiplicity totals on long and fixed edges | Nonnegative integers | Page 61 | The decay estimate is exponential in $BM_1+M_2$. |
| $|p|$ | Coefficient norm | Largest absolute coefficient | Page 75 | It is not a function sup norm. |

## Conditional tangles and final eigenvalue lemma

| Symbol | Meaning | Type | Introduced | Common confusion |
| --- | --- | --- | --- | --- |
| $\Psi^+$ | Representatives of nonempty unions of $\Psi$-tangles | Poset of derived tangles | Page 83 | Its low-order part is finite under Theorem 9.3 hypotheses. |
| $N(\Omega,\Omega')$ | Number of inclusions of $\Omega$ into $\Omega'$ | Nonnegative integer | Page 83 | $N(\Omega,\Omega)$ is an automorphism count. |
| $\mu_\Omega$ | Möbius weights solving inclusion equations | Real | Page 84 | Not related to spectral roots $\mu_{1,2}(\lambda)$. |
| $\Omega$-type | Type incorporating a forced tangle $\Omega$ | Partially numbered graph | Page 87 | Unnumbered $\Omega$ edges need not be traversed by the walk. |
| $\theta_i$ | Normalized spectral-shift variables in Lemma 11.1 | Complex random variables | Page 94 | The application is $\theta_i=1-(1-\chi_\Psi)\nu_i/(d-1)$. |
| $\nu_i$ | Complete multiset of non-backtracking spectral values | $nd$ complex numbers on even $k$ | Page 106 | Nonreal $\nu_i$ have modulus $\sqrt{d-1}$. |
| $\sigma_k$ | Shift in trace length | $(\sigma_kf)(k)=f(k+1)$ | Page 92 | It is not an edge letter $\sigma_i$. |
| $\gamma$ | Spreader parameter or permitted power $k\leq n^\gamma$ | Positive real | Pages 94 and 99 | These are separate local uses. |

## Two sign conventions worth memorizing

1. For a form or tangle, $\operatorname{ord}=E-V$. For a connected graph, the cycle rank is $E-V+1$, so $\operatorname{ord}$ is one less. The leading occurrence scale is $n^{V-E}=n^{-\operatorname{ord}}$.
2. Theorem 6.6 uses $(\sqrt{d-1}-\eta)^{BM_1+M_2}$. The multiplications by $B$ and the subtraction of $\eta$ are both crucial. The selective expansion wins because the compensating sums have approximate base $(d-1)^{-1/2}$.
