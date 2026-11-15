# Notation

The paper reuses several letters in new contexts. Section 3 explicitly resets its notation. This table records the intended reading, with page or equation references. The symbol $\underline{\phantom{M}}$ denotes centering or fiberwise centering, not complex conjugation.

## Global and regular-graph notation

| Symbol | Meaning and type | Introduced | Common confusion and related symbols |
| --- | --- | --- | --- |
| $n$ | Number of vertices in the regular model, later the lift degree | Page 1, Definition 22 | The lift has $|V|n$ vertices, not $n$ vertices |
| $d$ | Fixed regular degree, $d\geq3$ | Page 1 | In Section 4 it becomes the maximum base degree, Eq. 59 |
| $q$ | Dossier shorthand for $d-1$, not used consistently by the paper | Derived | Do not confuse with $q(\gamma)$ in Eq. 38 or $q$ in Lemma 12 |
| $G=(V,E)$ | Finite simple graph in the introduction | Page 1 | The configuration model and base lift graphs permit loops and multiple edges |
| $A$ | Adjacency matrix indexed by $V$ | Page 1 | $A^\ell$ counts ordinary walks, unlike $B^\ell$ |
| $\mu_i$ | Ordered real adjacency eigenvalues, $\mu_n\leq\cdots\leq\mu_1$ | Page 1 | $\mu(\gamma)$ in Eq. 40 is a different scalar, an expected path product |
| $\mu$ | $\max\{|\mu_i|:|\mu_i|<d\}$ | Page 1 | Excludes both adjacency eigenvalues of modulus $d$ |
| $\widehat E$ or $\vec E$ | Half-edge or directed-edge set. In the configuration model, $[n]\times[d]$ | Page 5, page 30 | PDF extraction may lose the arrow. This is not the undirected edge set $E$ |
| $\vec E(v)$ | $\{v\}\times[d]$, the $d$ half-edges at $v$ | Eq. 6 | $\vec E_\gamma(v)$ later means only visited half-edges at $v$ |
| $\sigma$ | Uniform fixed-point-free involution implementing the configuration matching | Page 5 | In Sections 3 and 4 it is instead a family of fiber permutations |
| $M(\vec E)$ | Set of perfect matchings represented as involutions | Page 5 | $M$ without parentheses is also a matrix |
| $M$ | Symmetric permutation matrix of the configuration matching, $M_{ef}=\mathbf1_{\sigma(e)=f}$ | Eq. 8 | $M^*=M$ here, unlike general directed-edge permutation matrices $M_e$ in the lift section |
| $N$ | Deterministic local switch matrix, $N_{ef}=\mathbf1_{u=v,\ i\ne j}$ for $e=(u,i)$ and $f=(v,j)$ | Eq. 9 | It connects distinct half-edges at one vertex and is not the matching |
| $B=MN$ | Configuration-model non-backtracking matrix on $\mathbb R^{nd}$ | Eq. 10 | $B$ is generally nonnormal despite $M$ and $N$ being symmetric |
| $\lambda_i$ | Eigenvalues of $B$, ordered by decreasing modulus after $\lambda_1=d-1$ | Page 6 | For lifts, $\lambda_i$ instead denotes only new eigenvalues |
| $\chi$ | All-ones vector, here in $\mathbb R^{dn}$ | Eq. 11 | In the lift proof it is the all-ones vector in $\mathbb R^n$, one coordinate per fiber index |
| $\underline M$ | $M-(dn)^{-1}\chi\chi^*$ | Eq. 15 | Centering changes the path product, so deletion and centering do not commute |
| $\underline B$ | $\underline M N$ | Eq. 16 | The paper says this matrix is not ultimately used. Its tangle-restricted power $\underline B^{(\ell)}$ is used |
| $J$ or $\chi\chi^*$ | All-ones matrix or rank-one operator of the appropriate size | Page 3, Eq. 21 | Normalization differs by context |
| $r$ | $|\vec E|/2-|V|=nd/2-n$ in Ihara-Bass | Eq. 12 | In Section 3, $r=|\vec E|$ instead |

## Path and decomposition notation

| Symbol | Meaning and type | Introduced | Common confusion and related symbols |
| --- | --- | --- | --- |
| $\ell$ | Length of a non-backtracking block, ultimately proportional to $\log n$ | Section 2.1 | $\ell'=\ell+2$ appears only in path-counting estimates |
| $\gamma=(\gamma_1,\ldots,\gamma_{2\ell+1})$ | A sequence of half-edges encoding a length-$\ell$ non-backtracking path | Definition 4, page 7 | It has $2\ell+1$ entries, not $\ell$ entries |
| $\gamma_t=(v_t,i_t)$ | A visited half-edge and its vertex and local label | Definition 4 | Repetition of the same half-edge encodes shared incidence in the matching product |
| $V_\gamma$ | Set of distinct visited vertices | Definition 4 | $s=|V_\gamma|$ in trace enumeration |
| $E_\gamma$ | Set of distinct unordered visited half-edge pairs $\{\gamma_{2t-1},\gamma_{2t}\}$ | Definitions 4 and 10 | This loses traversal multiplicity by design |
| $G_\gamma$ | Multigraph supported on $V_\gamma$ and $E_\gamma$ | Definition 4 | It is the visited support, not necessarily an induced subgraph of $G$ |
| $\Gamma^\ell$ | All non-backtracking half-edge sequences of the prescribed length | Definition 4 | Independent of the random configuration $\sigma$ |
| $\Gamma_{ef}^{\ell}$ | Such sequences with $\gamma_1=e$ and $\gamma_{2\ell+1}=f$ | Definition 4 | The $ef$ are half-edges, not ordinary vertices |
| $F^\ell$ and $F_{ef}^{\ell}$ | Tangle-free subsets of $\Gamma^\ell$ and $\Gamma_{ef}^{\ell}$ | Definition 5 | “Tangle-free" here means at most one cycle in the visited support |
| $B^{(\ell)}$ | Tangle-free path sum with uncentered factors $M$ | Eq. 18 | If $G$ is $\ell$-tangle-free, then $B^{(\ell)}=B^\ell$ |
| $\underline B^{(\ell)}$ | Tangle-free path sum with centered factors $\underline M$ | Eq. 19 | It is generally not equal to $\underline B^\ell$, even on $\ell$-tangle-free graphs |
| $p_k(\gamma)$ | Product centered before position $k$, uncentered afterward, with the $k$-center correction omitted | Eq. 21 | The omitted factor $M-\underline M=1/(dn)$ is placed outside the sum |
| $F_k^\ell$ | Paths whose three pieces around position $k$ are separately tangle-free | Page 10 | $F^\ell\subset F_k^\ell$, with generally strict inclusion |
| $R_k^{(\ell)}$ | Remainder matrix supported on $F_k^\ell\setminus F^\ell$ | Eq. 22 | Figure 2 is the combinatorial reason this term cannot be dropped |
| $k_i$ | $k$ for odd trace strands and $\ell-k+1$ for even strands | Eq. 46 | Reversal of even strands shifts the deletion position |
| $G_\gamma^k$ | Support after omitting the $k_i$-th half-edge pair from every trace strand | Page 26 | It may be disconnected, unlike $G_\gamma$ for $W_{\ell,m}$ |
| $W_{\ell,m}$ | $2m$ tangle-free paths satisfying alternating boundary conditions | Eqs. 36 and 37 | Figure 3 is the best mental model |
| $W_{\ell,m}^k$ | Analogue for tangled strands with tangle-free prefix and suffix | Page 26 | The superscript $k$ is the remainder location, not a path length |

## Path-counting notation

| Symbol | Meaning and type | Introduced | Common confusion and related symbols |
| --- | --- | --- | --- |
| $m$ | Positive trace-moment integer in Sections 2.5 and 4.3 | Eq. 35 | It is not $dn$. In Proposition 11's proof the paper temporarily sets $m=dn$ instead |
| $k$ | Number of matched pairs in a path product | Proposition 11 | Elsewhere it locates the correction within $R_k^{(\ell)}$. In overview discussions it can be a walk length |
| $m_\gamma(e)$ | Multiplicity of a half-edge in a sequence | Definition 10 | Distinct from the matrix $M$ and trace parameter $m$ |
| $m_\gamma(\{e,f\})$ | Number of visits to a distinct matched pair | Definition 10 | Multiplicity one and consistency are separate properties |
| Consistent edge | A pair $\{e,f\}$ whose two distinct half-edges occur exactly together and nowhere else | Definition 10 | For random lifts, the extra configuration-model condition $e\ne f$ is not needed |
| $a$ | Number of distinct visited matched pairs, $|E_\gamma|$ | Proposition 11 | Not the tail exponent $a$ in Eqs. 2 and 13 |
| $b$ | Number of centered occurrences on inconsistent multiplicity-one pairs | Proposition 11 | Produces the factor $2^b$ |
| $a_1$ | Number of centered occurrences on consistent multiplicity-one pairs | Proposition 11 | Produces the valuable factor $(3k/\sqrt{dn})^{a_1}$ |
| $s$ | Number of distinct visited vertices, $|V_\gamma|$ | Lemma 15 | $s_v$ in Lemma 30 counts lift vertices over each base $v$ |
| $g$ | $a-s+1$ | Lemma 15 | For connected $G_\gamma$, this is its cycle rank. For disconnected $G_\gamma^k$, the forest excess is $g+p-1$ |
| $\mathcal W_{\ell,m}(s,a)$ | Canonical isomorphism representatives with given $s$ and $a$ | Lemma 16 | Calligraphic $\mathcal W$ is not the whole path family $W$ |
| $q(\gamma)$ | Endpoint multiplicity, at most $(d-1)^m$ | Eq. 38 | Not the probabilistic $q$ in Lemma 12 |
| $\mu(\gamma)$ | Expected centered product for one path circuit | Eq. 40 | Not an adjacency eigenvalue $\mu_i$ |
| $\mu_k(\gamma)$ | Expected mixed centered and uncentered product for remainder paths | Page 28 | Uses $G_\gamma^k$ rather than all $k_i$-pairs |
| $T,T^*,S$ | Deterministic consistent-edge set and its two random subsets in the conditional moment proof | Pages 16 to 18 | $S$ here is not the edge-reversal matrix of Section 3 |
| $(n)_k$ | Falling factorial $n(n-1)\cdots(n-k+1)$ | Page 13 | The paper's double-parenthesis falling factorial on page 17 instead decreases in steps of $2$ |
| $P_s(t)$ | Polynomial formed by products of distinct indices in Lemma 12 | Page 13 | It has degree $2s$, which drives the finite-difference cancellation |

## Random-lift notation

| Symbol | Meaning and type | Introduced | Common confusion and related symbols |
| --- | --- | --- | --- |
| $G=(V,\vec E,\iota,o)$ | Abstract possibly irregular multigraph | Page 30 | $\iota$ reverses directed edges and $o$ gives their origins |
| $t(e)$ | Terminal vertex $o(\iota(e))$ | Page 30 | $t$ is also an integer path index elsewhere |
| $r$ | $|\vec E|$, the number of base directed edges | Page 30 | Thus $B$ is $r\times r$ and $B_n$ is $nr\times nr$ |
| $\rho_i$ | Eigenvalues of the base non-backtracking matrix $B$ | Page 31 | $\rho_1>1$ is the Perron eigenvalue under the standing hypotheses |
| $S$ | Base reversal permutation matrix, $S_{ef}=\mathbf1_{f=\iota(e)}$ | Eq. 49 | Here $B=SN$. It is unrelated to the temporary matrices $R,S$ in Lemma 3 |
| $\sigma_e$ | Uniform permutation on $[n]$ assigned to directed base edge $e$ | Definition 22 | Only one independent permutation is chosen per undirected pair because $\sigma_{\iota(e)}=\sigma_e^{-1}$ |
| $G_n$ | Random $n$-lift with $V_n=V\times[n]$ and $\vec E_n=\vec E\times[n]$ | Definition 22 | Figure 5 uses vertex label $vi$ for $(v,i)$ |
| $B_n=S_nN_n$ | Lift non-backtracking matrix | Eq. 50 | $N_n=N\otimes I_n$, but $S_n$ contains the random fiber permutations |
| $M_e$ | $n\times n$ permutation matrix of $\sigma_e$ | Eq. 54 | $M_{\iota(e)}=M_e^*=M_e^{-1}$ |
| $\underline M_e$ | $M_e-n^{-1}\chi\chi^*$ | Page 34 | This is fiberwise centering, different in dimension from configuration centering |
| $\chi_e$ | Indicator of the directed-edge fiber $\{(e,i):i\in[n]\}$ | Eq. 51 | $\chi$ without $e$ remains the all-ones fiber vector used to define $\underline M_e$ |
| $H$ | Span of $\{\chi_e:e\in\vec E\}$, dimension $r$ | Eq. 51 | Vectors in $H$ are constant on each directed-edge fiber |
| $H^\perp$ | Fiberwise zero-sum vector space, dimension $nr-r$ | Page 31 | Carries all new non-backtracking eigenvalues and no inherited base eigenvalues |
| $\lambda_i$ | New eigenvalues of $B_n$, ordered by decreasing modulus | Eq. 52 | $\lambda_1$ is not the Perron eigenvalue of the whole lift in this section |
| $\rho$ | Fixed strict upper surrogate for $\rho_1$, with $\rho>\rho_1$ | Eq. 67 | Only at the end is $\rho$ taken close enough to $\rho_1$ |
| $c_\rho$ | Constant ensuring $\|(B^*)^k\delta_e\|_1\leq c_\rho\rho^k$ | Eq. 67 | Depends on $\rho$ and the fixed base graph |
| $d_{i,\ell}$ | Degree at a path-boundary vertex in the lift trace count | Page 40 | Reduces to $d$ in the regular case |
| $\delta_e$ | Coordinate unit vector at a base directed edge | Page 39 | Not a small scalar $\varepsilon$ and not a Dirac mass on vertices |

## Recommended reading rule

Before interpreting an equation, identify which of four contexts is active: adjacency reduction, configuration-model moments, trace enumeration, or random lifts. Most apparent symbol contradictions disappear once the context is fixed. The remaining genuine source defects are listed separately in `09-assumptions-and-weak-points.md`.
