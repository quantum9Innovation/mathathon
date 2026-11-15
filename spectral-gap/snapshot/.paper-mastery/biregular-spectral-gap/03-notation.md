# Notation and collision map

## Housekeeping symbols used only in this dossier

For compact derived formulas, write

$$a=d_1-1,\qquad b=d_2-1,\qquad \rho=\sqrt{ab},\qquad \tau=(ab)^{1/4}.$$

Here $a\geq b>0$ under the paper's ordering. The dominant non-backtracking magnitude is $\rho$, and $\tau$ is the radius appearing in Theorem 3. These four abbreviations are **Derived** notation. They are not used uniformly in the paper.

The paper itself uses $\alpha$ both for $\sqrt{a}/\sqrt{b}$ in $\mathbf 1_\alpha$ and for $(ab)^{1/4}$ after Equation 26. The dossier avoids that collision.

## Core graph and matrix notation

| Symbol | Meaning and type | Introduced | Common confusion |
| --- | --- | --- | --- |
| $V_1,V_2$ | Left and right independent vertex sets | Section 1.1, page 2 | Degrees are constant within each side, not globally |
| $n,m$ | $n=\lvert V_1\rvert$, $m=\lvert V_2\rvert$, usually $n\leq m$ | Section 1.1 | $m/n=d_1/d_2$ is fixed by regularity |
| $d_1,d_2$ | Degrees on $V_1,V_2$ | Section 1.1 | Fixed throughout the main limit. Usually $d_1\geq d_2\geq3$ |
| $d$ | $\max\{d_1,d_2\}=d_1$ in the ordered case | Section 4 | In the application to frame graphs, $D$ can instead be a whole degree matrix |
| $G\sim\mathcal G(n,m,d_1,d_2)$ | Uniform simple bipartite biregular graph | Section 1.1 | This is not the unconditioned configuration multigraph |
| $E$ and $\lvert E\rvert$ | Graph edge set and size, with $\lvert E\rvert=nd_1=md_2$ | Section 1.1 | In path counting, $\mathscr E$ counts distinct edges of one circuit instead |
| $\vec E$ | All oriented edges, with $\lvert\vec E\rvert=2\lvert E\rvert$ | Section 2 | One undirected edge contributes two orientations |
| $X$ | Biadjacency matrix in $\mathbb R^{n\times m}$ | Equation 1, page 2 | Rank conclusion concerns full row rank $n$, not full rank $m$ |
| $A$ | $\begin{pmatrix}0&X\\X^*&0\end{pmatrix}$ in $\mathbb R^{(n+m)\times(n+m)}$ | Equation 1 | In matrix completion, $A,B$ also name row and column subsets |
| $\eta$ | Second adjacency eigenvalue $\lambda_2(A)$, equivalently second singular value of $X$ | Section 1.1 | For a bipartite graph this is not a signed-only ordering ambiguity since the negative partner is $-\eta$ |
| $\eta_{\min}^{+}$ | Smallest strictly positive adjacency eigenvalue | Theorem 4(ii) | It is not $\lambda_{\min}(A)$, which is negative |
| $\sigma(M)$ | Eigenvalue spectrum of $M$, with multiplicity when used carefully | Section 1 | $\sigma(A)$ is real, while $\sigma(B)$ is generally complex |
| $\xi$ | An adjacency eigenvalue or nonnegative singular value in the transfer calculation | Equations 4 to 8 | $y=\xi^2$ loses the sign, but $\pm\xi$ give the same non-backtracking roots |
| $B$ | Non-backtracking matrix in $\mathbb R^{2\lvert E\rvert\times2\lvert E\rvert}$ | Section 2 | It is not the adjacency matrix of the original graph and need not be symmetric |
| $\lambda$ | Candidate non-backtracking eigenvalue | Section 2 | In Appendix A, $\lambda_i(X)$ means ordering in absolute value |
| $\mathbf1_\alpha$ | Block vector $(\mathbf1,\alpha\mathbf1)$, with $\alpha=\sqrt{a}/\sqrt{b}$ | Section 2 | $\mathbf1_\alpha$ and $\mathbf1_{-\alpha}$ give the dominant eigenpair structure |
| $L$ in Section 6 | Symmetrized Markov matrix $D_G^{-1/2}AD_G^{-1/2}$ | Section 6.2 | It is not the normalized Laplacian $\mathcal L=I-L$ |
| $P$ | Markov matrix $D_G^{-1}A$ | Section 6.2 | $P$ and $L$ have the same real spectrum but different eigenvectors |
| $D(H),R(H)$ | Frame degree matrix and its row normalization | Section 6.1 | $D(H)$ is distinct from the diagonal vertex-degree matrix $D_G$ |
| $p_i,n_i$ | Class proportion and class size $np_i$ in a frame graph | Section 6.1 | Frame balance requires $p_iD_{ij}=p_jD_{ji}$ |

## Random matching and path decomposition

| Symbol | Meaning and type | Introduced | Common confusion |
| --- | --- | --- | --- |
| $\vec E_1,\vec E_2$ | Labeled half-edges on the two sides, each of cardinality $\lvert E\rvert$ | Section 4.1 | Half-edge labels remember configuration-model isomorphisms |
| $\pi$ | Uniform bijection or permutation matching half-edges | Section 4.1 | $\pi$ indexes randomness, not adjacency eigenvectors |
| $M$ | Symmetric permutation-matching matrix, with $B=MN$ | Equation 9, page 10 | $M$ is random. $N$ is deterministic |
| $N$ | Matrix selecting distinct half-edges at a common vertex | Section 4.1 | $N$ excludes immediate reversal |
| $S$ | Rank-two block-average matrix subtracted from $B$ | Section 5.2, page 14 | $\operatorname{range}(S)$ is the dominant span, not $\ker S$ |
| $\bar B$ | $B-S$, an almost-centered operator | Section 5.2 | Individual row supports keep it from being an ordinary independent-entry matrix |
| $S',\bar M$ | $S'=S$ with degree factors removed and $\bar M=M-S'$ | Section 5.2 | $\bar B=(M-S')N=\bar MN$ |
| $B^\ell$ | Ordinary $\ell$th matrix power | Section 5 | Not the restricted path matrix $B^{(\ell)}$ |
| $B^{(\ell)},\bar B^{(\ell)}$ | Matrices whose entries sum only over tangle-free paths | Equation 16 | Parentheses around $\ell$ mark restriction, not differentiation |
| $T$ | Rank-two projection-type matrix used in Lemma 6 | Section 5.1 | Do not confuse with the tangle path family $T^{\ell,j}$ |
| $\ell$ | Logarithmic path and neighborhood scale | Sections 4 and 5 | Eventually $\ell=\lfloor c\log n\rfloor$ with $c<1/32$ |
| $k$ | Moment exponent | Section 5.8 | Eventually $k=\lfloor(\log n)^{1/3}\rfloor$. In Section 1.2, $k$ also means lift multiplicity |
| $\Gamma_{ef}^{\ell}$ | Non-backtracking sequences of $2\ell+1$ half-edges from $e$ to $f$ | Definition 2 | These sequences need not all be realized as graph edges |
| $F_{ef}^{\ell}$ | Tangle-free subset of $\Gamma_{ef}^{\ell}$ | Definition 3 | Path segments may each be tangle-free while their union is tangled |
| $T_{ef}^{\ell,j}$ | Overall tangled path whose three split pieces are tangle-free | Definition 4 | The $j$ in the suffix belongs to the split position |
| $R^{\ell,j}$ | Remainder matrix after tangle-free decomposition | Equation 15 | It is not the frame Markov matrix $R(H)$ |
| $\Vert C\Vert $ | Euclidean vector norm or operator spectral norm | Throughout | $\Vert C\Vert _F$ is the Frobenius norm instead |

## Circuit counting

| Symbol | Meaning | Introduced | Watch for |
| --- | --- | --- | --- |
| $\gamma$ | A walk or concatenated circuit | Section 5 | A circuit may have multiple distinct traversals of one graph edge |
| $\gamma_j$ | One of $2k$ tangle-free segments | Sections 5.1 and 5.4 | Alternating transposes reverse alternate segments |
| $\mathscr V$ | Number of distinct vertices in a circuit | Section 5.4 | It is not total vertex count of the ambient graph |
| $\mathscr R$ | Number of distinct circuit vertices in $V_2$ | Section 5.4 | $L=\mathscr V-\mathscr R$ is a useful derived abbreviation |
| $\mathscr E$ | Number of distinct undirected edges in a circuit | Section 5.4 | It is not total traversal count |
| $b_\mathcal C$ | Inconsistent multiplicity-one edges | Lemma 14 | Distinct from the degree abbreviation $b$ in this dossier |
| $\mathscr E_1$ | Consistent multiplicity-one edges entering Lemma 7 | Sections 5.3 and 5.8 | A centering-induced penalty |
| $\chi$ | $\mathscr E-\mathscr V+1$ for connected circuit support | Lemma 9 | **Appendix A prints $\lvert V\rvert-\lvert E\rvert+1$, which is incompatible with Lemma 9 and standard tree excess** |
| $C_{\mathscr V,\mathscr E}^{\mathscr R}$ | Number of tangle-free-segment circuits in each class | Lemma 9 | Counts choices of ordered actual vertices before half-edge choices |
| $D_{\mathscr V,\mathscr E}^{\mathscr R}$ | Analogous remainder-circuit count | Lemma 10 | Its encoding splits each tangled path into three pieces |
| $I_{\mathscr V,\mathscr E}^{\mathscr R}$ | Half-edge labeling count | Lemma 11 | Distinct from the trace contributions $I_1,I_2,I_3$ |
| $\psi$ | $\mathscr R-\mathscr E/2$ | Section 5.6 | Signed imbalance. The printed upper bound does not explicitly claim an absolute-value bound |
| $(p_i,q_i,r_i)$ | Old-tree endpoint, new-tree length, non-tree endpoint triple | Section 5.4 | Only $q_i$ is directly a length. The other two encode endpoints, so lengths come from the discovered tree |
| $\mathcal T_\gamma$ | First-discovery spanning tree of a circuit support | Section 5.4 | Non-tree edges correspond to independent cycles |

## Application notation

| Symbol | Meaning | Location | Collision warning |
| --- | --- | --- | --- |
| $K$ | Number of classes | Section 6 | $K_G$ is Grothendieck's constant, not a class count |
| $\kappa$ | Common integer degree multiplier | Theorem 19 | Scaling $D$ leaves frame Markov matrix $R$ fixed |
| $\mathcal C_i=[d_i,k_i,\delta_i]$ | Local code length, dimension, and minimum distance | Section 7 | The third parameter is a distance, not a relative distance |
| $\delta$ | Tanner-code minimum distance | Theorem 21 | In Section 8, $\delta$ becomes a noise level |
| $\gamma_2(Y)$ | Factorization norm | Section 8.1 | $\gamma$ elsewhere is a path |
| $\circ$ | Hadamard entrywise product | Section 8.2 | Not function composition there |
| $\nu(R)$ | Sign nuclear norm | Theorem 24 proof | Related to $\gamma_2$ through $K_G$ |
| $E(A,B)$ in Section 8 | Number of sampled graph edges between vertex subsets | Theorem 24 proof | Distinct from expectation $\mathbb E$ and edge-set notation |
| $u,v$ in sign matrices | Intended to be sign vectors of lengths $n,m$ | Theorem 24 proof | The printed domain $u,v\in\{-1,1\}^{n\times m}$ is dimensionally wrong |
| $\epsilon_{ij}$ | Additive observation noise | Section 8.3 | Unrelated to the vanishing spectral errors $\epsilon_n,\epsilon_n',\epsilon_n''$ |

## Appendix table and visual cross-reference

Appendix A on page 36 is a compact symbol table, not a theorem summary. It is useful for $A,B,X^*,\eta,\Gamma,F,T$, and norms, but three cautions matter:

1. Its definition of $\chi$ has the sign reversed relative to the body of the paper.
2. Its path-length wording suppresses the half-edge convention. Definition 2 gives the precise $2\ell+1$ half-edges corresponding to $\ell+1$ graph edges.
3. The same letters are repurposed in applications. Use the section-specific rows above rather than assuming one global meaning.
