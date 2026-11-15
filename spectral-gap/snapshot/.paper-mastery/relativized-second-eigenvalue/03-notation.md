# Notation

**Label convention.** Definitions under **Paper** follow the source. The shorthand $R=\rho(H_B)$ used in derived comments is introduced here solely to make formulas shorter. The source also uses $\rho^{1/2}(H_B)$ for $\rho(H_B)^{1/2}$ and $\rho^k(H_B)$ for $\rho(H_B)^k$.

## Core objects

| Symbol | Meaning | Type or dimension | Introduced | Common confusion and related symbols |
| --- | --- | --- | --- | --- |
| $B$ | Fixed base graph | Finite graph, often regular and connected | Throughout | $G$ is the random covering graph, not the base |
| $G$ | Random or arbitrary covering graph | Typically $G\in\mathcal C_n(B)$ | Section 0.1 | A letter $G$ can also denote an abstract probability-space element in side-stepping |
| $\pi:G\to B$ | Covering map of degree $n$ | Local graph isomorphism | Sections 0.1, 1.1.3 | $n$ is degree, not the number of vertices of $B$ |
| $\mathcal C_n(B)$ | Broder-Shamir model | Probability space of permutation assignments and induced covers | Definitions 1.1.11 and 1.1.22 | Model-specific, not every random-cover distribution |
| $V_G,E_G,E_G^{\mathrm{dir}}$ | Vertices, undirected edges, directed edges | Sets | Definition 1.1.3 | Half-loops require special convention care |
| $t_G,h_G,\iota_G$ | Tail, head, opposite-edge involution | Maps on directed edges | Definition 1.1.2 | $e^{-1}=\iota_G(e)$, not matrix inversion |
| $A_G,D_G$ | Adjacency and degree matrices | $|V_G|\times|V_G|$ | Sections 0.1 and 1.1.2 | For regular $G$, $D_G=dI$ |
| $\lambda_i(G)$ | Ordered adjacency eigenvalues | Real scalars, $\lambda_1\ge\cdots$ | Equation (0.1) | Usually $\lambda$ without index denotes one eigenvalue in the Ihara quadratic |
| $\operatorname{Spec}_B^{\mathrm{new}}(A_G)$ | New adjacency spectrum | Multiset of size $(n-1)|V_B|$ for a connected finite base | Definition 1.1.16 | Old spectrum has one copy of the base spectrum, not $n$ copies |
| $\rho_B^{\mathrm{new}}(A_G)$ | Largest absolute new adjacency eigenvalue | Nonnegative real | Section 0.1 | Do not confuse with $\rho(H_G)$, the full Hashimoto radius |
| $H_G$ | Hashimoto matrix | $|E_G^{\mathrm{dir}}|\times|E_G^{\mathrm{dir}}|$ | Definition 1.1.9 | Rows and columns are directed edges, not vertices |
| $\mu_1(G),\mu_i(G)$ | Dominant and remaining Hashimoto eigenvalues | Complex scalars with $\mu_1>0$ | Section 0.2.3 | $\mu_i$ for $i>1$ has no fixed ordering |
| $\operatorname{Spec}_B^{\mathrm{new}}(H_G)$ | New Hashimoto spectrum | Multiset on fibrewise-zero functions on directed edges | Definition 1.1.18 | The side-stepping argument zeroes out old eigenvalues and tangle cases |
| $\rho(H_G)$ | Full Hashimoto spectral radius | Nonnegative real | Definition 0.2.4 | This is not interchangeable with $\rho_B^{\mathrm{new}}(H_G)$, see Section 3.3 caution |
| $R$ | Dossier shorthand for $\rho(H_B)$ | Fixed real greater than $1$ in core cases | Derived shorthand | Not a symbol systematically used by the paper |
| $\rho^{1/2}(H_B)$ | Paper shorthand for $R^{1/2}$ | Positive real threshold | Definition 1.2.4 | It is not $\rho$ applied to $H_B^{1/2}$ |
| $\widehat B$ | Universal cover of $B$ | Infinite connected graph in general | Section 0.2.2 | For $d$-regular $B$, $\rho(A_{\widehat B})=2\sqrt{d-1}$ |
| $\chi(\psi)$ | Euler characteristic | Combinatorial scalar | Sections 0.2.2 and 2.2.1 | No-half-loop formulas use $|V_\psi|-|E_\psi|$ |
| $\operatorname{ord}(\psi)$ | Graph order, $-\chi(\psi)$ | Usually integer, indexing $1/n$ exponents | Definition 1.2.3 | Trees have order $-1$ despite the paper's erroneous Euler-characteristic sign for trees |
| $\operatorname{ord}(B)$ | Base order | Fixed positive integer in much of Chapter 2 | Chapter 2 | Negative Euler characteristic means positive order |

## Walks, forms, and certificates

| Symbol | Meaning | Type or domain | Introduced | Common confusion |
| --- | --- | --- | --- | --- |
| $w$ | Walk $(v_0,e_1,\ldots,e_k,v_k)$ | Finite walk in $B$ or $G$ | Definition 1.1.6 | Non-backtracking and strictly non-backtracking closed differ at the wraparound edge |
| $w^{-1}$ | Reverse walk with opposite directed edges | Walk | Definition 1.1.6 | Not a reciprocal function |
| $\operatorname{Graph}(w)$ | Subgraph traced by $w$ | Subgraph of the ambient graph | Definition 1.3.1 | Depends only on visited vertices and edges, not multiplicities |
| $\mathrm{SNBC}$ | All strictly non-backtracking closed potential walks | Walk collection | Example 2.3.6 | Its modified trace is $\operatorname{Tr}(H_G^k)$ |
| $(w,\mathbf t)$ | Potential walk with trajectory | $w$ in $B$, $t_i\in\{1,\ldots,n\}$ | Definition 2.3.1 | Bold vector arrows denote indexed tuples, not geometric vectors |
| $P(w,\mathbf t)$ | Probability the potential walk is attained | Real in $[0,1]$ | Definition 2.3.1 | $\mathcal E_{\mathrm{symm}}$ sums this over trajectory symmetries |
| $a_e,b_v$ | Numbers of used edges over $e$ and distinct labels over $v$ | Nonnegative integers | Definition 2.3.3 | Their totals are $|E|$ and $|V|$ of the traced graph |
| $\mathcal E_{\mathrm{symm}}(w,\mathbf t)_n$ | Symmetry-grouped attainment weight | Real, of leading order $n^{\chi}$ | Definition 2.3.7 | Exact factorial formula is Proposition 2.3.8 |
| $\mathcal W$ | Walk collection | Symmetric, size-invariant SNBC collection | Definition 2.3.5 | $\operatorname{WalkSum}(\mathcal W,k,n)$ is an expectation |
| $\operatorname{WalkSum}_{<r}$ | Walk sum restricted to order below $r$ | Real function of $k,n$ | Definition 2.3.11 | This truncation is in order, not walk length |
| $\mathcal T=(T,\gamma_V,\gamma_E,L)$ | Type: skeleton, orderings, and lettering | Finite combinatorial datum | Definition 2.3.14 | $T$ is the underlying type graph, $\mathcal T$ includes extra information |
| $\mathcal F$ | Form of a type | Variable lengths plus base walks on type edges | Definition 2.3.15 | Infinitely many forms can share one type |
| $\mathrm{VLG}(T,\mathbf k)$ | Realization with edge $e$ replaced by a path of length $k_e$ | Graph | Definition 1.1.19 | Longer prescribed paths lower the dominant spectral radius under componentwise lengthening |
| $\operatorname{Types}[r]$ | Finitely many types of order below $r$ | Finite set | Proposition 2.3.16 | $r$ is an order cutoff, not a matrix dimension |
| $\mathbf k$ | Beaded-path lengths | $\mathbb Z_{\ge1}^{E_T}$ in certified sums | Sections 2.3 and 2.4 | Scalar $k$ also means walk length |
| $\mathbf m$ | Type-edge traversal multiplicities | Positive integer vector | Sections 2.1.1 and 2.4.5 | Weighted length is $\mathbf m\cdot\mathbf k=k$ |
| $\mathrm{CertTr}_{<r}(G,k)$ | Truncated certified trace | Nonnegative integer | Definitions 1.4.1 and 2.4.27 | Counts SNBC $k$-walks with order below $r$ and traced Hashimoto radius below $R^{1/2}$ |
| $\mathrm{HasTangle}_{r,B}$ | Graphs containing a $B$-tangle of order below $r$ | Event in $\mathcal C_n(B)$ | Notation 1.5.1 | $\mathrm{TF}_{r,B}$ is its complement |
| $\mathbb I_{\mathrm{TF}(r,B)}$ | Indicator of tangle-free event | $0$ or $1$ | Notation 1.5.1 | Its expectation is not the same as conditioning |
| $\eta_{\mathrm{fund}}(B)$ | Fundamental order | Least order of a strict feasible tangle | Definition 2.4.8 | Some prose calls it fundamental power. The printed universal lower bound has a counterexample |

## Functions, expansions, and side-stepping

| Symbol | Meaning | Type or domain | Introduced | Common confusion |
| --- | --- | --- | --- | --- |
| $P_i(k)$ | Degree-$i$ coefficient in $1/n$ expansion | Function of walk length $k$ | Definition 1.3.7 | It need not be polynomial in $k$ |
| $p_i(\mathbf a,\mathbf b)$ | Expansion polynomial of a potential walk | Polynomial in edge and vertex counts | Definition 2.3.9 | Distinct from $P_i$, which sums over walk classes |
| $p_{\ell,i}(k)$ | Polynomial multiplying $\ell^k$ in a coefficient | Polynomial | Lemma 2.6.7 | First nonzero index determines an occurrence exponent |
| $\mathrm{err}(k,n)$ | Remainder after order-$r$ truncation | Function of $k,n$ | Definition 1.3.7 | Bounds enlarge with $r$, $B$, and sometimes $\varepsilon$ |
| $P(k)=s(k)+e(k)$ | $B$-Ramanujan decomposition | $s=\sum_{\mu\in\operatorname{Spec}(H_B)}p_\mu(k)\mu^k$ | Definition 1.3.6 | Source writes "principle part" for $s$ |
| $g_1*g_2$ | Additive convolution | $(g_1*g_2)(k)=\sum_{j=0}^k g_1(j)g_2(k-j)$ | Definition 2.2.5 | Weighted and truncated variants use different constraints |
| $(g_1*\cdots*g_s)_{\mathbf m}^{\mathbf k_0}$ | Truncated weighted convolution | Sum over $\mathbf m\cdot\mathbf k=k$ and $\mathbf k\ge\mathbf k_0$ | Definition 2.2.12 | Check positivity conventions before using printed closed forms |
| $L$ | Finite set of dominant real bases | Usually eigenvalues of $H_B$ above the critical threshold | Definition 2.6.4 | It is not the covering graph $L$ used in tangle discussions |
| $\ell$ | Element of $L$ | Real base | Lemma 2.6.7 | Distinct from adjacency eigenvalue $\lambda$ and Hashimoto eigenvalue $\mu$ |
| $\tau_0,\tau_1$ | Critical disk and outer spectral bounds | Positive reals with $\tau_0<\tau_1$ in the abstract setup | Definition 2.6.4 | Section 2.7 prints inconsistent powers. Do not copy that parameter list literally |
| $S$ | Shift in $k$ | $(Sf)(n,k)=f(n,k+1)$ | Section 2.6.1 | Elsewhere $S$ is a modulus for mod-$S$ functions |
| $Q(S)$ | Polynomial in the shift | Finite operator | Proposition 2.6.1 | $Q(S)\mu^k=Q(\mu)\mu^k$, with $k$ as the shifted variable |
| $\mathrm{Near}_n(\ell,\delta)$ | Expected number of $\mu_i$ near $\ell$ | Nonnegative random-scale expectation | Definition 2.6.6 | Not itself a probability |
| $\mathrm{Exception}_n(\delta,\varepsilon)$ | Event of an outlier away from all $\ell\in L$ | Event | Definition 2.6.6 | $\mathrm{AbsoluteException}$ includes outliers near $L$ as well |
| $\gamma$ | Spreader ratio or abstract count bound | Positive real | Definition 2.6.4 and Section 3.2.1 | Meaning depends on section |
| $\Omega,\xi$ | Fixed graph and label specialization | Potential graph event | Section 2.5.1 | $\Omega$-types retain all of $\Omega$ and add walk skeleton data |
| $m!_{\mathrm{odd}}$ | $(m-1)(m-3)\cdots3\cdot1$ for even $m$ | Odd factorial | Proposition 2.3.8 | Called double factorial in other notation, but not the ordinary factorial |
| $\bmod S$ polyexponential | Different polyexponential formula on each residue class | Function on nonnegative integers | Section 3.5.1 | The same $S$ letter is unrelated to the shift operator |

## Dimensional checks to retain

1. If $B$ has $N$ vertices and $G\to B$ has degree $n$, then $|V_G|=nN$, the old adjacency space has dimension $N$, and the new adjacency space has dimension $(n-1)N$.
2. $\operatorname{Tr}(H_G^k)$ is a nonnegative integer for each realized $G$ and each positive integer $k$.
3. $\mathcal E_{\mathrm{symm}}$ scales like $n^{|V|-|E|}=n^\chi$ when all edge and vertex counts are fixed.
4. $\operatorname{Tr}(A_G^k)-\operatorname{Tr}(A_B^k)$ correctly subtracts one copy of the old spectrum. Multiplying the second trace by $n$ would be a dimension error.
5. In a $B$-Ramanujan error bound, $R^{k/2}$ is exponential in $k$, not in $n$ or the number of vertices of $G$.
