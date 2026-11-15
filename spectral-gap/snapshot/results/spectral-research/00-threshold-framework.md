# A common framework for spectral thresholds

## Status

Interim research framework, 14 November 2026. The four paper dossiers were read as source guides, not as certified proofs. The external theorem statements below were checked against the cited arXiv metadata or downloaded papers. Research priorities are provisional until the independent agents and a broader citation search are complete.

## 1. Four objects that determine a gap

A meaningful spectral gap requires all four of these objects.

1. **An operator.** Examples are adjacency, Laplacian, nonbacktracking, directed adjacency, a block of a group algebra, or a higher-dimensional up-down operator.
2. **A structural subspace $\mathcal T$.** Remove trivial, inherited, symmetry-generated, or rank-forced eigenfunctions, but never call all early-indexed eigenvalues trivial automatically.
3. **An infinite operator $A_\infty$.** It might act on a universal cover, an infinite Cayley graph, a Bloch or Floquet fiber bundle, or a free-product model.
4. **A quantitative question.** One can ask for an outer radius, a one-sided edge, an internal band gap, an eigenvalue edge fluctuation, or spectral measure localization.

For a self-adjoint finite operator $A_N$, a generic relative spectral quantity is

$$
\rho_{\mathrm{rel}}(A_N)=\|Q_N A_N Q_N\|,
$$

where $Q_N$ is the projection onto $\mathcal T_N^\perp$. The target is often $\|A_\infty\|$, but that is not automatic. Sometimes only $\sigma(A_N^{\mathrm{new}})\subseteq \sigma(A_\infty)+[-\varepsilon,\varepsilon]$ is true, with no universal comparison against the entire spectrum. For a nonnormal directed or nonbacktracking operator, normality, pseudospectrum, eigenvalues and singular values require separate treatment.

## 2. Translation dictionary

### Regular graphs

The nonbacktracking operator removes immediate reversals and has branching $d-1$. Its bulk radial threshold is $\sqrt{d-1}$. Ihara-Bass converts an adjacency eigenvalue $\mu$ outside $[-2\sqrt{d-1},2\sqrt{d-1}]$ into a real nonbacktracking root $\lambda$ through

$$
\lambda^2-\mu\lambda+(d-1)=0.
$$

If $|\mu|=2\sqrt{d-1}(1+\delta)$, the larger root has radial excess of order $\sqrt\delta$. This explains why a nonbacktracking additive error gets squared when converted into an adjacency error. See D1 of the local [Bordenave derivation](../../.paper-mastery/friedman-second-eigenvalue-lifts/06-derivations.md).

### Biregular graphs and the second edge

Let $X$ be the n by m biadjacency matrix with row degree $d_1$ and column degree $d_2$, and set $a=d_1-1$, $b=d_2-1$. Nonzero singular values correspond to Ihara-Bass parameters through

$$
\xi^2=x+\frac{ab}{x}+a+b,\qquad x=\lambda^2.
$$

The bulk has $|x|=\sqrt{ab}$ and therefore

$$
\xi_{\pm}=\sqrt{d_1-1}\pm\sqrt{d_2-1}.
$$

This is a genuinely two-sided problem. The lower positive edge is invisible to an ordinary positive $\lambda_2$ formulation, while full row rank of $X$ is governed by the same nonbacktracking bound, provided $a>b$. These are central reconstructible identifications, not research proposals.

### Feng-Li hypergraph adjacency as a singular-value transform

For an $r$-uniform $d$-regular hypergraph, let $X$ be its vertex-hyperedge incidence matrix. Then

$$
A_H=XX^\mathsf{T}-dI.
$$

The Perron eigenvalue is $\sigma_{\max}(X)^2-d=dr-d=d(r-1)$, not $d$. The singular-value bulk above translates into

$$
r-2-2\sqrt{(d-1)(r-1)}
\le \lambda_{\mathrm{bulk}}(A_H)
\le r-2+2\sqrt{(d-1)(r-1)}.
$$

If $d<r$, rectangularity gives at least $|V|-|E|$ forced eigenvalues $-d$, called obvious in the covering literature. A definition of the Ramanujan property may have to exclude both trivial and obvious eigenvalues. This identity does not control tensor spectra or every matrix assigned to a hypergraph.

Dumitriu and Zhu, arXiv:1905.06487v5, Theorem 4.3, already establishes the almost Ramanujan upper bound for the nontrivial Feng-Li adjacency spectrum of uniform random regular hypergraphs under $d\ge r\ge3$. Therefore simply replacing Friedman by those adjacency matrices is not an open leading-order problem.

### Covers and Cayley graphs

For an N-lift, remove functions induced from the base, equivalently the zero-mean fibre complement. For a Cayley graph with symmetric $S$,

$$
A=\sum_{s\in S}\lambda_{\mathrm{reg}}(s).
$$

If $G$ is abelian, its characters give

$$
\lambda_\chi(S)=\sum_{s\in S}\chi(s).
$$

For general groups, the regular representation decomposes into $\rho$-blocks $\sum_s\rho(s)$, with multiplicities $\dim\rho$. Thus a Cayley spectrum, a relative lift spectrum and a Bloch fiber spectrum are all representation-twisted walk matrices. This is a notation-independent source of unity. It does not imply that different random models have the same spectral edge law.

## 3. The threshold-to-rate architecture

The proof template extracted from the dossiers is:

1. **A deterministic lower comparison:** an Alon-Boppana type lower bound identifies a limiting operator or a local obstruction. The relevant condition is not just regularity, but an infinite covering or local limit whose spectral properties can be computed.
2. **A high-moment upper bound:** at suitable walk length, estimate traces of a nonbacktracking or matrix-weighted operator rather than ordinary adjacency powers.
3. **Discard defects before centering:** tangles and locally dangerous subgraphs otherwise dominate high moments despite being rare or having finite probability.
4. **Compress walks:** types, circuit supports and encodings reduce the entropy. The bookkeeping must be reconstructible, not merely plausible.
5. **Recover the actual spectrum:** tangle-free expectations, calibrated trace lengths, side-stepping, spreading or polynomial test functions close the gap between the combinatorial trace and an eigenvalue statement.
6. **Identify the rarest obstruction:** in models with polynomial failure probability, a fixed subgraph $H$ commonly has occurrence scale $N^{-(|E(H)|-|V(H)|)}$, under explicit model and connectivity assumptions. The first obstruction with a sufficiently large local spectral defect gives a candidate exponent.

This last step is sharper than the generic $o(1)$ Ramanujan statement. Friedman and Kohler aim at a fundamental tangle order for random covers. Their dossier records concrete printed errors, so the exponent and its proof must be checked from the repaired argument rather than repeated uncritically.

A major distinction now visible in the recent literature is between polynomial tangle excess and much smaller edge fluctuations. Huang, McKenzie and Yau prove edge rigidity and Tracy-Widom limits for fixed-degree random regular graphs in arXiv:2412.20263v2. Their approximately $69\%$ Ramanujan probability is in the normalized form $\max\{\lambda_2,|\lambda_N|\}\le2$ with $\lambda_1=d/\sqrt{d-1}$. It is not evidence for a universal probability across random-cover models and does not confuse a fixed positive threshold excess with a rescaled $N^{-2/3}$ edge fluctuation.

## 4. Where this breaks

- A lattice torus is locally tree-like only in a bounded-radius sense and has algebraic rather than exponential volume growth. Its gap tends to zero, so $2\sqrt{d-1}$ is not its relevant threshold.
- An irregular adjacency spectrum cannot generally be read from the regular Ihara quadratic. The universal-cover adjacency operator must be computed directly.
- A rank-one or rank-finitely-many perturbation creates discrete outliers without moving the continuous bulk edge. Those outliers should not be misidentified as bulk drift.
- On $\mathbb F_2^r$ with a connection set $S$ of size $d$, $\lambda_2=d-2d_{\min}(C)$, where $C$ is the binary row code of the character-by-generator matrix. Connectivity forces rank $r\le d$, so fixed $d$ bounds the group size for connected Cayley graphs on these groups. This is an exact obstruction, not a shortage of techniques.
- Fourier characters on finite abelian groups are one-dimensional. Nonabelian random walk theory instead needs matrix blocks, and a scalar Chernoff bound is not the complete answer.
- Nonbacktracking nonnormality defeats naive adjacency Hermitian norm arguments. In directed graphs, eigenvalue moduli and singular values answer different questions.

## 5. Provisional research priorities

### P1. Quantitative relative spectrum inside internal universal-cover gaps

Bordenave and Collins, arXiv:1801.00876v4, Theorem 2, is stronger than the regular $2\sqrt{d-1}$ bound. It gives Hausdorff convergence in probability of the new spectrum of symmetric random lifts to the universal-cover spectrum, whose bands may have internal gaps. Huang and Xu, arXiv:2610.37463v1, then provides quantitative Green-function control away from singular energies and delocalization on small scales.

The candidate missing link is a model-sensitive rate for entering or approaching each internal gap, possibly dominated by tangles near that band edge. A concrete theorem would have explicit band-edge hypotheses and describe how the choice of polynomial test functions depends on the edge. This is the best conceptual bridge, but novelty remains unverified. Existing quantitative strong convergence results could settle part of it.

### P2. Bloch band competition and exact finite-quotient gaps

For a finite cyclic quotient, Bloch decomposition turns the gap into a nearest-lattice-point problem near competing critical points of dispersion functions. A definite target is an explicit anisotropic lattice or hexagonal family with a change in the winning band or rate exponent. This is mathematically tractable before any general theory is attempted.

The right reference point is the periodic spectral-edges literature, not Friedman alone. Faust and Sottile, arXiv:2206.13649v5, prove critical-point bounds and establish the spectral-edges conjecture for some $\mathbb Z^2$-periodic graphs. The exact target must be checked against further work on periodic quotients and discrete magnetic Laplacians. No open-problem claim is made for the basic Bloch translation itself.

### P3. Finite-degree defects and the relation of outliers to tangle exponents

On the infinite $d$-regular tree with a single center of degree $\Delta>d$, a radial-wave candidate with $x_{j+1}=qx_j$ on every regular branch satisfies $\nu=q^{-1}+(d-1)q$ on those branches and $\nu=\Delta q$ at the center. Eliminating $q$ gives

$$
q=(\Delta-d+1)^{-1/2},\qquad
\nu=\frac{\Delta}{\sqrt{\Delta-d+1}}.
$$

The value $\nu>2\sqrt{d-1}$ when $\Delta>2d-2$. At that condition $(d-1)q^2<1$, so the candidate is square-summable over the geometric number of radial vertices. This supports a genuine outlier above the regular-tree bulk rather than only an interior candidate. The natural research problem is to use this or a finite tangle computation to predict which defect wins, in which graph distribution, and with what occurrence probability. Separate bulk stability from outlier existence. Finite rank perturbations and positive-density degree changes must not be conflated.

### P4. Hypergraph spectra relative to inherited and obvious modes

The most defensible replacement for a bare $d-\lambda_3$ study is a relative singular-value question on $XX^\mathsf{T}$, distinguishing old, Perron and rectangular-nullspace eigenvalues. A possible strong program is to transfer random-lift strong convergence to explicitly defined hypergraph covers, or to establish tangle-controlled rates for the Feng-Li adjacency bulk.

Foundations already include the almost Ramanujan bound in Dumitriu-Zhu and right-sided Ramanujan 2-cover existence in Song-Fan-Miao, arXiv:2310.01771v2, Theorem 1.6. Song-Fan-Miao also has a universal-cover lower bound for general $d$-regular hypergraphs, Theorem 1.5. A claim that hypergraph covering spectra are unexplored would therefore be false. The remaining test is whether the matrix-valued permutation proof for random incidence lifts can be used literally or needs a new argument, and whether its induced hypergraph cover models match.

### P5. Cayley character or representation blocks at the optimal degree-scale frontier

For abelian Cayley graphs, exploit exact character sums rather than generic matrix concentration. Hermon and Olesker-Taylor, arXiv:2102.02801v2, Theorem E, supplies relaxation-time order in broad parameter ranges and identifies a formula of scale $|G|^{2/k}$ for $k$ random generators. The remaining directions should be explicit outside those ranges, or concern rescaled full spectra and larger generator regimes rather than another statement of Alon-Roichman.

For nonabelian groups, the most interesting target is a tangle or strongly-representation version of the matrix-valued lift methods under symmetry restrictions. This is high risk because reduced randomness changes both coefficient cancellation and the limiting model. A rigorous lower bound or exact saturated example should come before a conjecture.

### P6. Local spectral expansion on Cayley high-dimensional complexes

Dikstein, Liu and Wigderson, arXiv:2411.08839v1, constructs explicit abelian Cayley high-dimensional expanders over $\mathbb F_2^n$ using sparse Grassmannian and Johnson structures. Their notion of local spectral expansion concerns links, not merely the second adjacency eigenvalue of a single graph.

The promising connection is to reuse character coding decompositions simultaneously for every link, and then compare nonlinear or coboundary expansion with the ordinary spectral gap. This is not a gap in the sense that Cayley high-dimensional expansion is unknown. It is a possible compatibility bridge between three active vocabularies: coding theory, high-dimensional expansion, and relative spectra.

## 6. What would count as convincing progress

- An exact computation of a previously unrecognized winning band or defect.
- A proof that a known general theorem specializes to a nontrivial new hypergraph or constrained-lift model, with every model requirement checked.
- A lower bound showing that a proposed optimal threshold cannot be attained in the selected symmetry class.
- A polynomial probability formula tied to the minimal spectral obstruction, not an assertion based only on simulations.
- Reproducible exact enumeration or spectra that disprove a naive generalization.
- A citation map establishing which statement is truly absent after comparison with modern strong convergence and periodic-operator literature.

No mathematical certification, exhaustive novelty verification or completed swarm judging is implied by this interim map.
