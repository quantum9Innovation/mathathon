# Priority comparison for the close-pair transition

November 15, 2026, America/Los_Angeles.

Status: bounded primary-source comparison, not a historical-firstness certificate. The current-round lower proofs were frozen before this report. The current-round probability and complementary upper proofs were not read during this audit.

## Exact claims compared

The cubic model is a uniform simple labelled cubic host with a predetermined set of m marks, followed by addition of one neighbour-duplicate vertex per mark. Its adjacency matrix is [[A,AE],[E^top A,0]]. The lower proof establishes positive-probability failure of the previous collective top law at m of order n^(1/3), and divergence of the top shift divided by sqrt(m/n) when n^(1/3)<<m=o(n). It also gives a lower bound in probability at scale m^2/n when n^(1/4)<<m<<sqrt(n). Fixed-degree weighted and bounded internal-interaction variants are separate extensions.

| Frozen lower proof | SHA256 |
| --- | --- |
| [Cubic proof](../obstruction/proof-v1.md) | cadd1408ff45526a328b78f7b2f063fa599278603e90282c216e364c68280a35 |
| [Weighted extension](../obstruction/weighted-extension-v1.md) | 3ffd9f003e3e4c3d94be96a9ff831f666da815e631eed531cdcbf1ba5d0f33d1 |
| [Pair-scale lower bound](../obstruction/pair-scale-v1.md) | 272cdb331e73e23aecc36685cb62211c9733d50022e438c6e7fa7f5fb18c505a |

No upper estimate, optimal critical distribution or localization statement is certified by these lower proofs. Any matching threshold claim must additionally use an independently reviewed subcritical theorem.

## 1. The graph operation is already known

The full-mark operation E=I is the splitting graph, also the neighbourhood corona with a single isolated vertex at each host vertex. Yang and Rosenfeld's Corollary 3.2 gives the spectrum of [[A,A],[A,0]] as the combined spectra of phi A and -phi^(-1)A, where phi is the golden ratio. Inspection depth: publisher-hosted definition, Corollaries 3.1 and 3.2, the displayed block matrix and its determinant calculation. The sparse-mark model is a partial use of this established operation. The inspected result concerns all vertices, not random distances between a sublinear set of marked labels. [Some spectral invariants of the neighborhood corona of graphs, 2018](https://doi.org/10.1016/j.dam.2018.03.052).

The splitting terminology and definition are also explicit in the abstract of Lu, Ma and Zhang's [Spectra of graph operations based on splitting graph, 2023](https://www.jaac-online.com/article/doi/10.11948/20210446). This second source was screened at abstract level only. Neither the operation nor its full-mark block spectrum should be presented as new.

## 2. Pair resonance and tunnelling are established mechanisms

Alt, Ducatez and Knowles explicitly compare tunnelling amplitudes with spacing between resonant centres, and prove localization by controlling their interactions. The inspected version assumes independent-edge Erdos-Renyi graphs with sqrt(log N) log log N << d <=3 log N. Theorem 1.1 treats the non-Perron spectrum and exponential localization for the indicated outer eigenvalues. Inspection depth: arXiv:2305.16294v2, Sections 1.1 and 1.2, Theorem 1.1, the two-state discussion and equations (1.2) and (1.3). Their proof was not re-audited. These results strongly precede the conceptual use of competing local interactions. They do not supply the prescribed bounded-degree clone model or the n^(1/3) mark-count threshold. [Localized phase for the Erdos-Renyi graph](https://arxiv.org/html/2305.16294v2).

Colin de Verdiere and Truc treat finite perturbations of a regular tree through its Green kernel and finite-support reductions. Their Theorem 4.2 bounds the pure-point spectrum produced by the perturbation. Inspection depth: arXiv:1209.1001v2, setup, regular-tree kernel, compact perturbation reduction, Theorem 4.2 and Section 5, building on the previous audit. This supplies established tree-scattering context. It does not count a growing random collection of defects in a finite host or its competition with the finite constant mode. [Scattering theory for graphs isomorphic to a homogeneous tree at infinity](https://arxiv.org/html/1209.1001v2).

## 3. Current sparse-graph results require model and scale comparisons

Buc-d'Alche and Knowles' April 2026 preprint allows typical degrees of constant order, so degree growth alone is not a sufficient distinction. However, Section 1.2 specifies independent edges with probabilities w_x w_y/(sum_z w_z+w_x w_y). Theorem 5.1 locates large eigenvalues with error of order sqrt(log N/log log N), and Section 4 explicitly notes when the semilocalization estimate is vacuous. Inspection depth: arXiv:2604.11682v1, model, Assumptions 1.1 and 1.2, Theorem 1.9, the concluding error discussion of Section 4, and Theorems 5.1 and 5.2. These hypotheses and errors do not resolve a shrinking displacement near the bounded value d in the dependent splitting model. [Semilocalization for inhomogeneous random graphs](https://arxiv.org/html/2604.11682v1).

Hiesmayr and McKenzie treat constant expected-degree Erdos-Renyi graphs and derive precise spectral information from neighbourhoods of unusually high-degree vertices, together with localization and Poisson edge statistics. Inspection depth: primary arXiv abstract and publisher abstract, not full theorem reconstruction. The current graph has bounded degrees even after unweighted duplication, while that source's extreme states are associated with growing maximum degrees in an independent-edge ensemble. No direct subsumption was established. Its locality methods remain relevant for any future localization or limit-law claim. [The Spectral Edge of Constant Degree Erdos-Renyi Graphs](https://arxiv.org/abs/2309.11007), [published version, 2025](https://doi.org/10.1002/rsa.70011).

The earlier [growing-rank priority audit](../../growing-defects-round-01/priority/PRIORITY-v1.md) continues to apply to abstract effective-matrix and overlap methods. Those methods are not claimed as new by this round.

## Search boundary and assessment

Targeted queries covered random regular graphs with duplicated vertices, neighbourhood duplication, partial splitting, close resonant pairs, two defects on regular trees, sparse-graph tunnelling and spectral outliers. Primary statements were used for the comparisons above. Search misses are not evidence that a mathematical question is open. Papers discovered only through abstracts were not treated as fully excluded precedents.

The plausible distinguishing statement is specific: predetermined partial splitting of a finite random regular host has a change from a collective sqrt(m/n) top displacement to obstruction from close marked pairs at the m^3/n parameter, with a proved lower scale m^2/n in the stated range. The proof combines classical walk lifting, positive Green kernels, a Schur witness and sampling moments. The source comparison did not identify a theorem directly providing this exact finite-host law, but it does not establish historical firstness.

A close-pair eigenvalue witness is substantially weaker than a localization theorem. The top eigenvector need not be shown to concentrate on a particular pair, and the result does not prove a new mobility edge, a universal phase transition across ensembles, a normalized-Laplacian gap law or an algorithmic consequence. These distinctions should remain in any later explanation or manuscript.

The most useful further priority step, if publication is pursued, is a focused citation-chain audit of partial splitting graphs and fixed-degree finite-rank defects, using the final integrated theorem's exact hypotheses. It should be separate from proof acceptance and should not delay recording the present bounded evidence.
