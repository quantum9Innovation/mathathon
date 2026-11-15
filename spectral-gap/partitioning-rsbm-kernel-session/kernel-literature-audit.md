# Primary-source audit for the prescribed planted eigenvalue

Checked against accessible primary statements on 2026-11-15. The derived even-block-size proof is in `meszaros-even-block-proof.md`; the entries below identify what was already known and what cannot be imported unchanged.

## 1. The usable finite-field input

András Mészáros, *The distribution of sandpile groups of random regular graphs*, [arXiv:1806.03736v4](https://arxiv.org/pdf/1806.03736v4), Theorem 1.6, PDF p. 3, proves a sum-over-inputs maximum-atom mixing estimate for adjacency matrices that are sums of `d>=3` independent uniform perfect matchings on **even** `n`. It holds for every fixed finite abelian group `V`; there is no condition that the prime avoid `d` in the mixing theorem itself. For `V=F_p` with odd `p`, its tensor restriction is vacuous. The theorem is stronger than merely a bound on the probability of one singularity event, and it supports the two-block calculation in the companion proof.

Hoi Nguyen and Melanie Matchett Wood, *Cokernels of adjacency matrices of random r-regular graphs*, [arXiv:1806.10068v2](https://arxiv.org/pdf/1806.10068v2), Section 4, proof of Theorem 1.6, PDF p. 8, make explicit the needed model transfer. They cite Janson (1995), Theorem 11, and Molloy–Robalewska–Robinson–Wormald (1997), Theorem 3. The latter paper's [publisher abstract](https://doi.org/10.1002/(SICI)1098-2418(199705)10:3%3C305::AID-RSA1%3E3.0.CO;2-%23) states mutual contiguity for every fixed `r>=3` between uniform simple regular graphs on an even vertex set and unions of disjoint random perfect matchings.

## 2. Standard nonsingularity is not the desired model or shift

Jiaoyang Huang, *Invertibility of adjacency matrices for random d-regular graphs*, [arXiv:1807.06465v2](https://arxiv.org/pdf/1807.06465v2), Theorem 1.3 and Remark 1.4, proves polynomial failure bounds for nonsingularity of the **unshifted** adjacency matrix of fixed-degree `d>=3` random regular directed or undirected graphs. In the undirected configuration model the displayed exponent is `min{1/8,(d-2)/(5d-6)}`. This statement alone concerns neither a deterministic nonzero shift nor the planted block-conditioned ensemble. Its source is useful as a methodological precedent, but cannot simply be applied to `A-(d1-d2)I` in the RSBM.

## 3. The Zhu–Zhu simplicity statement has an assumption gap in its citation

Xiangyi Zhu and Yizhe Zhu, *Non-backtracking eigenvalues and eigenvectors of random regular graphs and hypergraphs*, [arXiv:2312.03300v3](https://arxiv.org/abs/2312.03300v3), also available from the [journal primary page](https://www.sciencedirect.com/science/article/abs/pii/S0012365X26004747), says in its introduction that efficient exact recovery for all fixed `d1>d2>0` remains open. Its Lemma 9.1 nevertheless states, without a gap hypothesis in that lemma, that `d1+d2` and `d1-d2` have multiplicity one with high probability; its proof refers to Brito et al., Section 4.

That citation does not establish the all-parameter assertion. Brito et al., [*Recovery and Rigidity in a Regular Stochastic Block Model*](https://arxiv.org/abs/1507.00930), Section 4, uses even `d1` and inherits its degree assumptions; it obtains old eigenvalues and controls new eigenvalues by the regular-tree edge, which only forces simplicity of the planted eigenvalue under a separating gap. The inconsistency is a source-assumption issue, not an all-regime theorem that can be claimed as a new proof. The companion finite-field proof uses Mészáros directly and independently of this lemma.

## 4. Current random-regular and random-lift results

Yukun He, Jiaoyang Huang, Xiaoyu Wang, [*Bulk universality of random regular graphs*, arXiv:2610.08127v1](https://arxiv.org/html/2610.08127), 2026-10-06: the main theorem gives fixed-energy microscopic point-process convergence to `Sine_1` for **uniform simple** fixed-degree `d>=3` random regular graphs at every energy strictly in the Kesten–McKay bulk. It has no RSBM conditioning in its statement and does not state a polynomial convergence rate for the point process. Its Theorem 1.2 gives polynomial mixed-fourth-moment control for all bulk eigenvector selections. A normalized planted sign vector has scaled fourth moment exactly `1`, versus the Gaussian fourth moment `3`, so the RSBM with a bulk planted eigenvalue lies in the exceptional set of this latter uniform-RRG theorem.

Jiaoyang Huang and Ruizhe Xu, [*Local Law and Eigenvector Delocalization for Random Lifts*, arXiv:2610.37463v1](https://arxiv.org/html/2610.37463), 2026-10-27: the base graph is fixed, connected, **simple**, and has minimum degree at least three. The local-law scale is `(log N)^C/N`, away from singular energies. Theorem 1.2 gives bulk interval counting at this scale and Theorem 1.3 eigenvector delocalization; conditioned on their locally tree-like class they have arbitrary polynomial probability, while Proposition 2.1 places a uniform random lift in that class with error `O(N^{-(1-c)})`. These conclusions do not exclude a collision of one new eigenvalue with one old bulk eigenvalue. Nor is the two-vertex quotient with loops/parallel edges automatically the simple base graph required in the theorem.

## 5. Why unconditional RRG theorems do not transfer by conditioning

This calculation is elementary and is included as a derived obstruction. Let `d=d1+d2`, fix the balanced planted split with blocks of size `N`, and consider the ordinary `d`-regular pairing model on `2N` vertices. The event `E_sigma` that every vertex has exactly `d2` cross-neighbors has probability

`P(E_sigma) = binom(d,d1)^(2N) * ((Nd1-1)!!)^2 * (Nd2)! / (2Nd-1)!!`.

For fixed positive degrees and admissible sizes, Stirling's formula gives

`P(E_sigma) = Theta(sqrt N) * [binom(d,d1)^2 * d1^d1 * d2^d2 / (2d)^d]^N`.

Conditioning the graphs on simplicity changes this by a degree-dependent constant factor asymptotically. For `(d1,d2)=(2,1)` the probability is `Theta(sqrt N) * 6^(-N)`. Thus polynomial unconditional failure probabilities provide no conditional control. The uniform-simple RSBM is precisely the uniform-simple `d`-regular graph conditioned on `E_sigma` for a prescribed planted split.

## 6. Algebraic detection was already explicitly recognized

Bandeira, Banks, Kunisky, Moore, and Wein, [*Spectral Planting and the Hardness of Refuting Cuts, Colorability, and Communities in Random Graphs*, COLT 2021](https://proceedings.mlr.press/v134/bandeira21a/bandeira21a.pdf), Remark 3 (PDF p. 7), explicitly states that the eigenvector structure gives polynomial-time **distinguishing** of the noiseless equitable SBM from uniform regular graphs at all parameter settings, citing Barucca. Its hardness conjecture therefore adds rewiring noise. Distinguishing does not itself establish planted-partition recovery or simplicity, but algebraic detection should not be presented as new here.
