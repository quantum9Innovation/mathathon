# Blind fibers, cover projections, and planted hypergraph factorizations

15 November 2026. Bounded primary-source comparison; no historical firstness certificate.

The `K_{3,12}` obstruction has a particularly close connection to complete hypergraph factorizations. A paper posted on **12 November 2026** proves a nonpartite contiguity theorem at exactly the same entropy inequality. Its model is different from the partite hypergraph obtained here. The elementary counting obstruction itself needs neither contiguity nor a second moment.

This note binds the actual root source
[`nonregular-fiber-counting-obstruction.tex`](../nonregular-fiber-counting-obstruction.tex),
SHA-256 `8b9a8bdfcd9392eb05c4e15e7f3a856e8cab4e95c37b82d2d517af6d2ef30f39`.
The source was read in full. The model map and calculations below are independent derivations, not claims reported in the cited papers.

## The exact factorization model behind the genie

Reveal the `r` small-side fibers `L_1,...,L_r`, each of size `N`, in a lift of `K_{r,b}`. Each hidden-side vertex `v` has one neighbor `f_i(v)` in each `L_i`. Replace it by the hyperedge

\[
 (f_1(v),\ldots,f_r(v))\in L_1\times\cdots\times L_r.
\]

Keep hyperedge occurrences labeled by `v`. The result is an **r-uniform, r-partite, b-regular hypergraph**, with `N` vertices per part and `bN` hyperedge occurrences. An ordered hidden-fiber partition is exactly a proper `b`-edge-coloring of this hypergraph in which every color occurs once at every vertex. Equivalently, it is an ordered decomposition into `b` perfect matchings. This equivalence is exact, including repeated hyperedges. The original bipartite lift graph is always simple.

Conversely, an ordered factorization gives exactly the hidden right fibers. Thus alternative factorizations are alternative covering projections onto the **same** known `K_{r,b}`, even while the genie fixes every `L_i`. This is stronger than merely finding a second possible base graph. The ambiguity remains after quotienting the `b!` global color permutations.

The planted hypergraph law is the union of `b` independent uniform perfect matchings of the complete `r`-partite hypergraph, with a uniform assignment of the `bN` distinct occurrence labels. This assignment is the hidden partition in the inference experiment.

## Exact change of measure and information count

Let `P_N` be uniform over all `r` independent balanced maps `f_i:V→L_i`, each fiber of each map having size `b`. Thus its observation space has cardinality

\[
 U_N=\left[\frac{(bN)!}{(b!)^N}\right]^r.
\]

Write `Z(G)` for its number of ordered complete factorizations and `W(G)=Z(G)/b!`. The exact marked count in the root source is

\[
 T_N=(bN)!(N!)^{(r-1)b}.
\]

Consequently

\[
 \mathbb E_{P_N}Z
 =\frac{T_N}{U_N}
 =\frac{(b!)^{rN}(N!)^{(r-1)b}}{((bN)!)^{r-1}}. \tag{A}
\]

If `Q_N` is the planted observation law, direct counting gives

\[
 Q_N(G)=\frac{Z(G)}{\mathbb E_{P_N}Z}\,P_N(G). \tag{B}
\]

The posterior on its ordered factorizations is uniform. Therefore the optimal unordered recovery probability is

\[
 \mathbb E_{Q_N}\frac1W
 =\frac{b!P_N(Z>0)}{\mathbb E_{P_N}Z}
 \leq\frac{b!}{\mathbb E_{P_N}Z}, \tag{C}
\]

and for `t≥1`,

\[
 Q_N(W\leq t)\leq\frac{b!t}{\mathbb E_{P_N}Z}. \tag{D}
\]

Thus exponential ambiguity under the planted law follows from an **exponentially large null first moment**, without needing that this first moment be typical under the null. The posterior cancellation in (C) is the same finite count as the root source's `b!U_N/T_N` bound. It is sharper to present that finite count directly than to invoke a general information inequality.

Stirling gives

\[
 \mathbb E_{P_N}Z
 =b^{-(r-1)/2}(2\pi N)^{(r-1)(b-1)/2}
 e^{\gamma_{r,b}N}(1+O_{r,b}(N^{-1})),
\]

\[
 \gamma_{r,b}=r\log(b!)-(r-1)b\log b.
\]

When `γ>0`, equations (C)–(D) prove exponential nonrecoverability and exponentially many compatible factorizations with planted probability tending to one. A nonpositive `γ` does not settle recovery or uniqueness.

## Closest current primary theorem: a nonpartite result

Alan Frieze and Xavier Pérez-Giménez, **Contiguity of unions of perfect matchings and random regular uniform hypergraphs**, [arXiv:2611.16160v1](https://arxiv.org/abs/2611.16160v1), submitted 12 November 2026. [Primary PDF](https://arxiv.org/pdf/2611.16160v1).

Theorem 1, printed page 1, fixes `s≥3` and `R≥2` with

\[
 f_{R,s}=\log(R!)-\frac{R(s-1)}s\log R>0.
\]

It asserts mutual contiguity between the union of `R` independent uniform perfect matchings of the complete **nonpartite** `s`-uniform hypergraph on `n` vertices and the uniform simple `R`-regular `s`-uniform hypergraph, as `n→∞` through multiples of `s`. Section 2, printed pages 2–3, uses the complete-factorization count `Z` and the planted change of measure `Q=ZP/E_PZ`. The second moment uses a sharp permutation-entropy inequality; the proof then uses small-subgraph conditioning. The source gives no partite theorem. These statements were checked directly in the PDF, rather than inferred from the title.

Under `s=r`, `R=b`, `n=rN`, the entropy constants satisfy exactly

\[
 r f_{b,r}=\gamma_{r,b}.
\]

**Assessment.** This is very close prior mathematics: full factorizations, the same planting mechanism, and the same entropy rate. It should be cited prominently if the obstruction is written up. It does not by itself prove partite contiguity, nor does its stated theorem concern inference of an erased factorization. The present elementary partite lower-tail argument is a direct counting specialization of the standard planted change-of-measure principle. Describing the information-count mechanism as a new general method would overstate the contribution. Whether this exact `K_{r,b}` recovery corollary was stated elsewhere was not established by this search.

The checked source is 24 pages. Actual reading coverage: Theorem 1 and introduction, Section 2 in full, Section 3 through the second-moment setup and exponential tail calculation, the final simplicity/contiguity passage and references, and the appendix's statement of the permutation entropy input. The second-moment and lattice proof were **not** independently audited in full. A complete text search finds no occurrence of `partite`.

PDF SHA-256: `d8089dbc9e7fc8b630991d37d358565ed9d4edc916b098a764d578184c25f2be`.

## Classical graph-factorization comparison

M. S. O. Molloy, H. Robalewska, R. W. Robinson, and N. C. Wormald, **1-Factorizations of random regular graphs**, *Random Structures & Algorithms* **10** (1997), 305–321, [publisher primary record and abstract](https://onlinelibrary.wiley.com/doi/10.1002/(SICI)1098-2418(199705)10:3%3C305::AID-RSA1%3E3.0.CO;2-%23).

The abstract states contiguity of fixed-degree random regular graphs with unions of independent random perfect matchings, conditioned to be disjoint, and also states the corresponding bipartite result. This is the graph analogue (`r=2` uniformity), rather than the minimum-degree-three partite hypergraph case above. Only the publisher abstract was inspected for this source, so no specific formula or theorem number is attributed to its body.

This source establishes that factorization-based changes of measure and their contiguity interpretation substantially predate the current problem. It does not, from the inspected material, provide the exact erased-fiber impossibility statement.

## Random covers: structural properties, decision, and inference differ

The standard model is already the subject of Alon Amit and Nathan Linial, **Random Graph Coverings I: General Theory and Graph Connectivity**, *Combinatorica* **22** (2002), 1–18, [primary publisher page](https://link.springer.com/article/10.1007/s004930200000). Its abstract describes independent matching lifts and identifies connectivity as its main specific result. A related primary source, Shashwat Silas, **Randomly Generated Subgroups of the Symmetric Group and Random Lifts of Graphs**, [arXiv:1607.01330v2](https://arxiv.org/abs/1607.01330v2), relates connectedness to transitivity of the subgroup generated by the cycle-rank number of random permutations. These are relevant to the root source's optional connectedness conditioning. They do not make connectivity a test for uniqueness of a covering projection. Only these primary abstracts were inspected here.

Jan Bok, Jiří Fiala, Nikola Jedličková, and Jan Kratochvíl, **Computational Complexity of Covering Regular Trees**, [MFCS 2025 primary record](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2025.26), studies the worst-case `H-Cover` decision problem: whether an input admits a locally bijective homomorphism to fixed `H`. Its abstract proves hardness for regular targets obtained by adding semi-edges to a tree. This differs from counting alternative projections in the planted distribution. No inference threshold is attributed to this result. The primary record/abstract and its definition of a covering projection were inspected.

Dmitriy Kunisky and Xifan Yu, **Computational hardness of detecting graph lifts and certifying lift-monotone properties of random regular graphs**, [arXiv:2404.17012v1](https://arxiv.org/abs/2404.17012v1), provides a more directly inferential comparison. Its introduction, pages 1–2, explicitly says that exact old eigenvalues make the *noiseless detection* task easy. Conjecture 1.6 and the precise noise models in Section 2.3 concern noisy lifts of regular Ramanujan bases. Theorem 1.9 gives local-statistics SDP lower bounds. Neither computational hardness with noise nor inability of that SDP hierarchy to detect is an information-theoretic nonuniqueness theorem for an exact nonregular lift.

For Kunisky–Yu, actual checked coverage was the abstract, printed pages 1–5 including Definition 1.1, Conjecture 1.6 and Theorem 1.9, and the Section 2.3 location; the entire 64-page paper was not audited. PDF SHA-256: `b47c066a39eae6ce65a658d67bc241ac1d039d8b41b32223ffe8cb61f8d017a7`.

## Bounded assessment for the packet

The exact structural statement supported by the root proof is that some connected fixed nonregular bases of minimum degree three admit exponentially many compatible equal-fiber projections with the same known quotient, with high probability. Its inference form requires a hidden partition or relabeling-invariant experiment; structural multiplicity holds for every fixed planted partition. Both qualifications are already explicit in the root source.

The obstruction should be presented as a transparent finite counting argument, with the hypergraph-factorization equivalence and the recent nonpartite theorem acknowledged. The search does not justify claiming a first random-cover nonidentifiability theorem, a sharp threshold at `γ=0`, or a classification of recoverable nonregular bases. Failure of the omission-weight LP is not itself a nonidentifiability theorem.

The weighted positive note proves an exact capacitated fractional-factor criterion and a restricted nonregular entropy extension. It leaves full recovery unasserted. The strict example `K_5` minus one edge shows that the sufficient class extends beyond regular bases, while the `K_{3,12}` example shows why minimum degree alone cannot replace the condition.

Search coverage was targeted rather than exhaustive: primary searches for random-cover projection uniqueness/reconstruction, erased-fiber recovery, planted complete factorizations, random regular partite hypergraph edge colorings, graph-factorization contiguity, and the exact factorial entropy expression. No primary source inspected here explicitly states the same `K_{3,12}` inference corollary. That is a search result, not a novelty certificate.
