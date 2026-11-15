# Structure and complete visual inventory

## Reading map

| Location | Purpose | Definitions and assertions | Read or skim |
| --- | --- | --- | --- |
| Section 1, pages 1 to 5 | Motivation, model, spectral density, lift comparison, proof roadmap | Uniform simple biregular family, lower bound in Equation 2, density in Equation 3 | Read Sections 1.1 and 1.3 carefully. Read 1.2 carefully because it limits model substitutions |
| Section 2, pages 6 to 7 | Define $B$ and unpack Ihara-Bass | Theorem 1, Equations 4 to 7, imaginary roots from zero adjacency eigenvalues | Essential. Every singular-value case matters |
| Section 3, pages 8 to 9 | State and deduce main results | Lemma 2, Theorems 3 and 4, Equation 8 | Essential, but use the corrections in `05-main-results.md` for Lemma 2 multiplicities |
| Section 4.1, page 10 | Random graph implementation | Half-edges, uniform matching, $B=MN$ in Equation 9 | Essential for understanding where randomness enters |
| Section 4.2, page 11 | Local tree-likeness | Definition 1, Lemma 5 | Understand the statement. The proof can be skimmed on a first pass |
| Section 5.1, pages 12 to 13 | Moment-proof architecture | Lemma 6, Equations 10 and 11, Figure 4 | Essential overview |
| Section 5.2, pages 13 to 15 | Centered and tangle-free matrix decomposition | Definitions 2 to 4, Equations 12 to 17 | Central technical reading. Indices and kernel prose need audit |
| Section 5.3, pages 15 to 16 | Expected matching products | Definition 5 and Lemma 7 | Understand the role of consistency. Full proof delegates to an external result |
| Section 5.4, pages 16 to 19 | Count tangle-free and remainder circuits | Lemmas 8 to 10, Figure 5 | Central combinatorics. Figure 5 must be read critically |
| Section 5.5, page 19 | Count half-edge labelings | Lemma 11 and Corollary 12 | Read Lemma 11. Treat Corollary 12 as an unresolved audit item |
| Section 5.6, page 19 | Left-right imbalance | Lemma 13 | Important in the genuinely biregular case |
| Section 5.7, pages 19 to 20 | Inconsistent edge control | Lemmas 14 and 15 | Supporting bookkeeping |
| Section 5.8, pages 20 to 26 | Moment and norm estimates | Theorems 16 and 17, partition $\mathcal C_1,\mathcal C_2,\mathcal C_3$ | Most technical section. Understand the common estimate and three regimes before detailed sums |
| Section 5.9, page 26 | Finish Theorem 3 | $\ell$th root and remainder suppression | Essential and short |
| Section 6, pages 26 to 31 | Community detection | Frame model, Proposition 18, Theorems 19 and 20 | Read after the main theorem. Figure 6 clarifies the model substantially |
| Section 7, pages 31 to 32 | Tanner and LDPC codes | Theorem 21, Corollary 22, $(14,9)$ example | Application and numerical illustration, with asymptotic cautions in `09` |
| Section 8, pages 32 to 36 | Deterministic matrix completion | $\gamma_2$, Theorems 23 to 26 | Self-contained enough after expander mixing. Read Theorem 24 proof |
| Appendix A, page 36 | Symbol table | Fast lookup | Useful, but the printed tree-excess sign conflicts with the proof |
| References, pages 37 to 40 | Bibliography | Sources of imported results | Do not use as evidence that an imported result was independently checked here |

## Dependency-friendly order

A shorter first route is Sections 1.1, 2, 3, 4.1, 5.1, 5.8.4, and 5.9, followed by one application. A complete proof reading must insert Sections 4.2 and 5.2 to 5.8.3.

# Visual inventory

All six numbered figures were inspected on the rendered pages. Every embedded source component was also opened separately. There are no numbered tables in the paper. Appendix A is a substantive symbol table and is included at the end of this inventory.

## Figure 1: biregular schematic

**Location:** page 2, Section 1.1, asset `bipartite_biregular_schematic.png`.

**What the visual encodes:** Two large colored ovals represent $V_1$ and $V_2$, labeled $n$ and $m$ vertices. A representative $u\in V_1$ has three outward stubs marked $d_1$, and $v\in V_2$ has two outward stubs marked $d_2$. The large double-headed arrow between the ovals is schematic matching across the partition.

**Main takeaway:** Regularity is side-specific. Every edge crosses, but not every vertex has the same degree. The stubs also preview the half-edge construction in Section 4.1.

**Claim supported:** Uniform sampling over simple biregular graphs and the feasibility equation $nd_1=md_2$.

**Ambiguity or caution:** The three and two stubs are illustrative, not an assertion that $d_1=3,d_2=2$. The arrows are not directed graph edges, and no actual matching is drawn. The double arrow must not be read as a single edge between aggregated vertices.

**How to use it:** When reading the configuration model, replace each schematic stub by a label $(v_i,j)$ or $(w_i,j)$. The uniform random permutation wires these labels across the ovals.

## Figure 2: a biregular graph that is not the required lift

**Location:** page 4, Section 1.2, asset `Lift_counterexample_2.png`.

**What the visual encodes:** The left graph is $K_{2,3}$. The crossed lift arrow points to a second graph with four green left vertices and six red right vertices. The drawn right graph has three edges at every left vertex and two at every right vertex. Its crossed connections are essential, not decorative.

**Main takeaway:** The same biregular degree data and the same total size as $2K_{2,3}$ do not force the graph to be a 2-lift of $K_{2,3}$.

**Claim supported:** A single base graph cannot produce every $(3,2)$-biregular graph through lifting. Combined with the equal-probability pair in the text, this is an obstruction to naively replacing the uniform configuration model by a lift model.

**Derived reading of the connectivity:** The caption says every pair of left vertices shares a right neighbor. With four left and six right vertices, the six right vertices can be viewed as the six unordered pairs of left vertices. Each left vertex meets the three pair-classes containing it. In particular, any purported fiber pair would also share a neighbor, whereas two left vertices in one fiber of a $K_{2,3}$ lift have disjoint right-neighborhoods.

**What it does not prove:** This example does not prove non-contiguity of random lift and configuration distributions. The authors explicitly phrase that broader conclusion as a doubt. It also does not dispute existence results for special Ramanujan lift families.

## Figure 3A: adjacency spectrum of one finite graph

**Location:** page 7 left panel, Section 2.1, asset `spectrum_n_400_k1_3_k2_7.png`.

**Parameters:** One sample from $\mathcal G(120,280,7,3)$. Thus $a=6,b=2$, the leading magnitude is $\sqrt{d_1d_2}=\sqrt{21}\approx4.583$, and the limiting upper second-eigenvalue threshold is $\sqrt6+\sqrt2\approx3.864$.

**What the visual encodes:**

- A histogram of the 400 real adjacency eigenvalues.
- A two-lobed black limiting density from Equation 3.
- A tall zero atom. There are at least $280-120=160$ structural zero eigenvalues.
- A red dash-dotted vertical line at the positive leading eigenvalue and a red dashed line at the limiting upper bound for the second eigenvalue. Symmetry supplies negative partners even when the lines are visually discussed at the positive edge.
- Small finite-sample eigenvalues outside the limiting bulk.

**Main takeaway:** The graph has a dominant spectral pair, a symmetric bulk, a forced zero component, and a small number of outliers. The theorem concerns the bulk edge relative to the outliers, not the leading Perron pair.

**Claim supported:** A concrete picture of Equation 3 and Theorem 4. The histogram should be compared against the limiting density, not expected to match it exactly at these finite dimensions.

**Ambiguity or caution:** The height axis is density, but the structural zero and leading spikes are clipped by the chosen plotting window. Do not infer their multiplicities or probabilities from their truncated visual heights. Finite-sample outliers are not counterexamples to an asymptotic statement.

## Figure 3B: non-backtracking spectrum of the same graph

**Location:** page 7 right panel, asset `spectrum_B_n_400_k1_3_k2_7.png`.

**What the visual encodes:**

- Transparent orange points for complex non-backtracking eigenvalues.
- A dashed black circle of radius $\tau=(ab)^{1/4}=12^{1/4}\approx1.861$.
- Blue crosses near $\pm\sqrt{ab}=\pm\sqrt{12}\approx\pm3.464$, the dominant real pair.
- Blue stars near $\pm i\sqrt b=\pm i\sqrt2\approx\pm1.414i$, associated with structural zero eigenvalues of $A$ when $X$ has full row rank.
- Additional points on the real and imaginary axes. The caption counts eight finite-sample outliers beyond the circle.
- Dense orange coverage near the circular bulk boundary, where overlap and transparency hide multiplicity.

**Main takeaway:** The adjacency outlier types have distinct non-backtracking signatures. Upper adjacency outliers generate real outer roots. Lower-positive-bulk-edge outliers generate purely imaginary roots. Bulk eigenvalues map close to the dashed circle.

**Claim supported:** The case analysis of Equation 8 and the strategy of proving Theorem 3 before Theorem 4. It also shows why controlling $B$ can detect rank loss through large imaginary eigenvalues.

**Quantitative reading, derived:** From one adjacency pair $\pm\xi$ above the bulk, Equation 7 gives two positive values of $\lambda^2$, hence four real $\lambda$ roots. Only the outer positive square root and its negative exceed the limiting circle. Imaginary roots from below the lower bulk edge have an analogous outer pair. This explains how a few adjacency outliers can produce the eight marked non-backtracking outliers.

**Ambiguity and local inconsistency:**

- Orange transparency prevents reliable visual counting of bulk multiplicity.
- The graph has no isolated vertices, so Theorem 1 excludes $\lambda=0$ for $B$. Nonetheless, the paragraph after Theorem 4 mentions “a number of zero eigenvalues” and black dots in the $B$ discussion. This should be read against the earlier warning that $0\notin\sigma(B)$, whose proof is simply $\det(D)\neq0$. The black dots visible near $\pm1$ are not evidence of a literal zero eigenvalue.
- The fixed sample demonstrates the mechanism, not the probability or convergence rate.

## Figure 4: four tangle-free legs forming one trace circuit

**Location:** page 13, Section 5.1, asset `circuit_k_2_l_2.png`.

**Parameters:** $k=2,\ell=2$. There are $2k=4$ legs and $\ell+1=3$ edge traversals per leg.

**What the visual encodes:** The traversal groups are

$$\gamma_1=(1,2,3),\qquad \gamma_2=(4,5,6),\qquad
\gamma_3=(7,8,9),\qquad \gamma_4=(10,11,12).$$

Purple edges carry the joins: $(3,4),(6,7),(9,10),(1,12)$. Red, green, blue, and magenta distinguish the other legs. The even legs are traversed backwards because they arise from transposed matrix factors.

**Main takeaway:** The trace of $[CC^*]^2$ is not a sum over one arbitrary 12-edge non-backtracking walk. It is a circuit assembled from four separately non-backtracking and tangle-free pieces, with permitted complications at their joins.

**Claim supported:** Equation 11 and the encoding strategy. The drawn union has eight distinct graph edges and twelve traversal indices, so repeated edges are part of the model. It also illustrates how each leg may be acyclic while the assembled circuit has a cycle.

**Ambiguity or caution:** A single purple line stands for the shared last and first traversal, not two different graph edges. Avoid counting twelve distinct graph edges. The statement that backwards orientation “turns out not to make any difference” relies on the undirected support. It does not say the transposes can be omitted from the algebra.

## Figure 5: compressed encoding of a path with one cycle

**Location:** page 17, Section 5.4, asset `path_encoding.png`.

**What the visual encodes:**

- A feeder path through vertices $1,2,3$.
- A six-edge cycle involving vertices $3,4,5,6,7,8$, with a return along already discovered edges.
- An exit from vertex $4$ to vertex $9$.
- Repeated traversal of the cycle indicated by a curved arrow marked $c+1$ times.
- The decomposition into $\gamma^a,\gamma^b,\gamma^c$ and the encoding

  $$(0,3,0)\,|\,(0,4,3)(4,0,0)\,\|\,(0,1,0).$$

**How to read the encoding:** The initial type-2 segment of length three discovers the feeder. In the cycle block, four new tree edges are followed by a non-tree closing edge encoded by its endpoint 3. The next triple asks for the already discovered tree path ending at vertex 4. Marks $|$ and $\|$ delimit the cycle portion, while the total path length lets one infer the repeat count.

**Main takeaway:** The encoding avoids recording every step of every repeated loop. That is exactly the saving needed for a useful circuit-count bound.

**Claim supported:** Lemma 8's minimal encoding and the modification for one-cycle tangle-free paths.

**Verified indexing inconsistencies:**

1. If $i=0,\ldots,c$ contributes six edges $4+6i,\ldots,9+6i$, then the next traversal index is $10+6c$. The caption uses $10+6c$, but the drawn exit label reads $10+6(c+1)$.
2. Under the caption's own length formula, the total is

   $$3+6(c+1)+1=6c+10.$$

   With $c=1$, this is 16, not the caption's $\ell=22$.
3. If one instead wants $\ell=22$ under that formula, the consistent value is $c=2$, giving three cycle traversals rather than the caption's two for $c=1$.

The encoding concept remains useful, but the printed example labels cannot all be true simultaneously. The safest anchor is the triple encoding rather than the numerical example in the caption.

## Figure 6A: weighted frame

**Location:** page 28 left panel, Section 6.1, source asset `frame.pdf`.

**What the visual encodes:** Three directed classes with proportions

$$p_A=\frac18,\qquad p_B=\frac18,\qquad p_C=\frac34.$$

The arrows carry degree weights. Reading $D_{ij}$ as neighbors in class $j$ per vertex in class $i$ gives

$$D_{AB}=D_{BA}=3,\qquad D_{AC}=6,\quad D_{CA}=1,\qquad D_{BC}=12,\quad D_{CB}=2.$$

The opposite arrows are drawn with different thicknesses. Large blue disk area conveys the larger class proportion.

**Main takeaway:** Reciprocal weights need not be equal. What matters is the detailed-balance equation $p_iD_{ij}=p_jD_{ji}$.

**Derived consistency check:**

$$p_A D_{AC}=\frac18\cdot6=\frac34=p_C D_{CA},$$

$$p_B D_{BC}=\frac18\cdot12=\frac32=p_C D_{CB},$$

$$p_A D_{AB}=\frac38=p_B D_{BA}.$$

Thus the model is feasible. The total degrees within classes are 9, 15, and 3 for types $A,B,C$ respectively.

## Figure 6B: a 72-vertex realization

**Location:** page 28 right panel, source asset `small_tripartite.pdf`.

**What the visual encodes:** Nine red vertices, nine green vertices, and 54 blue vertices, placed in separated clusters. There are no within-cluster edges. Edges fan out heavily between blue and green, with other cross edges between blue and red and between red and green.

**Main takeaway:** The tiny frame inflates into a much larger graph while preserving class-wise degrees. The graph need not be globally regular because per-class total degrees differ.

**Derived edge-count check:** The displayed weighting implies $9\cdot3=27$ edges between $A,B$, $9\cdot6=54$ between $A,C$, and $9\cdot12=108$ between $B,C$. These total 189 edge incidences counted once each, and the degree sum is $378=2\cdot189$.

**Claim supported:** The definition of a random regular frame graph and how Figure 6A governs Figure 6B.

**Important visual caution:** The caption explicitly says this realization is a **multigraph**, not a simple graph. It illustrates a configuration-model outcome before conditioning on simplicity, not a literal member of the simple-graph ensemble required by the theorem application. At this small size, parallel edges are visibly plausible and counting exact multiplicities from the dense rendering would not be reliable.

## Appendix A: symbol table

**Location:** page 36.

**What it encodes:** A compact list for $A,B,X^*,\sigma,\eta,\lambda_i,\mathcal G,d,V,E,\vec E,\chi,\gamma,\Gamma,F,T$, and norms.

**Main use:** Quick lookup after reading the precise definitions. It compresses away important path-length and ordering qualifiers.

**Audit finding:** It defines $\chi$ as $|V|-|E|+1$. Lemma 9 and every tree-excess calculation require $\chi=\mathscr E-\mathscr V+1$. The body is consistent with the latter, so the appendix entry should not be propagated.
