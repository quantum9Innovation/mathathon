# Partitioning frontier: primary-source scope map

Checked 2026-11-15. Repository input: `spectral-gap/RESEARCH_SESSION_2026-11-15.txt`, read in full. New files in this directory only. This is a targeted literature search and theorem-scope review, not an exhaustive priority determination or independent verification of the cited papers' complete proofs. Public PDFs and extracted text are retained for reproducibility.

The repository's actual new tool is a gap-free low-rank relative approximation to a fractional Laplacian response after one conductance increase. Its construction takes expected nearly-linear work for that one update. This is not already a polylogarithmic-time dynamic partitioning algorithm. Eigenvector stability, balance, cut rounding, evolving normalization, and cumulative updates remain separate issues.

## Two precise ambitious targets that survive the inspected literature

### Target A: nearly-linear optimal-quality balanced edge cutting

Fix constant b in (0,1/2). Let OPT_b be the minimum conductance of a cut whose two sides each have at least b of total degree volume. On every connected undirected graph with polynomially bounded integer capacities, find in expected O(m polylog n) time an Omega(b)-balanced cut S with

\[
 \Phi(S)\le C_b\sqrt{\log n}\,\mathrm{OPT}_b.
\]

The algorithm must work without an eigengap promise. Its output balance is measured in the same graph as OPT_b. A cut of conductance O(sqrt(OPT_b)) is a different, already classical guarantee. An O(log n) multiplicative guarantee is also already achievable by the cut-matching/fair-cut machinery. The substantive target is preserving the O(sqrt(log n)) quality while removing the n^epsilon sequential-work loss of the inspected chaining/SDP approaches. We found no primary theorem establishing this precise combination.

This is BIG IF TRUE. Our low-rank update might accelerate repeated matrix-function operations inside an SDP process, but that alone does not eliminate the work in finding violating paths or enforcing metric triangle inequalities. The SDP weight change is usually supported on many edges; it is not a single-edge edit. A legitimate intermediate theorem must prove an accumulated error/work bound over the actual adaptive sequence and preserve the exact separation-oracle certificate. Merely plugging in a one-edge response routine is insufficient.

### Target B: nearly-linear almost-optimal flow-expander decomposition

For every graph and parameter n^{-O(1)}<=phi<=1, compute in expected O(m polylog n) time C subset E such that each connected component of G-C is a phi-flow-expander and

\[
 |C|\le \phi m\log n\exp(O(\sqrt{\log\log n})).
\]

The comparison is the Bansal--Jambulapati--Saranurak polynomial-time theorem below, with its quality preserved. A cut-expander target is weaker and should be labeled separately. A parameter-dependent O(m/phi) bound does not meet this target. Overhead o(log n) is impossible in general; the desired quality already exists in polynomial time.

This is the stronger coherent research target for this repository: it asks whether response compression can help recycle certificates over recursive graph changes without paying an extra logarithm. The missing bridge is substantial. BJS uses concurrent-flow LP dual shortest-path metrics; an electrical/fractional energy certificate does not certify multicommodity congestion without a flow-cut loss. Induced-subgraph restriction is also not a PSD edge increase, and restriction/Schur complementation does not commute with fractional powers. A first concrete milestone would be a relative-response update representation for the actual restricted certificate, with total charged work over the recursion and no new log n in the cut charge.

## Source ledger and scope checks

### Classical balanced spectral cutting already removes the conductance dependence

[Orecchia--Sachdeva--Vishnoi, arXiv:1111.1491, STOC 2012](https://arxiv.org/abs/1111.1491) gives, for constant b and target gamma, an Omega(b)-balanced cut of conductance O(sqrt(gamma)), or a certificate excluding b-balanced cuts of conductance below gamma, in tilde O(m) time. The method uses heat-kernel random walks and fast Laplacian solves. Thus a static gap-free tilde O(m), O(sqrt(gamma)) balanced-cut claim is not a new frontier. Inspected abstract and theorem statements; full proof not re-audited. Local files: `osv2012.*`.

### Current sparse-cut quality/work tradeoff

[Kolmogorov, arXiv:2307.00115v5, 10 July 2025; ACM TALG 2025](https://arxiv.org/abs/2307.00115) simplifies Sherman's chaining approach. For epsilon in [Theta(1/log n),Theta(1)], it attains O(sqrt(log n/epsilon)) approximation using O(n^epsilon polylog n) maxflows. Its parallel version uses polylog n maxflows on O(n^epsilon) processors; this does not imply nearly-linear sequential work. Its triangle/violating-path mechanisms are not ordinary eigenvector perturbation. Inspected abstract/current version and source comparison; no claim of complete proof verification. Local files: `kolmogorov2025.*`.

### Polynomial-time near-optimal flow decomposition is now known

[Bansal--Jambulapati--Saranurak, arXiv:2602.15015v2, 28 April 2026](https://arxiv.org/abs/2602.15015), also [ICALP 2026](https://drops.dagstuhl.de/entities/publication/10.4230/LIPIcs.ICALP.2026.22), Theorem 1.1 gives polynomial-time phi-flow-expander decomposition with overhead O(log n exp(sqrt(log log n))); Theorem 3.1 extends to integral node measures. Its algorithm repeatedly solves a concurrent-flow LP and clusters in its dual metric. The n-vertex hypercube gives a graph-theoretic Omega(log n) overhead obstruction. The flow-cut gap rules out equating cut expansion and flow expansion at the same phi. We inspected the definitions, theorems, LP, algorithm overview, recursion charge, and stated open directions; no full proof audit. Local files: `bjs2026.*`.

### Near-linear time with log-squared overhead and arbitrary measures

[Agassy--Dorfman--Kaplan, arXiv:2510.23913v3, 29 October 2026](https://arxiv.org/abs/2510.23913) computes, for a vertex measure mu, a randomized tilde O(m)-time decomposition cutting O(phi log^2(n) mu(V)) edges and giving phi expansion relative to mu. Its introduction explains removal of 1/phi from the earlier ICALP 2023 bound using fair cuts. With mu equal to degree, this is the log-squared-overhead comparison. The measure-range assumptions and refinements are explicitly addressed in its Appendix D. Inspected first three pages and theorem scope; no full proof audit. Local files: `adk2026.*`.

[Li--Nanongkai--Panigrahi--Saranurak, arXiv:2203.00751v2, SODA 2023](https://arxiv.org/abs/2203.00751) supplies the nearly-linear fair-cut primitive. Its expander-decomposition application works even for polynomially small expansion. Therefore merely removing 1/phi from an older decomposition runtime is already done. Inspected abstract, introduction, and expander-decomposition scope. Local files: `faircuts2023.*`.

### Warm-starting expander decomposition is already an explicit 2026 technique

[Fleischmann--George Z. Li--Jason Li, ICALP 2026, arXiv:2511.02943](https://arxiv.org/abs/2511.02943), [proceedings](https://drops.dagstuhl.de/entities/publication/10.4230/LIPIcs.ICALP.2026.91), warm-starts the cut-matching game for weak decomposition, using O(log^2 n) maxflow calls instead of O(log^3 n). Its formal approximate-flow runtime is O(m log^9 n log log n+epsilon^{-1}m log^6 n) for integral polynomial capacities. Weak and strong decomposition have different guarantees. Thus a qualitative claim that low rank enables warm starts is not sufficient novelty. Inspected introduction, theorem statement, and definitions in proceedings; full proof not re-audited. Local files: `weakexpander2026.*`.

### Higher-order Cheeger: a fresh competing sharp claim changes target selection

[Lee--Oveis Gharan--Trevisan, arXiv:1111.1055v6, JACM 2014](https://arxiv.org/abs/1111.1055) gives the classical higher-order connection, including k disjoint sets with O(k^2 sqrt(lambda_k)) conductance and a constant fraction of k sets with O(sqrt(lambda_k log k)). Noisy hypercubes show the logarithmic factor is necessary in the latter regime. Local files: `highercheeger2014.*`.

[Yunpeng Li, arXiv:2609.35369v2, 5 October 2026](https://arxiv.org/abs/2609.35369) claims the same-index sharp statement phi_k<=C sqrt(lambda_k log(k+1)), with exactly k disjoint nonempty sets and original-graph one-sided conductance. This is a fresh primary preprint claim, not a theorem independently verified here. I inspected the theorem and proof architecture, including the dyadic maximal estimate and local eigenvalue count, but did not complete its proof audit. It would be improper to advertise this same inequality as a newly unexplored target without first auditing this competing claim. Local files: `highercheeger2026.*`.

[Kwok--Lau--Lee--Oveis Gharan--Trevisan, STOC 2013](https://cs.uwaterloo.ca/~lapchi/papers/Cheeger-conf.pdf) proves the sweep guarantee Phi(G)<=O(k)lambda_2/sqrt(lambda_k), with extensions to multiway cuts and balanced separator. A stronger guarantee on an explicitly large higher-order gap can already be classical.

### Dynamic spectral clustering: relevant current competitor and an objective caveat

[Jourdan--Macgregor--Schwartzman, ICML 2026](https://proceedings.mlr.press/v306/jourdan26a.html) maintains a sampling structure with O(log n) worst-case edge update. Theorem 6's query includes k dmax^2 log n, log n log* n epsilon^{-4}k^2, a static clustering call T_NC(epsilon^{-4}k^2,k), epsilon^{-8}k^4, and min{|Y|k^2 epsilon^{-4},vol(Y)}. It promises labels consistent with an approximate full partition; labels may be chosen afresh at query time. It does not promise small recourse or track a fixed eigenspace. Most critically, Appendix A's multiplicative conversion between positive kernel k-means cost and classical normalized cut requires an additive-shift check. Our exact obstruction is in `NORMALIZED_CUT_SHIFT_AUDIT.md`; that calculation is not a full algorithmic refutation. Inspected main result, graph-kernel definition, Appendix A, and formal Appendix F. Local files: `dynamiccoreset2026.*`.

[Laenen--Sun, arXiv:2406.03152, 2024](https://arxiv.org/abs/2406.03152) supports incremental graphs and changing cluster structure under explicit cluster promises, with O(1) amortized update and o(n) query. This is not an arbitrary fully dynamic, no-promise, genuine normalized-cut guarantee. Inspected abstract and model. Local files: `laenen2024.*`.

[Peng--Yoshida, arXiv:2006.04094, KDD 2020](https://arxiv.org/abs/2006.04094), Theorem 5.1 bounds expected volume sensitivity by O((nu_2/nu_3^2)vol(G)+1), under its degree, deletion-probability, reliability and spectral assumptions. Theorem 6.1 gives a k-way result under additional cluster assumptions. These are random edge-deletion sensitivity results, not an adversarial one-edge recourse theorem. Conversely, calling any gap-dependent stability bound new would overlook this work. Inspected Sections 4--6 and assumptions. Local files: `sensitivity2020.*`.

### Balanced vertex separators have substantial 2026 developments

[Spalding-Jamieson, arXiv:2506.01228v5, 15 October 2026](https://arxiv.org/abs/2506.01228) unifies reweighted spectral vertex separators for planar, genus, minor-free, and geometric classes. Theorem 1.8 gives formal polynomial runtimes and graph-class-dependent size guarantees, including robustness after vertex merges; the practical implementation corresponds to a specified weaker variant. This is not an unconditional nearly-linear general balanced edge-cut theorem. Inspected abstract, Theorems 1.1/1.3/1.8, and their runtime scope. Local files: `reweighted2026.*`.

[Bonnet--Korhonen--Le--Li--Masarik, arXiv:2512.01587v2, 8 September 2026](https://arxiv.org/abs/2512.01587), Theorem 2, finds O(poly(h)sqrt(n)) balanced vertex separators in deterministic O(poly(h)n) time, with a minor alternative. It does not assert optimal dependence on h. Inspected introduction and formal Theorem 2. Local files: `separator2026.*`.

[Le--Spalding-Jamieson, arXiv:2611.05756, 3 November 2026](https://arxiv.org/abs/2611.05756), Theorems 2--3, gives expected O(h^7(m+n)) time for a 3/4-balanced O(h log h sqrt(n)) separator in K_h-minor-free graphs, plus an induced-minor bound. Its FTRL mechanism and claimed flow-optimality belong to a different setting than general edge-cut approximation. Local files: `ftrl2026.*`.

[Le, arXiv:2605.05494v2, 8 May 2026](https://arxiv.org/abs/2605.05494), Theorem 2, improves the separator size to O(h sqrt(log h) sqrt(n)) in randomized polynomial time. Beware OCR: the square root over log h is easy to lose. Local files: `beyondflow2026.*`.

[Conroy--Le--Spalding-Jamieson, arXiv:2611.00663, 31 October 2026](https://arxiv.org/abs/2611.00663) newly claims a 3/4-balanced separator of size at most 16h sqrt(n), resolving the AST size conjecture, with an associated Lean formalization. This is a primary claim whose complete proof/formalization was not independently audited here. Thus proposing the unrestricted AST size bound as open would be inappropriate. Local files: `ast2026.*`.

[Kolmogorov--Spalding-Jamieson, arXiv:2603.15782, 16 March 2026](https://arxiv.org/abs/2603.15782) gives O(sqrt(log n/epsilon)) balanced-vertex-separator pseudoapproximation in n^{O(epsilon)}m^{1+o(1)} time; allowing any additional omega(1) factor yields almost-linear time. This is a vertex separator and balance may weaken. Local files: `balancedvertex2026.*`.

### Conditional hardness: do not claim a universal sub-square-root cut guarantee

[Raghavendra--Steurer--Tulsiani, arXiv:1011.2586, CCC 2012](https://arxiv.org/abs/1011.2586), Corollary 3.6, gives SSE-hardness of distinguishing a bisection of conductance epsilon+o(epsilon) from instances in which every cut of relative size between 1/10 and 1/2 has conductance at least c sqrt(epsilon). Thus an arbitrary-graph balanced-cut guarantee o(sqrt(OPT)) would contradict this hypothesis. It is conditional, not an unconditional NP-hardness theorem; it is a specific balance promise, not every possible small-set or unbalanced objective. Neither Target A's logarithmic factor nor Target B's runtime contradicts this statement. Inspected Theorem 3.5, Corollary 3.6, and Appendix A.3. Local files: `rst2012.*`.

## What this review actually establishes

The primary-source review changes the target landscape substantially and rules out several easy novelty claims. It does not establish a new partitioning algorithm or settle historical firstness. The concrete new mathematical artifact here is the exact normalized-cut/kernel-cost shift identity and the connected, regular, balanced cycle counterexample to an invalid relative-error transfer. That obstruction should become a required check in any proposed application of the repository's positive-form approximations to partition objectives.

## Follow-up: the proposed aggregate-leakage disjoint repair is already a specialization

An additional candidate asked for k disjoint sets after one positive edge addition, assuming an original k-partition of maximum one-sided conductance h, with bound C(h+sqrt(lambda_k(G'))) independent of k. `ONE_STEP_REPAIR_PRIOR_ART.md` reconstructs this from [Lau's September 2026 manuscript](https://cs.uwaterloo.ca/~lapchi/papers/ASGT.pdf), printed pp. 99--104, core overlap and local eigenvalue machinery. The explicit bound is max{h,4sqrt(2lambda_k)}+8sqrt(lambda_k). Merge the endpoint blocks to obtain k-1 sets, trim to cores, search outside, and then ordinary Cheeger splitting needs only the second local eigenvalue of one core. This is a specialization of known reasoning, not a third open frontier. A full-cover or efficient dynamic variant is a separate question whose novelty is not established here.
