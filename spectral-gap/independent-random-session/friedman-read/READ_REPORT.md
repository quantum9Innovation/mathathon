# Complete new read of the Friedman reference

This report concerns the supplied primary source `cs/0405020`, not a reconstruction from historical dossiers. Its entire `all.tex`, lines 1 through 7220, and its included `all.ind`, lines 1 through 116, were newly read in this session. The report does not claim full formal verification of every proof or that any defect reported here was previously unknown.

The principal usable fact for the concurrent graph investigation is the deterministic tangle witness in Section 4. Its proof does not require a tree neighborhood around the embedded tangle. That removes a probabilistic conditioning obligation from the proposed growing-base obstruction.

## Source and coverage

The [official arXiv record](https://arxiv.org/abs/cs/0405020) identifies one deposited version, submitted May 5, 2004. The source itself is dated March 27, 2002, with third revision May 3, 2004. The [author's publication list](https://www.cs.ubc.ca/~jf/pubs/index.html) identifies the same 118-page third revision. The [publisher record](https://doi.org/10.1090/memo/0910) identifies the later Memoirs publication. This session read the supplied arXiv source, and did not read or compare the entire publisher PDF. Findings below must not be silently attributed to the publisher's text.

| Item | Size | SHA256 |
| --- | --- | --- |
| `snapshot/reading-sources/alon-second-eigenvalue/source/all.tex` | 7220 lines, 293361 bytes | `907027a6eb92efe2e8f53737a25c5e77e20a50615d747133a8938a92ef3f3bf3` |
| `snapshot/reading-sources/alon-second-eigenvalue/source/all.ind` | 116 lines | Recorded in `coverage.json` |

All of the following chunks were displayed and read without output truncation. No source interval was skipped.

| Read | Inclusive source lines | Coverage |
| --- | --- | --- |
| 1 | 1 to 800 | Preamble, abstract, introduction, beginning of trace method |
| 2 | 801 to 1600 | Trace limitations, explicit loop tangles, graph and VLG terminology |
| 3 | 1601 to 2400 | Generating functions, infinite-edge limit, nonbacktracking graph, tangle witness |
| 4 | 2401 to 3200 | Tangle occurrence probabilities, forms and general walk expansion |
| 5 | 3201 to 4000 | Simple loops, types and new types, selective trace, crucial count statement |
| 6 | 4001 to 4800 | Crucial selective count proof, fundamental orders, Ramanujan functions, selective expansion |
| 7 | 4801 to 5600 | Selective expansion proof, tangle absence, Möbius truncation |
| 8 | 5601 to 6400 | Conditioned types, strongly irreducible traces, sidestepping, spreading proof |
| 9 | 6401 to 7220 | Spreading completion, final proofs, closing remarks, bibliography |
| 10 | `all.ind` 1 to 116 | Included glossary |

The two EPS illustrations were not independently inspected. Their mathematical definitions and explanatory text in `all.tex` were read. External papers cited in the bibliography were not counted as newly read.

## Complete proof structure

The introduction fixes degree and the model before taking the number of vertices to infinity. For the independent-permutation model with even degree, the polynomial failure exponent is governed by the smallest order of a supercritical tangle. The analogous exponents depend on the random graph model. Domination or contiguity transfers the qualitative probability limit but need not preserve its polynomial exponent.

Section 2 explains why merely extending the unmodified trace expansion fails. Nonbacktracking trace coefficients are not all Ramanujan functions. A rare dense local core gives a positive contribution with an exponential growth rate exceeding the tree rate. The section's loop example has nonbacktracking growth `2m-1`, and its regular-tree completion has adjacency radius `(2m-1)+(d-1)/(2m-1)` when `2m-1 > sqrt(d-1)`.

Section 3 supplies the deterministic machinery. Variable-length graphs separate a finite core from long paths. Positive generating functions and Perron values handle edge suppression and edges tending to infinity. The nonbacktracking graph counts strongly irreducible closed walks. The tree completion of a core has adjacency radius above `2 sqrt(d-1)` precisely when the core's nonbacktracking radius exceeds `sqrt(d-1)`. The proof is a Schur-complement or generating-function version of the Ihara-Bass bridge, with a physical branch restriction supplied by the tree generating function.

Section 4 translates cores into spectral obstructions and occurrence probabilities. The order is edges minus vertices. A fixed labelled tangle has expected occurrence count `n^(-order)+O(n^(-order-1))`. Automorphisms must be divided out when estimating the probability of at least one occurrence. Two distinct overlapping pruned copies force larger order, which controls the overlap correction.

Section 5 organizes the trace into forms, types and new types. A form remembers the exact graph traced by a walk and its labels. A type suppresses degree-two paths. A new type additionally fixes short edges and leaves the others long. The expected count of a form is an exact product of falling factorials. The general walk expansion has polynomially controlled remainders, but its coefficients need not have the desired tree growth without selection.

Section 6 defines a selective trace by excluding walks that traverse a forbidden tangle during a short contiguous interval. Its crucial count bounds the number of selective walks below the nonbacktracking tree rate. This restores convergence of the infinite multiplicity sums. The argument uses finitely many extremal VLGs below the threshold, along with positive generating-function majorants. The remainder of the section determines fundamental orders for the four models.

Section 7 explains the closure of Ramanujan functions under convolution. This is needed when products of path sums are assembled. It also identifies why the permitted exponential error base is tied to the spectral edge.

Section 8 proves that the selective trace has an arbitrarily long expansion with Ramanujan coefficients. It groups a finite number of types and new types at each fixed expansion order. Polynomial word sums reduce to elementary exponential-polynomial terms. The selective walk count offsets the multiplicity growth in the summation over edge traversal counts.

Section 9 addresses a separate necessity: selection alone is not a spectral statistic of the original graph. It seeks expansions for the selective trace weighted by the event that a forbidden tangle is present, then subtracts this from the unrestricted selected trace. On the tangle-free event, selection changes no walk. A finite set of minimal supercritical tangles is obtained by suppressing degree-two paths and taking limits when an edge length diverges. Inclusion-exclusion is expressed through a poset of derived tangles and their Möbius coefficients. Types are enlarged to remember overlap with a fixed tangle.

Section 10 replaces irreducible traces with strongly irreducible traces. The latter are power sums of nonbacktracking eigenvalues. Each adjacency eigenvalue gives the two roots of `mu^2-lambda mu+d-1=0`, together with the appropriate `+1` and `-1` contributions. Half-loops require separate odd-length conventions.

Section 11 supplies the sidestepping lemma. Applying a high power of a finite-difference operator kills the unknown polynomial coefficients of the expansion. The remaining powers detect eigenvalues outside the permitted bulk. The section then separates small, intermediate and larger displacement parameters, using polynomial interpolation to propagate a bound from large trace orders to smaller ones. Several parity and normalization details in this presentation require care, as described below.

Section 12 proves spreading with polynomially small failure probability. Small exceptional vertex sets are excluded by small supercritical tangles. Larger sets are handled by exact matching or permutation counts, Stirling's formula and entropy bounds. Spreading separates the trivial eigenvalue from all other adjacency eigenvalues in absolute value.

Section 13 combines tangle exclusion, the conditioned selective expansion, the nonbacktracking trace identity, spreading and the sidestepping lemma. It takes an expansion order large enough for the desired fixed epsilon, and a trace length proportional to that order times `log n`. Markov's argument then bounds nontrivial adjacency eigenvalues. Section 14 gives sufficient model properties and verifies them for the remaining ensembles. Section 15 discusses exact Ramanujan bounds, critical tangles, random covers and alternatives to conditioning away tangled graphs.

This is the dependency order. A sharper permutation monomial estimate cannot bypass the selective walk enumeration, the tangle-absence expansion, spreading, or the extraction of a spectral bound.

## Direct application to a growing base graph

The statement labelled `th:key_to_s`, at source lines 2307 to 2344, is the key deterministic ingredient. For a finite core `psi`, take a finite induced subgraph of its regular-tree completion. Its nonnegative Dirichlet Perron vector `f` satisfies `A f >= r f` after extension by zero, where `r` is its Dirichlet spectral radius. The regular-tree completion covers every regular host graph containing the core. Pushing `f` forward by summing over the fibers of this covering map preserves the pointwise inequality. Collisions of different tree branches in the host therefore do not invalidate the positive witness.

For a graph that is itself an `n`-lift of a base graph, let `g` be this pushed-forward witness and suppose its support has at most `S` vertices. Let `P_old` be the orthogonal projection onto functions constant on each base fiber. Cauchy-Schwarz in each fiber gives

`||P_old g||^2 <= (S/n) ||g||^2`.

The old and new subspaces reduce adjacency. Since adjacency norm is at most `d`, putting `delta = ||P_old g||^2/||g||^2` gives

`Rayleigh((I-P_old)g) >= r - (d-r)delta/(1-delta)`

whenever `delta < 1`. Consequently an embedded fixed hypercritical core produces a new eigenvalue near its completed-tree radius, uniformly in base size, once `n` is large relative to its finite witness support. This projection argument is an additional derivation in this report. The source's theorem is about the second eigenvalue and does not make this old-fiber projection explicitly.

This means that an independent collection of base locations, each supporting a fixed rare core with probability of order `1/n`, can prevent a base-uniform high-probability random-lift theorem when the number of locations is of order `n`. The exact graph family and its Poisson calculation belong to the parent investigation, not to a theorem claimed by this source-reading report.

## Incorrect intermediate assertions in this source version

These are local source checks. They do not show that Alon's conjecture, Friedman's main spectral theorem, or a later published proof is false. The source comparison with the publisher's full text remains undone. Historical discovery priority is not claimed.

1. **Finite common-fixed-point bound.** At lines 1117 to 1137, the common-fixed-point calculation replaces a two-point probability by `n^(-2m)`. For `m` independent uniform permutations the exact two-point probability is `1/(n(n-1))^m`, which is larger. For two permutations, inclusion-exclusion gives `p_n = sum_{k=1}^n (-1)^(k+1)/(k! (n)_k)`. At `n=4`, this is `41/192`, whereas `1/n-1/(2n^2)` is `42/192`. Thus that asserted lower bound for the common-fixed-point event is false. Correct Bonferroni gives `p_n >= 1/n-1/(2n(n-1))`. The main polynomial order remains the same. The resulting spectral-event theorem could conceivably have additional contributions, so this example is not a counterexample to its final spectral probability statement.

2. **Möbius remainder boundedness.** At lines 5493 to 5502, the proof treats the truncated Möbius remainder `h(G)` as having uniformly bounded magnitude. Take degree four, a tangle consisting of one vertex with two distinctly labelled whole-loops, and cutoff `r=2`. The only derived tangle of order below two is this tangle, and its Möbius coefficient is one. In the graph where both generating permutations are identity, `N(psi,G)=n`, the event indicator is one, and `h(G)=1-n`. Its magnitude is not bounded independently of `n`. An upper bound on a signed remainder is insufficient for the absolute error estimate needed for the expansion. A replacement must control the expected absolute remainder weighted by the walk count, for example using higher-order derived-tangle counts. The current rare-event-probability argument alone does not do that. This is an identified proof-step gap, not a refutation of the lemma's conclusion.

3. **Uniform geometric-sum lemma.** The statement labelled `lm:useful_aux`, lines 5020 to 5086, claims a coefficient bound proportional to `(1-rho)^(-2D)`. With `D=1`, `Q(x)=x` and `g(r)=r rho^r`, the constant coefficient of `sum_r Q(x-r)g(r)` has magnitude `sum_r r^2 rho^r = rho(1+rho)/(1-rho)^3`. No universal multiple of `(1-rho)^(-2)` bounds this as `rho` approaches one. The binomial generating function displayed in the proof also has incorrect exponents. The later application uses fixed `rho=(d-1)^(-1/2)`, bounded away from one, so an extra factor may be absorbed there. This particular local error need not affect that fixed-degree application.

4. **Half-loop model inconsistency.** The introduction's `J_{n,d}` assertion imports the `G_{n,d}` exponents. Section 4, lines 2644 to 2648, says that a one-vertex half-loop tangle gives the lower bound just as whole-loops did. But `m` half-loops have nonbacktracking radius `m-1`, whereas `m` whole-loops have radius `2m-1`. Section 6, lines 4557 to 4596, instead derives the same fundamental order for `J_{n,d}` as for the perfect-matching model. Section 12 explicitly says those two fundamental orders agree. For instance, at degree eight the two displayed formulas give one and two. This session establishes an internal inconsistency and a failed justification of the displayed lower-bound exponent. It does not establish a counterexample to every possible spectral probability estimate for `J_{n,d}`.

5. **Other presentation problems.** The radius-of-convergence formula at line 1605 omits the reciprocal. The closed-walk supermultiplicativity inequality at line 1547 is written in the wrong direction. The Section 6 degree-six tangle calculation first says to take a square root of a two-step transition matrix's Perron value, then identifies the unsquared value with the nonbacktracking radius. These are explicit local transcription or normalization errors. The needed threshold conclusion in the degree-six example survives the square-root correction.

The sidestepping proof also uses a bound of the form `|1-theta| <= 1-log^(-2)n` solely from `|theta|>log^(-2)n`, at source lines 6203 to 6207. That implication is false for real `theta` near two. A parity-aware treatment or an assumption excluding the negative endpoint is needed at that point. The later spreading statement does exclude nontrivial eigenvalues near the negative endpoint, but it is not an assumption of the abstract lemma as stated. I record this as a repair obligation for that proof step, without asserting that the abstract lemma itself is false.

## Verification and remaining work

`check_source_steps.py` computes exact rational common-fixed-point probabilities for `2 <= n <= 14`, checks the correct Bonferroni inequality, and independently enumerates all 576 ordered pairs of permutations at `n=4`. It also records the symbolic Möbius-remainder counterexample. Finite checks corroborate the explicit examples and do not establish a general spectral theorem.

The useful deterministic tangle witness and its old-fiber projection can be proved without importing the problematic truncation or sidestepping steps. For a source-level repair project, the important remaining tasks are comparison with the Memoirs text, a correct weighted Möbius remainder estimate, a fully parity-aware sidestepping argument, and reconciliation of the near-perfect-matching exponents. These tasks are outside the completed full-read claim.
