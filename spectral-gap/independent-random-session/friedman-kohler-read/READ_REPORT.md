# Friedman and Kohler 2014, fresh complete source read

This session newly read all 13,144 lines of `spectral-gap/snapshot/reading-sources/relativized-second-eigenvalue/source/all.tex`. No historical dossier was used as a substitute for this read. This is a source mastery and defect report, not a verification of every proof or a new graph eigenvalue theorem.

The source has 540,574 bytes and SHA256 `71855d7f4603addf5d3c132751a05c878b39195032d87b3ac1a96c180f0887db`. The [official arXiv record](https://arxiv.org/abs/1403.3462) lists only version 1, submitted March 13, 2014. The TeX dates itself March 14, 2014. The imported PDF has SHA256 `3f724862d1d518939afb9f0425d66fb70c0598b67807fc81a7d1a7e48bc22571` and 144 pages. Its text was freshly extracted into `2014-pdf-text.txt` for targeted source comparisons. The whole PDF was not independently read a second time.

The authors subsequently wrote a six article series in 2019. The [first article](https://arxiv.org/abs/1911.05688) and [sixth article](https://arxiv.org/abs/1911.05775) were checked at their official records. Section 8.1 of the sixth article was newly read for its correction of an erroneous bound in the 2014 paper. This report does not claim a complete read of the 2019 series.

## Exact source coverage

The following ranges were printed and read in this session. Ranges use one based inclusive TeX source line numbers.

| Read | Lines | Content |
| --- | --- | --- |
| 1 | 1 to 1000 | Preamble, macros, glossary definitions |
| 2 | 1001 to 1800 | Glossary definitions, front matter, main results, introduction |
| 3 | 1801 to 2800 | Historical motivation, irregular graphs, graph and covering definitions |
| 4 | 2801 to 4000 | Cover model, old and new spaces, nonbacktracking trace method, tangles |
| 5 | 4001 to 5200 | Ignored draft material, loop expectation proof, asymptotic expansion definitions |
| 6 | 5201 to 6600 | Certified trace overview, proof structure, pruned graphs, convolution bounds |
| 7 | 6601 to 7200 | Walk statistics, potential walks, exact symmetrized expectation, Taylor expansion |
| 8 | 7201 to 7800 | General walk sum expansion, types and forms, finiteness, tangles |
| 9 | 7801 to 8400 | Subgraph occurrence probabilities, fundamental order, poset methods |
| 10 | 8401 to 9000 | Finite cone decomposition, certified trace estimates, prescribed subgraphs |
| 11 | 9001 to 9600 | Derived graph inclusion and exclusion, indicator truncation, generalized types |
| 12 | 9601 to 10200 | Generalized expansions, side stepping statement and first exception bound |
| 13 | 10201 to 10800 | Limit formula, main spectral argument, irregular case, spreading introduction |
| 14 | 10801 to 11400 | Spreader probability estimates and transfer from bouquets |
| 15 | 11401 to 12000 | Spreading completion, bipartite case, refined probability power, algorithm |
| 16 | 12001 to 12600 | Fundamental order bound, algebraic models, congruence polyexponentials |
| 17 | 12601 to 13144 | Stronger coefficient notions, proposed weighted extensions, bibliography |

The first display lost a short macro span to output truncation. Lines 500 to 700 were reread in full. The display of lines 5201 to 6600 also had a truncated central span. Lines 5700 to 5900 and 5900 to 6200 were reread in full, covering that span. These overlap reads complete the coverage, rather than counting truncated output as read. Other large output searches were supplementary and are not the basis for the coverage claim.

The source contains an obsolete draft block inside `\jfignore{...}` between its early tangle discussion and the final loop section. That block was read as source text but was not treated as part of the rendered proof. The printed PDF comparisons below concern active material.

## What the proof actually does

The main result, Theorem 0.1.1, fixes a regular base graph B and epsilon, and bounds the probability of a new adjacency eigenvalue outside the Alon interval by C(B,epsilon)/n. It does not make C uniform over growing B. Theorem 0.1.3 gives matching powers for Ramanujan bases and sufficiently small fixed epsilon. The latter is sensitive to the model of random cover, since the set of feasible tangles can change.

The exact probabilistic starting point, Proposition 2.3.8, is

\[
\mathbb E_{\mathrm{symm}}(w,\mathbf t)
=\prod_{v\in V_B}(n)_{b_v}\prod_{e\in E_B}(n)_{a_e}^{-1}.
\]

Here b_v counts distinct lifted vertices above v and a_e counts distinct lifted edges above e. The leading power is n to the Euler characteristic of the walk graph. This is an uncentered exact probability formula, not a mixed centered moment estimate. Uniform permutation colors are independent. Half loops require involution probabilities and separate parity handling.

The proof has the following dependency chain.

1. Count coincidences in a revealed walk. A walk graph with order at least r needs at least r+1 coincidences. This controls the discarded high order part by a term of the form C k^(2r+2) n^(-r) Tr(H_B^k).
2. Expand the exact probability for each remaining walk class in powers of 1/n. Organize the classes into finitely many types by contracting degree two paths. Fixed order bounds the number of branch vertices and type edges.
3. A type plus its vector of path lengths determines whether its walk graph is a tangle. Increasing path lengths decreases the nonbacktracking spectral radius. Thus the permitted length vectors form an upper set in a finite product of the positive integers.
4. Dickson style finite generation turns that upper set into a finite union of cones. Inclusion and exclusion reduce the certified trace coefficients to finitely many cone sums.
5. In each cone sum split type edges by multiplicity at a large fixed cutoff M. Edges with fixed small multiplicities yield weighted convolutions of polyexponential functions based on the old Hashimoto spectrum. The high multiplicity part contributes at most the square root growth rate plus an arbitrarily small exponential slack.
6. Repeat this analysis jointly with prescribed finite subgraphs. Derived graph inclusion and exclusion then supplies expansions for the certified trace multiplied by the event that no low order tangle occurs.
7. Apply polynomials in the shift operator in the walk length. These annihilate unknown polyexponential principal parts. The generalized side stepping lemma localizes possible exceptional eigenvalues near old Hashimoto eigenvalues and bounds their probabilities through the first nonzero expansion coefficient.
8. The zeroth principal part cancels against the old spectrum. The first remaining possible order is at least 1, yielding the general O(1/n) probability bound. For regular graphs the Ihara and Bass relation converts a real nonbacktracking outlier mu into an adjacency eigenvalue mu+(d-1)/mu.
9. If the base is Ramanujan, only the bases plus or minus (d-1) remain outside the nonbacktracking bulk. Spreading estimates rule out new eigenvalues near these bases except through small components. This makes the tangle occurrence order the governing probability power.

The algebraic model discussion gives examples rather than an encompassing formal definition or a uniform theorem for every algebraic looking distribution. It allows single cycle permutations, prescribed finite cycle structures, fixed finite permutation constraints, and certain mild dependencies when the relevant probabilities retain polynomial expansion coefficients. Each proposed variant still needs its feasibility and expansion arguments checked.

## Three precise source defects

### 1. The printed lower bound on fundamental order is false

Theorem 3.3.4, printed pages 119 and 120, source lines 12070 to 12129, asserts

\[
\eta_{\rm fund}(B)>\sqrt{d-1}
\]

for every connected d regular base, allowing whole loops. Take B to be the bouquet of two whole loops. Then d=4, B has one vertex and two edges, and its Hashimoto matrix has constant row sum 3. B itself is a feasible strict tangle of order 1 because 3 is greater than sqrt(3). Every connected graph of nonpositive order without half loops has Hashimoto spectral radius at most 1, so eta_fund(B)=1. This contradicts the displayed bound.

The proof's error is explicit. After contraction to one vertex with s+1 whole loops, it writes that the Hashimoto spectral radius is s. It is 2s+1. The source's own preceding bouquet calculation, lines 12035 to 12042, uses the correct condition 2m-1>sqrt(d-1), and hence already conflicts with Theorem 3.3.4.

This is not a new theorem or a first discovery claim. The authors' [2019 article VI, Theorem 8.1](https://arxiv.org/html/1911.05775v1#S8.SS1) states the correct lower bound for the tangle power,

\[
\tau_{\rm tang}\ge
\left\lfloor\frac{\sqrt{d-1}+1}{2}\right\rfloor,
\]

with equality in the appropriate whole loop permutation model. For the standard model without half loops, the strict tangle definitions coincide with the 2014 quantity used in this counterexample. This later source prevents presenting the correction as a fresh spectral contribution.

### 2. The broad Taylor remainder range is false

Theorem 2.3.10, printed page 56, source lines 7113 to 7130, claims that for any potential walk of length k at most n/2 and any fixed r,

\[
\mathbb E_{\rm symm}
=n^{\chi}\left(p_0+\cdots+p_{r-1}n^{1-r}+\operatorname{error}(k,n)n^{-r}\right),
\quad |\operatorname{error}(k,n)|\le C_r k^{2r}.
\]

Here is an explicit counterexample to this range. Use the two whole loop base, label its two colors a and b, and prescribe the potential closed nonbacktracking walk a^m b^m. Its trajectory is the cycle on the same m lifted vertices for each color. Its graph has m vertices and 2m edges. Thus k=2m, chi=-m, and

\[
\mathbb E_{\rm symm}=\frac{(n)_m}{(n)_m^2}
=\frac1{(n)_m},
\qquad
n^{-\chi}\mathbb E_{\rm symm}
=F_n(m)=\frac{n^m}{(n)_m}.
\]

At r=1 the constant coefficient p_0 is 1. Set n=4m, so k=n/2. The claimed estimate implies F_n(m) at most 1+C_r n/4. But

\[
\log F_n(m)=\sum_{j=0}^{m-1}-\log(1-j/n)
\ge \frac{m(m-1)}{2n}=\frac{n-4}{32}.
\]

This exponential lower bound contradicts the polynomial upper bound as n increases. The potential walk is feasible and strictly nonbacktracking, including at its closing edge, so the issue is not an inadmissible word.

The printed proof bounds derivatives of a product of inverse factors without the multiplicative size of the product. The intended logarithmic walk lengths lie in the much smaller regime k squared at most n. An exponential factorial correction is uniformly bounded there, so restricting the expansion range can repair this input for the main application. This report has not rewritten or independently verified every dependent theorem after that repair.

### 3. A deterministic trace bound loses a factor n

The proof of Lemma 2.5.13, printed page 85, source lines 9426 and 9434, bounds the certified trace by Tr(H_B^k). In general the elementary deterministic bound is n Tr(H_B^k), because a closed base walk can have up to n closed lifts.

For an exact counterexample take B=K4, n=2, and all edge permutations equal to the identity. The lift is two disjoint copies of K4. At k=3 every strictly nonbacktracking closed walk traces a triangle. A triangle has Hashimoto spectral radius 1, below sqrt(2), and order 0, so these walks are all certified for any truncation order r at least 1. There are 24 such rooted oriented walks per K4. The certified trace is 48 and Tr(H_B cubed)=24.

This refutes the displayed deterministic assertion. It does not refute the main spectral theorem. Truncating derived graphs one order later is a possible route to compensate for a factor n, but it requires an actual joint expectation argument rather than the displayed bound. No completed repair is claimed here.

## Consequences for growing bases and remaining obligations

The fixed base theorem cannot simply be read uniformly over all bases with bounded degree. Its constants depend on B through the number and lettering of types, the old spectrum in the annihilating shift polynomial, spectral separations in convolution estimates, and spreading parameters. For example, the spreading proof uses walks of length greater than 6 times the number of base vertices and a spreading parameter bounded in terms of the square of that number. These losses are structural in the written argument.

Tangle occurrence probabilities provide the appropriate test for a growing base claim. A fixed order r feasible tangle has probability of order n^(-r) for one specified base placement, while a base with many independent placements supplies many opportunities. This is precisely the mechanism behind the independent session's growing base obstruction. Proving an exact threshold requires joint occurrence control and a test vector in the new spectral subspace. Counting subgraphs alone does not establish a new eigenvalue, because an old base eigenvalue can already be large.

The reviewed source chain does not by itself establish a new optimal nonasymptotic bound for growing base size. A positive theorem would need explicit uniform constants or a different proof. A falsification theorem can instead construct independent local placements, produce a local adjacency witness above the universal cover edge, project it away from the old fibre constant space, and keep that projection loss small. Those are separate obligations from improving a scalar permutation moment.

Checks actually performed here are complete TeX source coverage, hash and line count checks, targeted PDF fidelity checks, exact symbolic finite matrix counts in `check_source_examples.py`, and primary source comparison with the later Theorem 8.1. The whole 2019 series, discovery priority for the defects, and an end to end repaired proof of the 2014 manuscript remain outside this report.
