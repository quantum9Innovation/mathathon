# Intuition at several altitudes

## One sentence

**Paper, paraphrased:** To bound the typical non-backtracking spectrum, first remove rare tangles from the path sum, then estimate the centered tangle-free operator by traces and path counting, and finally return to the adjacency spectrum through Ihara-Bass.

## One paragraph

**Interpretation:** Very long closed walks contain the desired spectral information, but rare small subgraphs with several cycles dominate their expected number. Trying to average over all configurations therefore asks the wrong probabilistic question. On a typical graph, logarithmic neighborhoods have at most one cycle, so walks supported on two or more local cycles can be deleted without altering $B^\ell$. Once those walks are gone, centered products of random matching entries acquire cancellation. Trace circuits built from the remaining paths can be organized by vertices $s$, distinct pairs $a$, and cycle rank $g$. Labelings provide $n^s$, matching costs remove roughly $n^{-a}$, and path entropy provides the spectral growth factor. A second family of remainder matrices pays for the fact that tangle-free prefixes and suffixes can form a tangle after splicing, as Figure 2 shows. The $1/n$ factor in front of those remainders makes them harmless. The resulting centered norm scales like $(d-1)^{\ell/2}$, so an $\ell$-th root yields $\sqrt{d-1}$. In a lift, the same accounting works after replacing regular branching by the base graph's non-backtracking growth rate $\rho$.

## Five-minute whiteboard version

1. **Write the target and the obstruction.**

   For even $k$, adjacency trace bounds would control $\mu_2\vee|\mu_n|$. But rare dense subgraphs with probability $n^{-c}$ can dominate $\mathbb E\operatorname{tr}(A^k)$ when $k\gg\log n$. Write “expected full trace fails, whp spectral claim can still hold”.

2. **Change operators.**

   Write $B=MN$ on half-edges and $\lambda^2-\mu\lambda+(d-1)=0$. Explain that $\sqrt{d-1}$ on the $B$ side corresponds to $2\sqrt{d-1}$ on the $A$ side.

3. **Draw the tangle-free event.**

   A local neighborhood may contain one cycle but not two. On that event,

   $$
   B^\ell=B^{(\ell)}.
   $$

   Lemma 9 says its failure probability is $O((d-1)^{4\ell}/n)$.

4. **Delete, center, and show Figure 2.**

   Define $\underline M_{ef}=M_{ef}-1/(dn)$. On $x\perp\chi$,

   $$
   B^\ell x=\underline B^{(\ell)}x-\frac1{dn}\sum_kR_k^{(\ell)}x.
   $$

   Draw two unicyclic pieces. Their union can have two cycles, which is why $R_k^{(\ell)}$ appears.

5. **Show the two norm bounds.**

   $$
   \|\underline B^{(\ell)}\|\lesssim(\log n)^{15}(d-1)^{\ell/2},
   $$

   $$
   \sum_k\|R_k^{(\ell)}\|\lesssim(\log n)^{30}(d-1)^\ell.
   $$

   Say that the first is the sharp calculation and the second gets a $1/n$ discount.

6. **Trace and count.**

   Use $\|C\|^{2m}\leq\operatorname{tr}((CC^*)^m)$. Draw Figure 3's alternating circuit. Write the three costs,

   $$
   \text{labels}\times\text{canonical supports}\times\text{expected weight}.
   $$

   Use Figure 4 to explain why repeated returns around one cycle do not require independent marks.

7. **Take roots.**

   With $\ell\sim\kappa\log_{d-1}n$, $0<\kappa<1/4$,

   $$
   |\lambda_2|
   \leq\sqrt{d-1}(1+O(\log\log n/\log n)).
   $$

   Ihara-Bass converts $\eta=\log\log n/\log n$ on the non-backtracking side to $O(\eta^2)$ on the adjacency side. Conditioning on simplicity gives Friedman's theorem on the uniform simple model.

8. **State the lift replacement in one line.**

   New eigenvalues live on $H^\perp$. Canonical path classes now have growth $\rho^s$ from $\|(B^*)^s\delta_e\|_1\leq c_\rho\rho^s$, so every $\sqrt{d-1}$ becomes $\sqrt\rho$, with $\rho$ finally taken down to $\rho_1$.

## The mathematical mechanism

### Why $\sqrt{d-1}$ appears for non-backtracking paths

**Interpretation anchored in Ihara-Bass:** On a $d$-regular tree, a non-backtracking step has $d-1$ forward choices. A centered second-moment calculation sees cancellation in independent directions and gains a square root of that branching scale. Meanwhile, if $\lambda=r\sqrt{d-1}$, then

$$
\mu=\lambda+\frac{d-1}{\lambda}
=\sqrt{d-1}(r+r^{-1}).
$$

At $r=1$ this is $2\sqrt{d-1}$. Real roots with $r>1$ describe nontrivial adjacency eigenvalues outside the bulk interval. The proof estimates a common restricted operator norm for $B^\ell$ and reads off $r\leq1+o(1)$.

**Caution:** The square-root threshold is not derived simply by counting $d-1$ children. That count alone would give the wrong scale $d-1$. It is the centered path-product expectation and the $2m$-moment root that govern the precise bound.

### Why tangles are the correct bad objects

A tangle is not defined as any dense graph. It is a visited support containing more than one cycle. These supports are especially costly to create and repeated in many high-power paths, yet their global occurrence is polynomially rare at the selected radius. Removing them changes little on a typical graph but removes exactly the configurations that poison expected moments.

### Why Figure 2 is more than an example

When a product over a path is split at a centered position, the desired matrix product assumes independent sums over prefix and suffix. If each sum is restricted only by its own tangle-free condition, their union may be forbidden. Therefore the product over approximately independent pieces includes paths the original tangle-free matrix had discarded. This overcount is the entire analytical origin of $R_k^{(\ell)}$.

### Why Figure 4 makes the entropy bound plausible

The path has a triangle with attached trees. Its fourth step closes the triangle. Later traversals around the same triangle look like new returns if every return is counted independently. But no second independent cycle is present. The tangle-free condition says there is only one independent cycle on each strand. An enhanced record of the first closure and the eventual exit reconstructs all repeated excursions. This is the difference between entropy depending on path length and entropy depending on cycle rank.

### Why the centered trace has an overall $n$, while the remainder does not

The centered circuit's support $G_\gamma$ is connected. A tree-like circuit with $g=0$ can have $a=s-1$, so one global factor of $n$ remains after the power bookkeeping. In the remainder support $G_\gamma^k$, every component contains a cycle, hence $a\geq s$. The $n^s$ labelings are fully discounted even without that global factor. This is why Proposition 18 lacks the trace's usual $n$ after the sum, although its moment bound is used less sharply than Proposition 14's.

## Geometric and topological intuition

- **Cycle rank is latitude in the path space.** With fixed $s$ and $g$, $a=s+g-1$ for a connected support. Increasing $g$ adds an edge and makes its random realization another $1/n$ rarer. This is why excess edges have a geometric discount.
- **The adjacency threshold is the bottom of a quadratic branch.** The map $r\mapsto\sqrt{d-1}(r+r^{-1})$ has its minimum at $r=1$. Small positive distance $r-1$ above the minimum produces only quadratic excess in $\mu$, explaining Eq. 2's squared scale.
- **The lift inherits a base direction.** The space $H$ is like pulling back functions from the base. $H^\perp$ contains zero-mean fluctuations within each fiber, exactly where genuinely new lift spectrum can occur.
- **Universal cover growth replaces homogeneous branching.** In a regular tree the growth is uniform. In an irregular universal cover it depends on direction and position, but large non-backtracking path counts have exponential rate $\rho_1$. The strict surrogate $\rho>\rho_1$ buys a clean geometric upper bound.

## Algorithmic intuition

The proof can be remembered as a deterministic-program wrapper around two probabilistic estimates:

```text
Choose logarithmic block length ell
Prove the graph is ell-tangle-free with high probability
On that event, replace B^ell by its tangle-free path matrix
Subtract the trivial Perron component through restriction
Center the surviving random path weights
Account exactly for nonfactoring splices with remainder matrices
Bound centered and remainder operators by separate trace circuits
Choose moment order m of order log n / log log n
Sum by support size, distinct pairs, and excess cycle rank
Take the ell-th root and then condition or transform the model as needed
```

This is not an algorithm for constructing graphs. It is a proof architecture.

## What is surprising?

1. **The naive direct expectation fails at exactly the useful long-walk regime.** The solution is not to abandon moments but to modify the combinatorial summands before taking them.
2. **The remainder can be much larger than the centered term.** Its raw scale is $(d-1)^\ell$, compared with $(d-1)^{\ell/2}$. Multiplying by $1/n$ and taking an $\ell$-th root makes this acceptable.
3. **A path with one cycle can be reused unboundedly without causing combinatorial explosion.** The correct cycle-rank encoding is what turns tangle-freeness into an entropy estimate.
4. **The adjacency error is squared relative to the non-backtracking error.** This follows from the minimum of $\lambda+(d-1)/\lambda$ at $\lambda=\sqrt{d-1}$, not from a loose inequality.
5. **An arbitrary-base lift theorem still has a clean universal growth scale.** The parameter $\rho_1$ comes directly from the fixed base non-backtracking operator, so irregularity enters through path entropy rather than destroying the proof structure.

## What does the naive baseline do?

### Naive trace baseline

Compute $\mathbb E\operatorname{tr}((A-(d/n)J)^k)$ for $k\gg\log n$. Rare dense or disconnected configurations dominate this expectation. The calculation can produce a huge bound even though the spectral event is typical.

### Naive matrix-norm baseline

Use $\|B^\ell\|\leq\|B\|^\ell$ or a rough entrywise estimate. This gives the scale $(d-1)^\ell$, hence an $\ell$-th root of $d-1$, not $\sqrt{d-1}$.

### Naive centering baseline

Set $\underline B=\underline MN$ and claim that $\underline B^\ell=\underline B^{(\ell)}$. This loses the path restriction and reintroduces tangled supports.

### Naive path-count baseline

Store all repeated return times, or multiply independent-looking choices without accounting for repeated edges. Figure 4 demonstrates the resulting overcount, while Definition 10 demonstrates the need to distinguish consistency types.

## Small cases to retain

### Case 1: two unicyclic pieces

A prefix visits one cycle and returns to the splice. A suffix visits a different cycle. Each belongs to its own tangle-free family, but their union has two independent cycles. Therefore their support contributes to $F_k^\ell\setminus F^\ell$, which is exactly the support of $R_k^{(\ell)}$. This is the content of Figure 2.

### Case 2: one triangle toured repeatedly

The first tour creates one excess edge. All later tours repeat existing edges and create no new independent cycle. One enhanced short-cycle mark can describe the family, while marking all returns would incorrectly suggest increasing entropy. This is Figure 4's lesson.

### Case 3: a loop in a lift

In Figure 5, $\sigma_c=(1)(2\,3)$ leaves one fiber index fixed and swaps two others. The base loop becomes a loop at $21$ and a double edge between $22$ and $23$. Fiber permutation does not necessarily turn a loop into a loop at every copy, and it does not change the base projection used for path counting.

## The most useful mental compression

Imagine a ledger with three columns:

- **How many ways can names be assigned?** This gives powers of $n$ and local degree factors.
- **How many genuinely different supports and base projections exist?** This gives cycle-rank entropy and $\rho^s$.
- **What does the random matching or permutation cost?** This gives $n^{-a}$ and extra cancellation from consistent singletons.

The proof finishes because the ledger balances after summing over $s$ and $g$, leaving only manageable polylogarithmic losses before taking high roots.
