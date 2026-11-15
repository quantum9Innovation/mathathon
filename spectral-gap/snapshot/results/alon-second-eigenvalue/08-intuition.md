# Intuition at several altitudes

## One sentence

Random $d$-regular graphs look spectrally like the infinite $d$-regular tree after rare finite subgraphs with abnormal non-backtracking growth are excluded, and selective traces make that exclusion precise enough to prove near-Ramanujan spectrum (Theorems 1.1 and 6.6).

## One paragraph

A closed walk explores a random graph much as it explores a tree, except where it creates cycles or dense local patterns. Most such patterns are harmless. The dangerous ones are supercritical tangles, whose non-backtracking growth is at least $\sqrt{d-1}$. A hypercritical tangle can force a second adjacency eigenvalue beyond $2\sqrt{d-1}$ because its tree completion supports an unusually concentrated test function. These tangles are rare with probability governed by $n^{-\operatorname{ord}(\psi)}$, but they occur often enough to spoil the naïve asymptotic trace expansion. Friedman deletes every walk containing a dangerous short segment, groups the rest into compressed new types, and proves their growth remains strictly below the Ramanujan error scale. Expansion on graphs with and without tangles restores enough information about the actual spectrum. Strongly irreducible traces then convert adjacency eigenvalues into roots $\mu$, and one logarithmic-power comparison finishes the bound (Sections 2 through 13).

## Five-minute whiteboard version

### 1. Write the target and the trace obstacle

For fixed $\epsilon>0$, the goal is

$$
\Pr\!\left[\max_{i>1}|\lambda_i|\leq2\sqrt{d-1}+\epsilon\right]
=1-O(n^{-\tau}).
$$

A trace power both counts closed walks and exposes large eigenvalues through $\lambda^k$. The ordinary irreducible trace has a $1/n$ expansion, but some coefficient functions grow faster than the permitted error $(d-1)^{k/2}$. Draw a small loop-rich graph and label it danger.

### 2. Turn danger into a local spectral computation

Complete the finite graph $\psi$ to $\operatorname{Tree}_d(\psi)$. Draw Figure 1's finite core with hanging trees. Then write

$$
\lambda_1(\operatorname{Tree}_d(\psi))>2\sqrt{d-1}
\iff
\lambda_{\mathrm{Irred}}(\psi)>\sqrt{d-1}.
$$

Explain that a bounded test function on this infinite completion can be moved into any large finite graph containing $\psi$.

### 3. Draw the selective correction

Delete any subwalk of length at most $S$ that traverses a supercritical tangle. Draw Figure 2's form, suppress its beads, and partition long versus fixed type edges. On the board, place the key inequality:

$$
W_{\widetilde T,S}(M_1,M_2)
\lesssim(\sqrt{d-1}-\eta)^{BM_1+M_2}.
$$

This is stronger than just saying dangerous walks are rare. It is a uniform exponential statement inside each compressed type.

### 4. Show why convergence returns

Put next to it the inverse length-sum factor:

$$
(d-1)^{-(BM_1+M_2)/2}.
$$

Multiplying gives

$$
\left(1-\frac\eta{\sqrt{d-1}}\right)^{BM_1+M_2},
$$

whose sum over multiplicities is finite. That is the whole reason new types matter. All selective expansion coefficients become d-Ramanujan, without computing them.

### 5. Restore the real graph and finish

Use a finite inclusion-minimal tangle set and Möbius inversion to analyze the event containing tangles. Subtract it. On the tangle-free event selective and actual traces match.

Now switch to strong traces. Each adjacency eigenvalue gives roots

$$
\mu_{1,2}=\frac{\lambda\pm\sqrt{\lambda^2-4(d-1)}}2.
$$

A nonreal pair has modulus $\sqrt{d-1}$. An outlier above the Ramanujan threshold has a larger real root. Finite differences annihilate unknown coefficients. Spreading keeps other non-Perron roots away from $d-1$. Choose $k\asymp\log n$ so one outlier dominates $n(d-1)^{k/2}$, then choose the expansion order to get the desired polynomial failure probability.

## Mathematical mechanism

Set $q=d-1$. After removing the trivial Perron direction, trace information can be imagined schematically as

$$
\sum_i\nu_i^k
=\underbrace{q^k(\text{unknown polynomial background})}_{\text{structured tree contribution}}
+\underbrace{O(k^cq^{k/2})}_{\text{allowed Ramanujan-scale noise}}
+\underbrace{O(k^cn^{-r}q^k)}_{\text{finite-expansion remainder}}.
$$

This is a conceptual compression, not an exact displayed theorem. A real outlier with $|\nu|>\sqrt q$ will dominate $q^{k/2}$ as $k$ grows. Two issues remain: unknown polynomial background and nonreal roots. Strong irreducibility and finite differences deal with the first, while even powers and the modulus of nonreal pairs deal with the second.

The selective proof is necessary only because this clean form fails for the ordinary trace at sufficiently high expansion order. It restores that form on a high-probability stratum where the actual and selective spectra agree.

## Geometric intuition

The $d$-regular tree supplies a universal geometric baseline. A first step has $d$ choices and subsequent non-backtracking steps have $q$ choices. The adjacency norm is nevertheless $2\sqrt q$, smaller than $dq^{k-1}$'s total count might initially suggest, because closed radial cancellations and spherical growth interact through Chebyshev-type recurrences.

Figure 1 visualizes a finite defect placed in this tree universe. The added branches do nothing unusual. The core determines whether return walks accumulate too quickly. That is why the threshold compares $\lambda_{\mathrm{Irred}}(\psi)$ with $\sqrt q$, not with $q$ or with $2\sqrt q$.

A tangle occurrence in a finite graph is like inserting that defect into an otherwise broad test space. The first test function concentrates near the defect, the second lives far away. Their two-dimensional span certifies $\lambda_2$ large.

## Combinatorial and algorithmic intuition

Think of each potential walk as a constraint satisfaction problem:

- A vertex requires choosing a label among $n$ possibilities.
- An edge labelled $\pi_j$ requires one permutation value.
- A repeated visit merges constraints.
- Incompatible constraints make a potential walk infeasible.

After vertex relabelling, the leading expectation is $n^{V-E}$. This is an order calculation rather than an algorithm for sampling walks.

Compression in Figure 2 is analogous to eliminating deterministic transitions in a state machine. Degree-two paths do not branch, so storing every bead wastes space. Store a single weighted transition with total length and endpoint letters. Selectivity is a local constraint on accepted paths. New types are a static encoding of that constraint, which lets dynamic path enumeration become a finite generating function calculation.

There is no implemented algorithm or software in the paper. This analogy only describes what the combinatorics is doing.

## What is surprising here?

1. **The hard part is not obtaining $2\sqrt{d-1}$ as a scale.** That is natural from the tree. The hard part is that finite bad subgraphs spoil an expansion just when higher orders would improve the eigenvalue bound (Section 2).
2. **Deleting walks can tell us about undeleted walks.** Section 9 expands both tangle and tangle-free strata, so selectivity disappears on the event used in the final proof.
3. **The expansion coefficients need not be known.** Earlier intuition might suggest computing enough of them explicitly. Lemma 11.1 eliminates their influence by finite differences.
4. **The rate is governed by local tangle order.** A global spectral failure exponent has a finite combinatorial explanation through $E-V$ (Sections 4 and 6).
5. **Critical and hypercritical are not interchangeable.** Supercritical includes equality and determines the upper proof cutoff. Hypercritical requires strict inequality and drives the lower failure evidence.

## Small examples

### Example A: $d=4$ and two whole-loops

Here $q=3$, $m=2$, and $x=2m-1=3>\sqrt3$. The loop tangle has order $m-1=1$, and

$$
\alpha=3+\frac33=4>2\sqrt3.
$$

Its occurrence probability has order $1/n$. Thus an order-$1/n$ family of bad local configurations can force a severe second eigenvalue, while the complementary event still has probability $1-O(1/n)$. This makes the $\tau_{\mathrm{fund}}(\mathcal G_{n,4})=1$ scale tangible (Theorems 1.1, 2.11, and 6.8).

### Example B: critical equality at $d=10$

Here $q=9$ and $\sqrt q=3$. For $m=2$, $2m-1=3$ exactly, so the tangle is critical and

$$
\alpha=3+\frac93=6=2\sqrt3.
$$

It has order 1 but gives no strict Ramanujan violation by this test. The next loop count $m=3$ is hypercritical of order 2. Hence $\tau_{\mathrm{fund}}=1$ while the hypercritical lower-bound exponent is $s=2$. This is the paper's one-step gap when $(\sqrt q+1)/2=2$ is integral (Theorem 1.1 and Definition 4.3).

### Example C: Figure 2 has order 0 despite repeated traversal

The triangle is traversed twice, but repetition changes multiplicities rather than the traced graph. There are five distinct form vertices and edges, and two type vertices and edges after suppression. Both orders are 0. An intuitive count of ten steps divided by anything would miss the invariant that determines factorial probability.

## What would the naïve baseline do?

A naïve high trace argument would:

1. Use $\operatorname{Tr}(A^k)$ or the ordinary irreducible trace.
2. Expand its expectation through some finite order in $1/n$.
3. Bound dropped terms by earlier expansion results.
4. Choose $k\asymp\log n$ and conclude.

The failure is not algebraic laziness. At high enough order the intermediate $g_i$ are not d-Ramanujan, because tangles force large second eigenvalues with probability comparable to the expansion order being used (Theorems 2.11 and 2.12). On those graphs, a logarithmic trace is large exactly when one hopes it is negligible. Simply estimating harder inside the same type framework does not repair this.

Selectivity modifies the object so that every expansion coefficient has the required growth. Section 9 then pays the separate cost of connecting it back to the original trace.

## What does not follow intuitively or formally?

- It does not follow that random graphs are exactly Ramanujan with high probability. The final estimate loses uniformity as $\epsilon\to0$ (Section 15).
- It does not follow that a low probability alone proves a tangle-free theorem directly. The tangle-free bad event also needs a spectral argument, supplied by selective expansion and sidestepping.
- It does not follow from Figure 1 that every bad graph contains a large tree. Only the finite tangle is needed in the graph.
- It does not follow that contiguity transfers all explicit exponents. It transfers vanishing bad events (Corollary 1.4).
- The closing mention of numerical experiments supplies no plotted evidence in this document. It is a remark, not an experimental result evaluated here.
