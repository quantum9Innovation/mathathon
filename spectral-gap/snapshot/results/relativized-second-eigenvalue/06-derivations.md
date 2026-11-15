# Derivations

**Label convention.** Each note distinguishes the paper's statement from **Derived** working. Repairs to printed formulas are always identified. No numerical code was run. Optional numerical checks are marked where useful, but all conclusions below come from symbolic reasoning.

Write $R=\rho(H_B)$ throughout these notes to reduce notation. This shorthand is not imposed on the paper.

## D1. Old and new traces, and the regular spectral dictionary

### Target

Prove the trace identities for new spectra and explain exactly why the critical adjacency threshold $2\sqrt{d-1}$ becomes the critical Hashimoto modulus $\sqrt{d-1}$.

### Where it appears

Equation (0.2), Definition 1.1.16, equation (0.9), Definition 1.1.9, and Section 2.7's opening paragraph.

### Inputs

- A degree-$n$ covering $\pi:G\to B$
- Old functions constant on fibres and new functions summing to zero on fibres
- Symmetry of $A_G$
- Ihara-Bass formula for $d$-regular graphs without half-loops

### Paper

For adjacency,

$$
\sum_{\lambda\in\operatorname{Spec}_B^{\mathrm{new}}(A_G)}\lambda^k
=\operatorname{Tr}(A_G^k)-\operatorname{Tr}(A_B^k).
$$

The same subtraction form is used for Hashimoto spectra. Ihara-Bass gives

$$
\det(\mu I-H_G)
=\det(\mu^2I-\mu A_G+(d-1)I)(\mu^2-1)^{-\chi(G)}.
$$

### Derived: why the old trace is subtracted once

Let $N=|V_B|$. Pullback gives an $N$-dimensional space of old functions, one pulled-back function for each function on $B$, not one per sheet. Covering degrees preserve local outgoing counts, so $A_G$ preserves both the old and new spaces. On old functions its restriction is exactly $A_B$. Therefore

$$
\operatorname{Tr}(A_G^k)
=\operatorname{Tr}(A_G^k\mid_{\mathrm{old}})
+\operatorname{Tr}(A_G^k\mid_{\mathrm{new}})
=\operatorname{Tr}(A_B^k)
+\sum_{\lambda\ \mathrm{new}}\lambda^k.
$$

**Type check.** $|V_G|=nN$, the old dimension is $N$, and the new dimension is $(n-1)N$. Replacing the second trace by $n\operatorname{Tr}(A_B^k)$ would be incorrect.

### Derived: adjacency to Hashimoto

Set $q=d-1$. For each adjacency eigenvalue $\lambda$, the determinant supplies two roots of

$$
\mu^2-\lambda\mu+q=0,
\qquad
\lambda=\mu+\frac q\mu,
\qquad
\mu_{\pm}=\frac{\lambda\pm\sqrt{\lambda^2-4q}}2.
$$

Their product is $q$. There are three cases:

1. If $|\lambda|<2\sqrt q$, the roots are non-real conjugates and
   $$|\mu|^2=\mu\overline\mu=q.$$
2. If $\lambda=\pm2\sqrt q$, the roots coincide at $\pm\sqrt q$.
3. If $\lambda>2\sqrt q$, the roots are real and positive. For $\mu\ge\sqrt q$,
   $$\frac{d}{d\mu}\left(\mu+\frac q\mu\right)
   =1-\frac q{\mu^2}\ge0,$$
   with strict increase for $\mu>\sqrt q$. Thus $\mu>\sqrt q$ is equivalent to $\lambda>2\sqrt q$. The reciprocal root is below $\sqrt q$.

The same argument with negative real roots handles $\lambda<-2\sqrt q$. Additional $\pm1$ Hashimoto roots are below the threshold for $q\ge2$, so they do not affect the large-eigenvalue conclusion.

**Hidden assumptions.** The clean quadratic uses regularity. For irregular graphs $A_G$ and $D_G-I$ need not share an eigenbasis, which is why the paper's irregular conclusion is weaker.

**Failure modes.** A theorem about the full Hashimoto radius cannot be used directly as a theorem about the new radius. The old dominant roots $\pm(d-1)$ may already exceed $\sqrt q$.

**Numeric check, optional.** Randomly choose $\lambda$ in each of the three ranges and compare the root moduli and $\lambda=\mu+q/\mu$. This supports, but is not needed for, the algebra.

**Remember this.** The adjacency Ramanujan interval $|\lambda|\le2\sqrt q$ corresponds exactly to all Hashimoto roots lying on or inside $|\mu|=\sqrt q$.

## D2. The factorial specialization formula

### Target

Derive Proposition 2.3.8 and its leading power $n^\chi$ without treating symmetrization as an unexplained normalization.

### Where it appears

Proposition 2.3.8, printed page 55, equation (2.21), and its rewriting at the start of Subsection 2.3.3.

### Inputs

A potential walk $(w,\mathbf t)$, its traced graph, $a_e$ used edges over base edge $e$, and $b_v$ distinct vertex labels over base vertex $v$. The base has no half-loops.

### Paper

$$
\mathcal E_{\mathrm{symm}}(w,\mathbf t)_n
=\prod_{v\in V_B}\frac{n!}{(n-b_v)!}
\prod_{e\in E_B}\frac{(n-a_e)!}{n!}.
$$

### Derived step 1: count trajectory labels

In the fibre over $v$, the $b_v$ distinct labels used by the walk can be placed in

$$
n(n-1)\cdots(n-b_v+1)=\frac{n!}{(n-b_v)!}
$$

ways. Independent relabeling in different base fibres gives the first product.

### Derived step 2: force the required permutation values

For a fixed base edge $e$, the walk determines $a_e$ distinct values of the uniform permutation $\sigma_e$. Once those values are fixed, the remaining $n-a_e$ values can be chosen in $(n-a_e)!$ ways among $n!$ permutations. The probability is therefore $(n-a_e)!/n!$. Independence across non-paired base edges and the inverse convention for opposite directed edges give the second product.

### Derived step 3: expose the leading exponent

Let $V$ and $E$ be the vertex and edge counts of the traced graph, so $\sum_v b_v=V$ and $\sum_e a_e=E$. Factor out one power of $n$ from each falling-factorial term:

$$
\begin{aligned}
\mathcal E_{\mathrm{symm}}
&=n^{V-E}
\prod_{v\in V_B}\prod_{j=0}^{b_v-1}\left(1-\frac jn\right)
\prod_{e\in E_B}
\prod_{j=0}^{a_e-1}\left(1-\frac jn\right)^{-1}\\
&=n^\chi\prod_{v}\prod_{j<b_v}\left(1-\frac jn\right)
\prod_{e}\prod_{j<a_e}\left(1-\frac jn\right)^{-1}.
\end{aligned}
$$

Consequently $\mathcal E_{\mathrm{symm}}=n^\chi(1+O(1/n))$ for fixed $a_e,b_v$, and its Taylor coefficients in $1/n$ are polynomials in those counts. This yields Definition 2.3.9,

$$
\mathcal E_{\mathrm{symm}}(w,\mathbf t)_n
=n^\chi\sum_{i\ge0}p_i(\mathbf a,\mathbf b)n^{-i}.
$$

**Dimensional check.** A graph with one vertex and no edges has $\chi=1$, so the leading factor is $n$, the number of possible lifts of that vertex. A nonempty finite graph with negative Euler characteristic has $\mathcal E_{\mathrm{symm}}\to0$.

**Half-loop modification.** Random fixed-point-free involutions count matchings rather than permutations. The edge factor becomes $(n-2a_e)!_{\mathrm{odd}}/n!_{\mathrm{odd}}$ for even $n$. Odd $n$ requires separate treatment of the one fixed point, as in Section 3.4.1.

**Hidden assumptions.** The prescribed values must be feasible, meaning they cannot force contradictory images under a permutation. If they are contradictory, the probability is zero.

**Failure modes.** The formula is not uniform without controlling $a_e$ and $b_v$ relative to $n$. Taylor remainders require a range such as the paper's $k\le n/2$ in the no-half-loop case.

**Intuition.** Every new distinct vertex supplies $n$ choices. Every forced edge supplies a probability approximately $n^{-1}$. Hence $\chi=V-E$ directly measures abundance.

**Numeric check, optional.** Enumerate all permutations for small $n$ and compare the two products with brute-force counts for a chosen feasible graph.

**Remember this.** Vertices produce factors of $n$, edges produce factors of $n^{-1}$, and their exponent is exactly $\chi$.

## D3. Fixed-subgraph occurrence probability

### Target

Derive Theorem 2.4.7's leading occurrence probability and see why prunedness is needed for the first-order lower bound.

### Where it appears

Theorem 2.4.7, printed pages 65 to 68, equations (2.35) through (2.38).

### Inputs

An étale $B$-graph $\phi:\psi\to B$ of order $s=-\chi(\psi)$, plus prunedness and positive order of every component for the second statement.

### Derived

Choose an injection on vertices. As in D2, the number of choices has leading order $n^{|V_\psi|}$, and requiring all $|E_\psi|$ edges has probability of leading order $n^{-|E_\psi|}$. Summing over injections gives

$$
\mathbb E[\operatorname{NumOccurs}(\phi,G)]
=n^{-s}+O(n^{-s-1}).
$$

The source sometimes prints $\operatorname{NumOccurs}(\phi,B)$ in this formula. The random second argument must be read as $G$.

Markov's inequality gives the upper bound $\Pr[\psi\text{ occurs}]\le n^{-s}+O(n^{-s-1})$.

For the lower bound, write $c=|\operatorname{Aut}(\phi)|$. Each actual $B$-subgraph isomorphic to $\psi$ corresponds to exactly $c$ injections. First-order inclusion-exclusion gives

$$
\Pr[\psi\text{ occurs}]
\ge \frac{n^{-s}}c+O(n^{-s-1})-O(\text{pairs of distinct copies}).
$$

Two distinct copies have a strictly larger union. Their union is pruned because both are pruned, and each component has positive order. Theorem 2.2.4 therefore gives order at least $s+1$. Applying the expected-occurrence estimate to the finitely many possible union shapes shows that pair events contribute $O(n^{-s-1})$. Hence

$$
\Pr[\psi\text{ occurs}]
=\frac{n^{-s}}c+O(n^{-s-1}).
$$

**Type check.** $s$ is an integer in the no-half-loop regime. The exponent is independent of $k$ because $\psi$ is fixed.

**Hidden assumptions.** The graph must be feasible over $B$. Pruned positive-order components are exactly what make every two-copy union strictly more expensive.

**Failure modes.** Without the union-order increase, pair intersections can share the leading order and a simple first-moment lower bound may fail. Automorphisms cannot be ignored when converting injections to unlabelled subgraphs.

**Intuition.** The easiest way to obtain a rare spectral obstruction is one copy of the least-order strict tangle. Higher-order tangles and repeated copies are lower-order effects.

**Remember this.** The order $s$ is simultaneously a graph invariant and the polynomial rarity exponent of a fixed subgraph.

## D4. From walk sums to type-form expansions

### Target

Explain how D2 yields an order-$r$ expansion and why there are only finitely many types to analyze.

### Where it appears

Lemma 1.3.5, Theorems 2.3.10 and 2.3.13, Proposition 2.3.16, and Theorem 2.3.23.

### Derived: order as the truncation parameter

A potential walk of order at least $r$ must make at least $r+1$ independent coincidences relative to its base walk. At a coincidence, a previously unrevealed permutation value must return to one of the at most $k$ previously seen labels, with conditional probability at most roughly $k/n$ for $k\le n/2$. Choosing the first $r+1$ coincidence positions introduces a binomial factor, and there are $n$ initial labels. The resulting contribution is bounded by

$$
C\binom{k}{r+1}(2k)^{r+1}n^{-r}
\le Ck^{2r+2}n^{-r}
$$

for each base walk, up to constants depending on $r,B$. Summing over base walks introduces $\operatorname{Tr}(H_B^k)$, giving Lemma 1.3.5's shape of remainder.

For all lower-order walks, truncate D2's Taylor series in $1/n$. The truncation error and the finite number of order classes give the usual bound

$$
|\operatorname{err}(k,n)|
\le Ck^{2r+2}\rho(H_B)^k n^{-r}.
$$

### Derived: finite types

Suppress degree-two vertices along beaded paths, retaining the starting vertex and vertices of degree at least three. Add orderings and base-edge lettering to get a type. For order below $r$, the paper derives from

$$
2|E_T|=\sum_v\deg(v)\ge2+3(|V_T|-1)
$$

and $|V_T|-|E_T|>-r$ that

$$
|E_T|<3r+1,\qquad |V_T|<2r+1.
$$

There are finitely many such graphs and, for fixed $B$, finitely many orientations, orderings, and letterings. Thus $\operatorname{Types}[r]$ is finite.

A form restores a positive beaded-path length $k_e$ and a base walk on each type edge. Local matrix-walk statistics make the coefficient contributions polyexponential in $\mathbf k$ with bases in $\operatorname{Spec}(H_B)$. Theorem 2.3.23 groups by type, form, lengths $\mathbf k$, and multiplicities $\mathbf m$ subject to $\mathbf m\cdot\mathbf k=k$.

**Type check.** Scalar $k$ is total walk length, while $\mathbf k$ stores subdivision lengths and $\mathbf m$ stores traversal multiplicities. Length cannot be confused with order.

**Hidden assumptions.** Strict non-backtracking is essential. Backtracking would allow a walk to enter only part of a beaded path and reverse, destroying this simple multiplicity bookkeeping.

**Failure modes.** A general expansion may exist without $B$-Ramanujan coefficients. Finiteness of types does not by itself control the infinite sums over lengths and multiplicities.

**Numeric check, optional.** Enumerate all connected pruned multigraphs satisfying these bounds for $r=1$ and $r=2$ to see why the number of types is finite but grows quickly.

**Remember this.** The finite skeleton controls the $1/n$ expansion. Infinite variable-length data remain to be controlled by certification.

## D5. $B$-Ramanujan functions and weighted convolutions

### Target

Derive the exact weighted-geometric example and explain why weighted convolutions preserve the $B$-Ramanujan class.

### Where it appears

Definition 1.3.6, Theorems 2.2.6, 2.2.10, 2.2.14, and Example 2.2.13.

### Paper

A $B$-Ramanujan function can be written

$$
P(k)=\sum_{\mu\in\operatorname{Spec}(H_B)}p_\mu(k)\mu^k+e(k),
$$

where for every $\varepsilon>0$ there is $C_\varepsilon$ such that

$$
|e(k)|\le C_\varepsilon(R^{1/2}+\varepsilon)^k.
$$

Equivalently, up to replacing $\varepsilon$, the error can carry polynomial factors in $k$.

### Derived: weighted geometric sum, with a source correction

Let $q=d-1$ and consider nonnegative $k_1,k_2$ with $k_1+2k_2=k$. Then

$$
F(k)=\sum_{k_1+2k_2=k}q^{k_1}q^{k_2}
=\sum_{j=0}^{\lfloor k/2\rfloor}q^{k-j}.
$$

For $k=2s$, put $u=k-j$ to get

$$
F(2s)=\sum_{u=s}^{2s}q^u
=\frac{q^{2s+1}-q^s}{q-1}
=\frac{q^{k+1}-q^{k/2}}{q-1}.
$$

For $k=2s+1$,

$$
F(2s+1)=\sum_{u=s+1}^{2s+1}q^u
=\frac{q^{2s+2}-q^{s+1}}{q-1}
=\frac{q^{k+1}-q^{(k+1)/2}}{q-1}.
$$

**Source correction.** Example 2.2.13 and Section 3.5 print different odd-$k$ variants. Neither equals the defining sum for every $k$. At $k=1$ the defining sum has only $(k_1,k_2)=(1,0)$, hence $F(1)=q$. The formula above gives $q$, which is the required consistency check.

### Derived: why the residue-class correction is still tame

The dominant term is $q^{k+1}/(q-1)$. The subtracted term has growth at most $q^{k/2}$, so each residue formula is $B$-Ramanujan. This illustrates why exact mod-$S$ structure is stronger than what the main proof needs.

### Derived: convolution closure mechanism

For ordinary convolution of $\alpha^kk^s$ and $\beta^kk^t$:

- If $\alpha=\beta$, factor $\alpha^k$ and expand $(k-j)^s j^t$. Power sums are polynomials in $k$, raising total polynomial degree by at most one.
- If $\alpha\ne\beta$, start with
  $$\sum_{j=0}^{k}x^{k-j}y^j=\frac{x^{k+1}-y^{k+1}}{x-y},$$
  then differentiate in $x,y$ to obtain polynomial coefficients.

For error growth:

- Two error factors still have at most polynomially many summands and retain the same exponential scale after a small increase in $\varepsilon$.
- If both weights $m_1,m_2\ge2$, then $k_1+k_2\le k/2$ on the weighted constraint. Even dominant $R^{k_1+k_2}$ bounds are only $R^{k/2}$.
- A mixed weight-$1$ polyexponential and an error term is handled by infinite convolution with rigorous tail estimates, as in Theorem 2.2.10 and Corollary 2.2.11. Factoring out the exponential base reduces the tail to a geometric series with ratio below one.
- A weight-$1$ error term combined with weights at least $2$ is subcritical for the same reason. Any polyexponential residue pattern is dealt with separately or absorbed into mod-$S$ structure.

**Hidden assumptions.** Finite sets of bases and fixed weights matter. Arbitrary infinite sums can destroy the $B$-Ramanujan class.

**Failure modes.** A uniform sharp polynomial prefactor is not preserved automatically. Allowing an arbitrarily small exponential $\varepsilon$ is what simplifies the estimates.

**Numeric check, optional.** Evaluate both sides of the odd and even formulas for random $q$ and $k\le20$. The $k=1$ identity is already an exact algebraic test.

**Remember this.** Certification only needs to produce finitely many weighted polyexponential-and-error convolutions. It does not need a single globally polyexponential formula.

## D6. Why certified traces produce finite cone sums

### Target

Prove that non-tangle certificates form an upper set and turn the certified coefficient sum into finitely many cone sums.

### Where it appears

Definitions 1.4.1 and 2.4.25 through 2.4.27, Proposition 2.4.28, Corollary 2.4.29, and Theorem 2.4.30.

### Paper

The truncated certified trace counts SNBC $k$-walks whose traced graph has order below $r$ and Hashimoto spectral radius strictly below $R^{1/2}$. For a type $T$, define

$$
U=\left\{\mathbf k\in\mathbb Z_{\ge1}^{E_T}:
\operatorname{VLG}(T,\mathbf k)\notin\operatorname{Tangle}_B\right\}.
$$

### Derived step 1: monotonicity makes $U$ upward closed

Suppose $\mathbf k\le\mathbf k'$ componentwise. Subdividing every type edge into longer paths cannot increase the dominant spectral radius, so

$$
\rho_H(\operatorname{VLG}(T,\mathbf k'))
\le \rho_H(\operatorname{VLG}(T,\mathbf k)).
$$

If the realization at $\mathbf k$ is certified, namely its radius is strictly below $R^{1/2}$, then the realization at $\mathbf k'$ is also certified. Hence $\mathbf k\in U$ implies $\mathbf k'\in U$.

**Source caution.** One sentence in the proof of Theorem 2.4.31 prints a negative exponent in the radius threshold. The defining certification and Proposition 2.4.28 require the positive $R^{1/2}$ threshold.

### Derived step 2: finitely many minimal certificates

The componentwise order on $\mathbb Z_{\ge1}^s$ is a product of copies of $\mathbb Z_{\ge1}$, up to an index shift. Each upper set has finitely many minimal elements. The paper proves this through Noetherian upper sets and finite products.

Thus there are $\mathbf p_1,\ldots,\mathbf p_s$ such that

$$
U=\bigcup_{i=1}^s\operatorname{Cone}(\mathbf p_i),
\qquad
\operatorname{Cone}(\mathbf p_i)=\{\mathbf k:\mathbf k\ge\mathbf p_i\}.
$$

### Derived step 3: inclusion-exclusion

Cone intersections are also cones:

$$
\operatorname{Cone}(\mathbf p_i)\cap\operatorname{Cone}(\mathbf p_j)
=\operatorname{Cone}(\max(\mathbf p_i,\mathbf p_j)),
$$

where $\max$ is componentwise. For an absolutely summable $f$,

$$
\sum_{\mathbf k\in U}f(\mathbf k)
=\sum_i\widehat f(\mathbf p_i)
-\sum_{i<j}\widehat f(\max(\mathbf p_i,\mathbf p_j))+\cdots,
\qquad
\widehat f(\mathbf p)=\sum_{\mathbf k\ge\mathbf p}f(\mathbf k).
$$

Collecting equal maxima gives finitely supported Möbius coefficients. Absolute convergence justifies rearrangement and the finite-support approximation used by the paper.

Applying this to the type-form coefficients gives Theorem 2.4.30's finitely many terms

$$
\sum_{\mathbf k\ge\mathbf k_0}
\sum_{\mathbf m\cdot\mathbf k=k}
W_{\mathcal T}(\mathbf m,\mathbf k)P_i(\mathbf k).
$$

**Type check.** $\mathbf k_0$ is a certificate vector, $W_{\mathcal T}$ counts walk patterns, and $P_i$ carries base-walk exponential contributions.

**Hidden assumptions.** Finite generation alone is not enough without cone intersections being cones. Absolute convergence, or a later analytic bound that legitimizes the relevant sums, is essential.

**Failure modes.** A strict tangle condition need not define an upper set without monotonicity. A non-strict tangle condition behaves differently, which is why the paper discusses separate limiting arguments for minimal tangles.

**Intuition.** Any sufficiently lengthened, spectrally tame realization is certified by finitely many coordinatewise lower bounds. Those lower bounds are the natural domains of weighted convolutions.

**Remember this.** "Certified" means both spectrally admissible and finitely decomposable into lower-bounded length regions.

## D7. Certified coefficient growth: short and long multiplicities

### Target

Expand the mechanism proving Theorem 2.4.31, especially why certification is needed and why the split uses $M$ rather than only multiplicities $1$ and $2$.

### Where it appears

Theorem 2.4.31, Lemma 2.4.32, and Lemma 2.4.34, printed pages 75 to 78.

### Inputs

A cone-bounded certified term, a fixed partition $E_T=E_{T,1}\sqcup E_{T,2}$, and $M\ge1/\varepsilon$. Short edges have $m_f\le M$, long edges have $m_f\ge M+1$.

### Derived: long-only case

Let all edges be long. Since $\mathbf m\cdot\mathbf k=k$ and every $m_f\ge M+1$,

$$
\sum_f k_f\le \frac{k}{M+1}.
$$

The polyexponential factor has a crude bound

$$
|P(\mathbf k)|
\le Ck^C R^{\sum_f k_f}
\le Ck^C R^{k/(M+1)}.
$$

The certified realization has subcritical walk growth, so the walk-count factor satisfies

$$
W_{\mathcal T}(\mathbf m)\le Ck^C R^{k/2},
$$

up to the polynomial-growth conventions of the paper. The number of pairs $(\mathbf m,\mathbf k)$ is polynomial in $k$ for a fixed type. Combining them gives

$$
|\operatorname{Term}|
\le Ck^C R^{k(1/2+1/(M+1))}.
$$

Choosing $M$ large makes $1/(M+1)$ smaller than the allowed exponential slack. A further slight enlargement of $\varepsilon$ absorbs $k^C$.

**Why certification matters.** If $W_{\mathcal T}$ itself allowed growth $R^{(1/2+\delta)k}$ for fixed $\delta>0$, no fixed choice of $M$ could recover an error below $R^{(1/2+\varepsilon)k}$ for all $\varepsilon$.

### Derived: short edges present

Define weighted lengths

$$
K_1=\sum_{f\in E_{T,1}}m_fk_f,
\qquad
K_2=\sum_{f\in E_{T,2}}m_fk_f,
\qquad K_1+K_2=k.
$$

Each walk traverses at most $M|E_{T,1}|$ short type edges. Break it into at most that many long-edge segments. Certification bounds each segment's growth by $R^{K_{2,i}/2}$ up to polynomial factors. Multiplication and bounded composition counting give

$$
W_{\mathcal T}(\mathbf m)\le Ck^C R^{K_2/2},
$$

with the sharper expression written in terms of $K_2$ rather than all of $k$.

For each finite short-multiplicity vector, define a short factor $Q_1(K_1,\mathbf m_1)$ by summing polyexponential short-edge contributions, and a long factor $Q_2(K_2)$ by summing the remaining weighted walk contributions. Then $Q_1$ is polyexponential, $Q_2$ has subcritical growth, and the original term is their weighted convolution. Section 2.2's closure results apply. There are finitely many $\mathbf m_1$ and partitions, so their total remains $B$-Ramanujan.

**Type check.** $K_1,K_2$ are weighted lengths summing to $k$, not graph orders or cutoffs.

**Hidden assumptions.** The type is fixed and the finite short-multiplicity enumeration really is finite. Constants may depend on $M$, $\mathcal T$, $B$, and the target $\varepsilon$.

**Failure modes.** Letting $M$ grow with $k$ would invalidate the finite-case decomposition. Overlooking certificate cones could leave unbounded summation regions.

**Intuition.** Frequently repeated type edges force many distinct beaded-path lengths to be small in total, which weakens their exponential contribution. Certification controls the ordinary walk growth between them.

**Numeric check, optional.** A small finite type can be used to compare different $M$ thresholds computationally, but this would only illustrate, not establish, the asymptotic estimate.

**Remember this.** Long multiplicities supply extra decay in $R$, and short multiplicities leave a finite convolution problem. Certification supplies the square-root-scale walk bound in both cases.

## D8. Recovering the true tangle-free trace

### Target

Derive the subtraction that turns certified-trace expansions into Theorem 2.1.1, and explain the unconditioned indicator.

### Where it appears

Sections 1.5.1, 2.5.4, and 2.7, especially Theorems 2.1.1 to 2.1.3.

### Derived

Write $H_r$ for the event that $G$ contains a tangle of order below $r$, and $T_r$ for its complement. Then $\mathbb I_{T_r}=1-\mathbb I_{H_r}$ and

$$
\begin{aligned}
\mathbb E[\mathbb I_{T_r}\operatorname{CertTr}_{<r}]
&=\mathbb E[\operatorname{CertTr}_{<r}]
-\mathbb E[\mathbb I_{H_r}\operatorname{CertTr}_{<r}].
\end{aligned}
$$

Theorem 2.1.2 gives a $B$-Ramanujan expansion for the first expectation. Theorem 2.5.1 gives such an expansion for the second, using generalized $\Omega$-types that retain a fixed tangle and the walk simultaneously. Thus the left side has the same expansion type.

On $T_r$, every SNBC walk of order below $r$ is certified, since otherwise its graph would be a tangle of order below $r$. Hence

$$
\mathbb I_{T_r}\operatorname{CertTr}_{<r}(G,k)
=\mathbb I_{T_r}\operatorname{SNBC}_{<r}(G,k).
$$

Replacing $\operatorname{SNBC}_{<r}$ by the full trace only loses walks of order at least $r$. D4's order bound shows that their contribution fits $Ck^{2r+2}R^kn^{-r}$. This proves the schematic conclusion

$$
\mathbb E[\mathbb I_{T_r}\operatorname{Tr}(H_G^k)]
=\sum_{i=0}^{r-1}P_i(k)n^{-i}+O(k^{2r+2}R^kn^{-r}),
$$

where every $P_i$ is $B$-Ramanujan.

**Type check.** $\mathbb E[\mathbb I_T X]$ is not $\mathbb E[X\mid T]$. The latter would require division by $\Pr[T]$ and would have different coefficients.

**Failure modes.** A tangle-containing graph cannot simply be assigned its full raw certified trace and expected to satisfy the same coefficient bounds. That is why the second, tangle-present expansion is proved separately.

**Source cautions.** Theorem 2.4.25's prose mentions order below $r$, but its formal set has no order restriction. The order restriction is properly applied in the truncated certified trace of Definition 2.4.27. Section 2.7 also drops $\operatorname{Tr}$ in some displays, which must be restored.

**Remember this.** Prove two certified expansions, subtract them, and only then exploit equality with the true trace on tangle-free graphs.

## D9. Side-stepping: annihilate, localize, and balance

### Target

Derive the logic of Lemma 2.6.7 from the abstract partial-trace expansion.

### Where it appears

Sections 2.6.1 through 2.6.5, especially equations (2.57) through (2.73) and (2.74) through (2.92).

### Inputs

Along a sequence of length moments,

$$
\mathbb E\sum_{i=1}^{\gamma n}\mu_i^k
=P_0(k)+P_1(k)n^{-1}+\cdots+P_{r-1}(k)n^{1-r}
+\operatorname{err}_r(n,k),
$$

where each coefficient is polyexponential in bases $\ell\in L$, each non-real $\mu_i$ lies in $|\mu_i|\le\tau_0$, every larger real $\mu_i$ is bounded by $\tau_1$, and the error has both $n^{-r}\tau_1^k$ and lower-growth parts.

### Derived step 1: shift algebra

Let $(Sf)(k)=f(k+1)$. Then

$$
Q(S)\mu^k=Q(\mu)\mu^k.
$$

Moreover, for degree $p<D$,

$$
(S-\ell)^D\ell^kk^p
=\ell^k\sum_{j=0}^D(-1)^{D-j}\binom Dj(k+j)^p=0,
$$

because the $D$th finite difference of a polynomial of degree below $D$ vanishes.

Choose $D$ even and greater than all polynomial degrees in the coefficients. Set

$$
Q(z)=\prod_{\ell\in L}(z-\ell)^D.
$$

Then $Q(S)P_i(k)=0$ for every coefficient, and $Q(\mu)\ge0$ for real $\mu$.

### Derived step 2: exceptional eigenvalues survive positively

Choose even $k$. If $\mu_j$ is real with $|\mu_j|>\tau_0+\varepsilon$ and is at distance more than $\delta$ from every $\ell\in L$, then

$$
|Q(\mu_j)|\ge\delta^{|L|D},
\qquad Q(\mu_j)\mu_j^k
\ge\delta^{|L|D}(\tau_0+\varepsilon)^k.
$$

After putting absolute-value bounds on small complex eigenvalues and on the shifted error, the abstract expansion gives a schematic inequality

$$
\delta^{|L|D}(\tau_0+\varepsilon)^k
\Pr[\mathrm{Exception}_n(\delta,\varepsilon)]
\le Ck^C\left(n\tau_0^k+(\tau_0+\varepsilon/2)^k
+\tau_1^kn^{-r}\right).
$$

Divide by $(\tau_0+\varepsilon)^k$. The three ratios are

$$
n\left(\frac{\tau_0}{\tau_0+\varepsilon}\right)^k,
\quad
k^C\left(\frac{\tau_0+\varepsilon/2}{\tau_0+\varepsilon}\right)^k,
\quad
k^C\left(\frac{\tau_1}{\tau_0+\varepsilon}\right)^kn^{-r}.
$$

The first two decay exponentially in $k$ after absorbing the factor $n$ or polynomial $k^C$. The third is controlled by choosing $r$ large relative to the logarithmic size of $k$. Taking $k$ even and proportional to $\log n$ makes all three as small as any prescribed negative power of $n$. Taking $\delta=n^{-\theta}$ with $|L|D\theta$ small keeps the prefactor $\delta^{-|L|D}$ from reversing that gain.

### Derived step 3: isolate one base

For a fixed $\ell$, use

$$
Q_{\ell,D}(z)=\prod_{\ell'\in L\setminus\{\ell\}}(z-\ell')^D.
$$

This annihilates the other bases but not the $\ell^k$ coefficient. Eigenvalues within $\delta$ of another $\ell'$ contribute at most $O(\delta^D)$ after applying $Q_{\ell,D}$. Eigenvalues near $\ell$ satisfy $Q_{\ell,D}(z)=Q_{\ell,D}(\ell)+O(\delta)$. The error balances give, after division by $\ell^kn^{-j}Q_{\ell,D}(\ell)$,

$$
p_{\ell,j}(k)+O(n^{-1})
=n^j\mathrm{Near}_n(\ell,n^{-\theta})+O(n^{-1})
$$

when all lower $\ell$-coefficients vanish. The left side is independent of $n$ aside from the error, while the right side is independent of $k$. Letting $n\to\infty$ shows that $p_{\ell,j}$ is constant and gives the limit formula.

Finally, if $P_0=\cdots=P_{j-1}=0$, every base-near count is $O(n^{-j})$ by this argument, and every away-from-base exception has the same bound by step 2. Their union gives $\Pr[\mathrm{AbsoluteException}_n]=O(n^{-j})$.

**Type check.** $\mathrm{Near}_n$ is an expected count, so multiplication by $n^j$ is plausible. The probability bound arises only after applying a union bound over at most $\gamma n$ eigenvalue indices.

**Hidden assumptions.** Positive real large eigenvalues and non-real eigenvalues confined to the disk are essential for this proof structure. The finite basis set $L$ must be fixed before choosing $D$, $\theta$, and $r$ in the prescribed order.

**Failure modes.** Applying one moment at one $k$ without the polynomial filter would leave all unknown polyexponential coefficients in the estimate. A fixed $k$ also cannot turn polynomial factorial errors into spectral thresholds.

**Numeric check, optional.** Test $Q(S)$ on synthetic moments formed from a few real bases and polynomial coefficients, then verify exact annihilation when $D$ exceeds the degrees.

**Remember this.** Side-stepping does not calculate unknown coefficients. It filters them out and transfers the order of the first nonvanishing coefficient into an eigenvalue-probability exponent.

## D10. Completing the $O(n^{-1})$ main proof

### Target

Connect D8 and D9 to Theorem 0.2.6 and then to Theorem 0.1.1, while making the required old-trace subtraction and tangle-event bookkeeping explicit.

### Where it appears

Section 2.7, printed pages 102 to 104, and the Ihara conversion at its opening.

### Derived: new trace on tangle-free graphs

Pointwise for every cover,

$$
\sum_{\mu\in\operatorname{Spec}_B^{\mathrm{new}}(H_G)}\mu^k
=\operatorname{Tr}(H_G^k)-\operatorname{Tr}(H_B^k).
$$

Multiply by $\mathbb I_{T_r}$ and take expectations. D8 gives an expansion for the tangle-free full trace. The old trace is deterministic and is multiplied only by the tangle-free probability.

The loop calculation of Theorem 1.3.4 identifies the $n^0$ coefficient's principle part as $\operatorname{Tr}(H_B^k)$. Subtracting the old trace therefore kills the new expansion's principle part at level zero. The abstract coefficients $(\widetilde P_i)$ have no level-zero dominant polyexponential obstruction.

**Source correction.** Section 2.7's display $\widetilde P_i=P_i+p_i\operatorname{Tr}(H_B^k)$ hides a sign and indexing convention involving the tangle-free probability. At level zero the needed identity is a subtraction of $\operatorname{Tr}(H_B^k)$, with later tangle-probability corrections carrying their separate signs. Equation (2.93) should not be read as a literal probability asymptotic for the tangle-free indicator without restoring its constant and indicator conventions.

### Derived: apply side-stepping with $j=1$

Use an abstract partial trace whose random eigenvalues are the new Hashimoto eigenvalues on the tangle-free event and zero on tangle cases. Large non-real eigenvalues lie inside $\tau_0$ by hypothesis, while real outliers can be localized by D9.

Since the level-zero principle part vanishes, side-stepping applies with $j=1$ and yields an $O_\varepsilon(n^{-1})$ probability of a new eigenvalue beyond $\tau_0+\varepsilon$ on that event.

The complementary tangle event is also $O(n^{-1})$: there are finitely many minimal tangles below the chosen order, every one has positive order, and D3 makes each occurrence probability $O(n^{-1})$. Adding these two events gives the required $O(n^{-1})$ bound without forgetting tangle-containing graphs.

For regular $B$, set $q=d-1$, $\tau_0=\sqrt q$, and $\tau_1=R=q$ as a coherent outer-bound choice. By D1, non-real roots lie on $|\mu|=\sqrt q$, and every Hashimoto root has modulus at most $q$ under the covering degree bounds. Theorem 0.1.1 follows by translating large Hashimoto roots into large adjacency eigenvalues.

**Source corrections needed in the printed parameter list.** Definition 2.6.4 requires $\tau_0<\tau_1$, but printed page 103 sets $\tau_1=\tau_0^{1/2}$, which is smaller when $\tau_0>1$. Its last sentence also uses $\tau_0^{1/2}+\varepsilon$ instead of Theorem 0.2.6's $\tau_0+\varepsilon$. These are not harmless alternative parameterizations. The corrected schematic above uses the abstract definition and the main theorem's stated threshold.

**Hidden assumptions.** Choose $r$ sufficiently large before invoking side-stepping. Constants depend on $B,\varepsilon,r$. The old trace must be removed exactly once for every realization.

**Failure modes.** Dropping tangle-containing graphs without adding their probability, or applying side-stepping to the full rather than new trace, leaves the old dominant spectrum in the estimate.

**Interpretation.** Level zero is the expected old spectrum. After it is removed, the first possible mysterious coefficient is at level one, which is why the universal theorem has exceptional probability $O(n^{-1})$.

**Remember this.** Old-trace subtraction gives $j=1$. Side-stepping gives $O(n^{-1})$ on the tangle-free part. Finite tangle occurrence bounds supply the other $O(n^{-1})$ part. Ihara-Bass converts the result to adjacency eigenvalues.

## D11. The fundamental exponent and its finite computation

### Target

Explain why the least strict-tangle order is computable and test the printed universal lower bound against the definitions.

### Where it appears

Definition 2.4.8, Theorem 2.4.7, Propositions 3.3.1 and 3.3.3, and Theorem 3.3.4.

### Derived: finite search

An arbitrary strict tangle has a finite type. Section 3.3.1 restricts the search to finitely many types of order below the base order. If the base projection of a beaded path repeats a base vertex, delete the intervening segment. This preserves an étale map and produces shorter path lengths.

Shorter lengths can only increase the dominant spectral radius under the monotonicity convention used in D6, so strictness is preserved. Repeating until no projected path repeats a base vertex gives every required path length at most $|V_B|$. There are finitely many integer vectors satisfying these bounds and finitely many candidate $B$-morphisms to inspect.

For each candidate constructible graph, the Hashimoto entries are integers. Its dominant eigenvalue is algebraic, as is the comparison with the fixed algebraic threshold $R^{1/2}$. Bounds on algebraic degree and height give effective separation when the difference is nonzero, so approximation can decide strict positivity. This yields a finite algorithm, not a practical complexity estimate.

**Source caution.** The sentence claiming $\eta_{\mathrm{fund}}(B)\le\operatorname{ord}(B)-1$ is not justified merely by the identity map, which directly supplies only $\eta_{\mathrm{fund}}(B)\le\operatorname{ord}(B)$. This inequality should not be substituted into the algorithm without a separate argument.

### Derived: a counterexample to Theorem 3.3.4 as printed

Let $W_2$ be one vertex with two whole-loops. It is $4$-regular and $\operatorname{ord}(W_2)=2-1=1$. Its directed-line Hashimoto matrix has outdegree $3$, so $\rho(H_{W_2})=3$. The identity map is étale, and $W_2$ occurs in the model at degree $1$. It is therefore an eligible strict tangle because

$$
3>\sqrt3.
$$

By Definition 2.4.8, $\eta_{\mathrm{fund}}(W_2)=1$, since no eligible tangle has positive order less than one. But Theorem 3.3.4 as printed would require

$$
\eta_{\mathrm{fund}}(W_2)>\sqrt{d-1}=\sqrt3,
$$

which is false. The paper's own formula $\eta_{\mathrm{fund}}(W_{d/2})=m-1$ for the least $m$ with $2m-1>\sqrt{d-1}$ independently gives $m=2$ and $\eta_{\mathrm{fund}}=1$ at $d=4$.

**What this does and does not show.** It decisively rejects the printed universal inequality and warns against any later use of it as a general growth estimate. It does not refute the existence of a computable tangle exponent for a specified model, nor the general $O(n^{-1})$ theorem.

**Type check.** All graphs here have no half-loops, so $|E|-|V|$ and the directed-loop degree computation require no loop-convention repair.

**Remember this.** The finite algorithm is meaningful, but ancillary inequalities must be tested against small bouquets before being quoted.

## D12. Why spreading is a separate ingredient

### Target

Explain the role of spreading without reproducing all 11 pages of its proof.

### Where it appears

Section 3.2 and the proof of Theorem 3.3.2.

### Paper

A $d$-regular graph is a $\gamma$-spreader when every $A$ with $|A|\le|V|/2$ satisfies $|\Gamma(A)|\ge(1+\gamma)|A|$. Theorem 3.2.4 states

$$
\lambda_2(G)^2\le d^2-\frac{\gamma^2}{4+2\gamma^2}.
$$

Applying this to walk powers controls all non-dominant eigenvalues, with bipartite parity handled separately.

### Derived role in the fine exponent

For a Ramanujan base, all base Hashimoto eigenvalues except $d-1$ and possibly $1-d$ are already inside the critical disk. Side-stepping can exclude outliers away from those remaining bases, but the argument also needs to prevent concentrations near them from producing fake lower-order coefficients.

Spreading gives a polynomially small probability of adjacency eigenvalues near $\pm d$, which through D1 corresponds to Hashimoto eigenvalues near $\pm(d-1)$. Thus a nonzero coefficient at order $j<\eta_{\mathrm{fund}}$ would require a base-near concentration with a probability larger than the spreading and tangle bounds allow. Coefficients below the fundamental order vanish. The smallest strict tangle supplies the matching lower-order event through D3.

**Hidden assumptions.** Small connected components are handled separately as tangling events. In the bipartite case, eigenvalue $-d$ is expected and must be excluded together with $d$.

**Failure modes.** Replacing side-stepping with spreading alone would not address outliers away from dominant bases. Conversely, omitting spreading would leave the extreme base eigenvalues uncontrolled in the Ramanujan refinement.

**Remember this.** Certified traces control generic non-tree-like behavior, spreading controls near-disconnection, and tangle order controls the leading rare obstruction. These are three different tasks.
