# Central derivations

These notes reorganize and expand the supplied paper. **Paper** identifies source statements. **Derived** contains independent reconstruction and algebra. **Interpretation** is explanatory rather than a new theorem. No numerical checks were run. Proposals marked **numerically checkable** await user approval.

For this file only, set $q=d-1$. This is a derived convenience, not a new paper symbol. Page numbers refer to the supplied arXiv PDF.

## D1. Non-backtracking walk matrices and the regular-tree count

### Target

Derive the recurrence for $A_k=q_k(A)$ in Lemma 2.3 and determine the correct value of $q_k(d)$.

### Where it appears

Section 2.1, pages 10 to 12, Lemma 2.3, Equation 2, and Theorem 2.7.

### Inputs

**Paper.** $A_k(u,v)$ counts irreducible length-$k$ walks from $u$ to $v$. Whole-loops follow the permutation model's adjacency convention. The graph is $d$-regular without half-loops in this derivation.

### Derivation

Set $A_0=I$ and $A_1=A$. In length 2, every backtracking pair leaves a vertex and immediately returns. There are exactly $d$ such pairs starting at that vertex, hence

$$
A_2=A^2-dI.
$$

For $k\geq3$, append one edge to every irreducible walk of length $k-1$. The product $AA_{k-1}$ counts all such extensions, both irreducible and reducible. A reducible extension reverses the last edge of the shorter walk. Remove that last edge to obtain an irreducible walk of length $k-2$. Conversely, from each such length-$k-2$ walk there are exactly $q=d-1$ non-reversing edges that can follow the forced back-and-forth insertion. Thus

$$
AA_{k-1}=A_k+qA_{k-2},
$$

which gives

$$
A_k=AA_{k-1}-qA_{k-2}\quad(k\geq3).
$$

Since the right side is a polynomial in $A$, there is a degree-$k$ polynomial $q_k$ with $A_k=q_k(A)$. Taking traces gives

$$
\operatorname{IrredTr}(A,k)=\operatorname{Tr}(A_k)
=\sum_{i=1}^nq_k(\lambda_i).
$$

Now apply $A_k$ to the constant vector $\mathbf1$. In a $d$-regular graph, the first non-backtracking step has $d$ choices and each later step has $q$ choices. Therefore

$$
q_k(d)\mathbf1=A_k\mathbf1=dq^{k-1}\mathbf1,
$$

so the necessary identity is

$$
q_k(d)=dq^{k-1}=d(d-1)^{k-1}\quad(k\geq1).
$$

**Source correction.** Page 12 instead states $q_k(d)=(d-1)^k$. That printed identity fails already at $k=1$, since $q_1(d)=d$. Theorem 2.7's leading term $d(d-1)^{k-1}$ agrees with the recurrence and is the consistent value.

For completeness, the tree-bound input in Lemma 2.4 follows from the sphere sizes on the $d$-regular tree. If $S_i$ is the sphere of radius $i>0$ around $v$, then $|S_i|=dq^{i-1}$. By spectral norm and Cauchy-Schwarz,

$$
|S_i|N_{k,i}
=(A_T^k\delta_v,\delta_{S_i})
\leq(2\sqrt q)^k\sqrt{|S_i|}.
$$

Hence

$$
N_{k,i}\leq(2\sqrt q)^kq^{-i/2}\sqrt{q/d}.
$$

For $i=0$, $|S_0|=1$ gives $N_{k,0}\leq(2\sqrt q)^k$.

### Type check

$A_k$ is again an $n\times n$ symmetric nonnegative integer matrix. The recurrence subtracts matrices of the same size. Evaluation at $\lambda=d$ is scalar polynomial evaluation, not application to the adjacency matrix of the finite graph itself.

### Hidden assumptions

- Every edge choice is regular and unweighted.
- The recurrence counts labelled or multiple-edge walks with their proper multiplicities.
- Half-loops require adjustments and are handled separately later in the paper.
- The tree estimate uses the infinite tree's norm $\|A_T\|=2\sqrt q$, whose upper bound is proved on pages 11 and 12.

### Intuition

Immediate reversals are local insertions. Removing one backtracking pair changes $k$ to $k-2$ and leaves $q$ legal continuations, exactly the recurrence. On a regular graph, non-backtracking paths have branching $d,q,q,\ldots$, hence the factor $dq^{k-1}$.

### Failure modes

Using $A^k$ directly mixes backtracking lengths of different parity. Omitting $-dI$ at $k=2$ would incorrectly include immediate reversals. Treating $q_k(d)$ as $q^k$ loses the graph-dependent prefactor $d/q$.

### Numerically checkable

On a small cycle with edge multiplicity $d/2$, compare $(A^k)_{vv}$ reduced by backtracking with the recurrence values $q_k(\lambda)$. **Not run.**

### Remember this

The adjacency spectrum enters through the same recurrence as the non-backtracking path count. The correct trivial-eigenvalue contribution is $dq^{k-1}$.

## D2. A loop tangle produces a spectral defect

### Target

Reproduce Theorem 2.11's $\alpha(m)$ and explain the probability exponent $n^{1-m}$.

### Where it appears

Section 2.2, pages 14 to 18, especially Equations 7 to 9 and Theorems 2.10 and 2.11.

### Inputs

**Paper.** Fix $1\leq m\leq d/2$ and condition on $\pi_i(v_0)=v_0$ for $i=1,\ldots,m$. Set $x=2m-1$ and

$$
\alpha(m)=x+\frac qx.
$$

The completion is one vertex with $m$ whole-loops, extended by trees to degree $d$.

### Derivation

Define a radial function on the first $r$ levels by $f(v)=x^{-\rho(v)}$, where $\rho$ is distance to $v_0$, and set $f=0$ farther out.

At a noncentral, nonboundary vertex, the parent contributes $xf(v)$ and its $q$ tree children together contribute $qf(v)/x$. Thus

$$
(Af)(v)\geq\left(x+\frac qx\right)f(v)=\alpha(m)f(v).
$$

At the center the term looks different but gives the same bound. The loops contribute $2m f(v_0)$, while at most $d-2m$ outward neighbors contribute $d-2m$ times $f(v_0)/x$. Since $x=2m-1$,

$$
2m+\frac{d-2m}x
=x+\frac{d-1}x
=\alpha(m).
$$

The drawing convention matters: each whole-loop contributes 2 to adjacency, and $x=2m-1$ is the residual non-backtracking growth through the center after entering from a branch.

Away from the final truncation boundary, $Af\geq\alpha f$. Only the edges leaving radius $r-1$ cause a missing term. Consequently,

$$
\frac{(Af,f)}{(f,f)}
\geq\alpha\frac{(f,f)_{r-1}}{(f,f)_r}.
$$

The last sphere has at most $(d-2m)q^{r-1}$ vertices. Therefore

$$
\frac{(f,f)_r-(f,f)_{r-1}}{(f,f)_{r-1}}
\leq C\frac{q^{r-1}x^{-2r}}{1}
=C' \left(\frac q{x^2}\right)^r.
$$

If $x>\sqrt q$, this tends to zero. Given any $\alpha'<\alpha$, choose $r$ sufficiently large to obtain $R_A(f)>\alpha'$.

The support of $f$ and its one-step neighborhood is bounded independently of $n$. Choose $g$ as the indicator of the complement of that neighborhood. Then $g$ is orthogonal to both $f$ and $Af$, and counting edges gives

$$
R_A(g)\geq d-O(1/n).
$$

On the two-dimensional span of $f,g$, every nonzero vector has Rayleigh quotient at least $\min(\alpha',d-O(1/n))$. Lemma 2.9 therefore yields $\lambda_2>\alpha'$ eventually. Since

$$
x+\frac qx-2\sqrt q=\frac{(x-\sqrt q)^2}x,
$$

strict hypercriticality $x>\sqrt q$ implies $\alpha>2\sqrt q$. Choosing $\alpha'$ between these numbers gives the strict conclusion.

At one specified vertex, the $m$ prescribed fixed points have probability $n^{-m}$ up to the exact uniform convention used in the paper. There are $n$ possible vertices. Inclusion-exclusion gives at least

$$
n\cdot n^{-m}-\frac12n^2n^{-2m}
=n^{1-m}-\frac12n^{2-2m}.
$$

The minimal hypercritical $m$ gives the lower failure exponent $s=m-1$ used in Theorem 1.1.

### Type check

The test functions belong to $\mathbb R^n$ after transfer to the finite graph. Their supports are bounded. $\alpha$ is an adjacency-scale growth rate, while $x=\lambda_{\mathrm{Irred}}$ is a non-backtracking-scale growth rate.

### Hidden assumptions

- $m$ is fixed and feasible for the model.
- The hypercritical inequality is strict. At $x=\sqrt q$, $\alpha=2\sqrt q$ and this argument gives no strict failure.
- The graph is large enough that the distant complement test has Rayleigh quotient above the chosen $\alpha'$.
- The local occurrence calculation counts overlapping vertices with inclusion-exclusion rather than independence.

### Intuition

The loops provide extra return routes at the center. An exponentially decaying radial test concentrates near this defect. The tree completion determines the exact local adjacency action, and the rest of the graph supplies a second large test space.

### Failure modes

At criticality the strict spectral conclusion disappears. If $q/x^2\geq1$, the outer spheres overwhelm the inner norm and the truncation argument no longer works. A finite graph also need not contain the infinite completion, only the finite tangle.

### Numerically checkable

Verify $x+q/x-2\sqrt q=(x-\sqrt q)^2/x$ and evaluate the center Rayleigh contribution for small $d,m$. **Not run.**

### Remember this

Hypercritical non-backtracking growth produces a strict tree-completion excess, and a fixed tangle at $n$ possible locations gives probability order $n^{1-m}$.

## D3. The $\operatorname{Tree}_d(\psi)$ threshold via generating functions

### Target

Fill in the algebra linking $\lambda_1(\operatorname{Tree}_d(\psi))$ and $\lambda_{\mathrm{Irred}}(\psi)$ in Theorem 3.13.

### Where it appears

Section 3.8, pages 31 to 33, Theorem 3.13 and Equation 13. Figure 1 illustrates the graph completion.

### Inputs

**Paper.** The first-return series for the rooted tree with $q$ children at each nonroot vertex is

$$
S=S_d(z)=\frac{1-\sqrt{1-4qz^2}}2.
$$

Realizing $\operatorname{Tree}_d(\psi)$ on $V_\psi$ yields

$$
Z_G(z)=zA+\frac{dI-D}{q}S(z).
$$

Ihara-Bass is cited as an external identity relating $\lambda_{\mathrm{Irred}}(\psi)$ to the smallest positive singular value of $I-yA+y^2(D-I)$.

### Derivation

A first return from the root chooses a child, performs a sequence of first-return walks below that child, and returns. The series for one child therefore satisfies

$$
S=qz^2(1+S+S^2+\cdots)=\frac{qz^2}{1-S}.
$$

Thus

$$
S(1-S)=qz^2.
$$

Choosing the root with $S(0)=0$ gives the displayed radical.

Set

$$
y=y(z)=\frac z{1-S(z)}.
$$

Then $z=y(1-S)$ and $z^2/(1-S)=S/q$. Using $D-I=-(dI-D)+qI$,

$$
\begin{aligned}
(1-S)&\left(I-yA+y^2(D-I)\right)\\
&=(1-S)I-zA+\frac{z^2}{1-S}(D-I)\\
&=(1-S)I-zA+\frac Sq\left(-(dI-D)+qI\right)\\
&=I-zA-\frac Sq(dI-D)\\
&=I-Z_G(z).
\end{aligned}
$$

Hence a singular Ihara-Bass matrix corresponds exactly to $Z_G(z)$ acquiring eigenvalue 1.

At the regular-tree threshold $z_0=1/(2\sqrt q)$,

$$
4qz_0^2=1,
\qquad S(z_0)=\frac12,
\qquad y(z_0)=\frac{z_0}{1/2}=\frac1{\sqrt q}.
$$

Moreover $S(z)\leq1/2$ on $0<z\leq z_0$, and the relevant composition is increasing before its singularity. Therefore the first crossing below $z_0$ detects precisely whether non-backtracking growth exceeds $\sqrt q$ or adjacency growth exceeds $2\sqrt q$.

Writing $z_1=1/\lambda_1(\operatorname{Tree}_d(\psi))$ and $y_1=1/\lambda_{\mathrm{Irred}}(\psi)$ in the supercritical regime gives

$$
y_1=\frac{z_1}{1-S(z_1)}.
$$

Both singularities occur before or at the threshold together. The two implications in Theorem 3.13 follow from Theorem 3.5's identification of Perron growth with the first eigenvalue-1 crossing of $Z_G$.

### Type check

$A,D,I$ act on $V_\psi$. $Z_G(z)$ has the same dimensions, with formal series entries. $S$ and $z$ are scalars. $y$ has units of inverse non-backtracking growth while $z$ has units of inverse adjacency growth.

### Hidden assumptions

- The graph is strongly connected enough for the Perron theorem, supplied by connectedness of $\psi$ and its completion.
- Ihara-Bass is used as a cited input, not rederived.
- For real nonintegral $d$, the meaning of the completion is the formal analytic continuation specified in Section 3.8, not literal graph degrees.
- The branch of the square root is selected by analyticity near $z=0$.

### Intuition

The completion compresses every infinite tree attached to a degree-$r$ vertex into one formal return series $(d-r)S/q$. The remaining finite matrix is exactly the non-backtracking determinant after a change of spectral variable.

### Failure modes

The determinant criterion alone is insufficient on arbitrary infinite graphs, as the counterexamples in Section 3.4 show. The theorem uses finite $\psi$ plus controlled tree attachments. Choosing the wrong quadratic root would destroy convergence at zero.

### Numerically checkable

Substitute several small positive $z$ values into both sides of the factorization identity for a random diagonal $D$ and symmetric $A$. **Not run.**

### Remember this

$S(1-S)=qz^2$ turns the infinite tree into a finite generating matrix, and $y=z/(1-S)$ matches non-backtracking and adjacency thresholds exactly.

## D4. Factorial walk expansions and the meaning of order

### Target

Derive the leading power in $\mathbb E[\Gamma]_n$ and explain the error scale in Theorem 5.9.

### Where it appears

Section 5.1, pages 43 to 49, especially Equations 16 through 21 and Theorems 5.5 and 5.9.

### Inputs

**Paper.** A form has $v$ distinct vertices and determines $a_j$ values of $\pi_j$, with $e=\sum_ja_j$. For $r$ fixed, $k\leq n/2$.

### Derivation

Sum a potential-walk probability over all $n(n-1)\cdots(n-v+1)$ vertex specializations:

$$
E_{\mathrm{symm}}(w,\vec t)_n
=n(n-1)\cdots(n-v+1)
\prod_{j=1}^{d/2}\frac1{n(n-1)\cdots(n-a_j+1)}.
$$

This is also $\mathbb E[\Gamma]_n$. Factor the leading powers:

$$
n(n-1)\cdots(n-v+1)
=n^v\prod_{\ell=0}^{v-1}(1-\ell/n),
$$

and

$$
\frac1{n(n-1)\cdots(n-a_j+1)}
=n^{-a_j}\prod_{\ell=0}^{a_j-1}(1-\ell/n)^{-1}.
$$

Therefore

$$
\mathbb E[\Gamma]_n
=n^{v-e}g(1/n),
$$

where $g$ is a finite product of polynomials and inverse polynomials. Its Taylor coefficients are universal polynomials in $a_1,\ldots,a_{d/2},v$. In particular,

$$
v-e=-\operatorname{ord}(\Gamma),
$$

so the leading scale is $n^{-\operatorname{ord}(\Gamma)}$.

For a form of order at least $r$, the sequential random-walk construction has at least $r+1$ coincidences. Mark their positions. Each marked coincidence chooses among at most $k$ old vertices, with probability at most $k/(n-k)$ after accounting for previously determined permutation values. The starting vertex has $n$ choices. This gives the paper's bound

$$
\sum_{\vec t:\operatorname{ord}(w,\vec t)\geq r}P(w,\vec t)
\leq n\binom{k}{r+1}\left(\frac{k}{n-k}\right)^{r+1}
=O(k^{2r+2}n^{-r})
$$

per fixed word.

On the other side, an irreducible word of order at most $r-1$ has at most $O(k^{2r})$ equivalence classes, by marking its coincidences. Truncating each factorial expansion contributes a further polynomial factor. There are $dq^{k-1}=O(q^k)$ irreducible words of length $k$ in the permutation alphabet. Combining those terms yields the generic bound

$$
|\operatorname{error}|\leq ck^{4r}q^k
$$

at level $n^{-r}$, as in Theorem 5.9.

### Type check

$\mathbb E[\Gamma]_n$ counts expected labelled specializations, not a probability of at least one inclusion. $v,e$ are counting parameters. The coefficient $f_i(k)$ is a function of walk length, while $n$ only enters through the displayed expansion and error.

### Hidden assumptions

- Vertex-relabelling symmetry holds.
- Fixed $k$ requirements permit Taylor expansion with bounded factorial parameters.
- High-order classes are dominated uniformly in the model.
- The collection is SSIIC so finite classes and expansions fit together.

### Intuition

A new vertex supplies a factor $n$, while each determined labelled edge costs approximately $1/n$. Order measures edge constraints minus vertex freedom.

### Failure modes

Expected inclusion counts do not directly give occurrence probabilities because automorphisms and overlaps matter. Letting $k$ grow without tracking $k/n$ can destroy the Taylor error. The expansion does not by itself control $f_i(k)$ as $k$ grows.

### Numerically checkable

Expand small products for fixed $v,a_j$ symbolically and compare the first two coefficients with direct factorial evaluation. **Not run.**

### Remember this

Order is the exponent in $1/n$. Coincidence position counting supplies polynomial-in-$k$ losses, not additional exponential bases beyond $q^k$.

## D5. Figure 2, compression, and order preservation

### Target

Reconstruct the form and type in Figure 2 and show exactly what data survive suppression.

### Where it appears

Page 31 for the general tree diagram, page 41 for Figure 2, and Definitions 5.13 to 5.19 on pages 52 to 55.

### Inputs

**Paper.** The displayed pair $(w,\vec t)$ in Section 5. The general suppression operation from Section 3.2.

### Derivation

The sequence visits

$$
5\to2\to4\to3\to7\to4\to3\to7\to4\to2\to5.
$$

Although the triangle occurs twice, the distinct undirected graph edges are only

$$
\{5,2\},\{2,4\},\{4,3\},\{3,7\},\{7,4\}.
$$

There are five distinct vertices and five distinct edges, hence

$$
\operatorname{ord}(\Gamma)=5-5=0.
$$

Vertices $2,3,7$ are beads. Suppression gives one type edge $5\leftrightarrow4$ with forward label $\pi_2^{-1}\pi_1$ and length 2, plus one type loop at $4$ with label $\pi_3\pi_1^{-1}\pi_3$ and length 3. The first edge is used in both directions during the full walk. The second is traversed twice before the return path.

The type has two vertices and two undirected edges, so its order is again $2-2=0$. Compression therefore preserves order and turns repeated traversal into multiplicity data $m_i$, rather than new edges.

The abstract first-visit names would be $5=v_1$, $2=v_2$, $4=v_3$, $3=v_4$, $7=v_5$. The figure's `4 (or v2)` instead makes sense if it means the second surviving type vertex. This explains the ambiguity without changing any walk data.

There is one additional closure check. The word starts with $\sigma_1=\pi_2^{-1}$ and ends with $\sigma_{10}=\pi_2=\sigma_1^{-1}$. Across the closure, the last step reverses the first. Thus this example is closed and irreducible but **not strongly irreducible** under Definition 10.1. It belongs to the earlier irreducible trace framework, not automatically to $\operatorname{SIT}$.

### Type check

Form order and type order use the same $E-V$ convention. Edge labels are words in $\Pi^+$ after compression, while the original form has single-letter labels in $\Pi$. Traversal multiplicity is not a VLG edge length.

### Hidden assumptions

- The starting vertex is preserved even if it is a bead.
- Numberings remember first visits, so a form has no nontrivial numbered automorphisms.
- Suppression must respect non-backtracking and loop conventions.
- A type alone does not encode repeated labels. Lettering and new-type data are added later.

### Intuition

Compress a walk by removing places where it has no meaningful choice. Keep the branch structure, edge lengths, and enough endpoint letters to reconstruct enumeration and non-backtracking transitions.

### Failure modes

Counting the triangle twice as six distinct edges would spoil factorial order. Reading the right-hand triangle as three independent type edges would also be wrong. Assuming Figure 2 already displays new-type fixed versus long decorations would anachronistically add information.

### Numerically checkable

No numerical check is needed. The entire example is a finite symbolic walk verification.

### Remember this

Forms record occurrence structure, types compress beads, and new types add the length information needed by selectivity. Figure 2 also cleanly illustrates the extra cyclic condition in strong irreducibility.

## D6. Why selective walk counts stay below $\sqrt q$

### Target

Explain the generating function proof of Theorem 6.6 and derive its exponential base.

### Where it appears

Section 6.2, pages 61 to 64, Theorem 6.6.

### Inputs

**Paper.** $B>S$ is sufficiently large. $\Psi$ contains all supercritical tangles occurring in the type. $M_1$ counts traversals of long type edges and $M_2$ counts traversals of fixed edges.

### Derivation

Start with a fixed new type $\widetilde T$. Replace each long edge by length $B$ for a worst-case VLG $G$, and retain the specified fixed lengths. Let $f(z)$ count selective irreducible walks by their total VLG length.

Every subwalk using only fixed edges and no long prohibited segment lies in a fixed-edge subgraph $H$ with

$$
\lambda_{\mathrm{Irred}}(H)<\sqrt q.
$$

Among such subgraphs, the paper extracts a finite set of extreme VLG majorants. Finiteness follows by passing to edge-length subsequences that are eventually constant or diverge. Diverging edges disappear in the limit, and remaining finite structures cannot produce infinitely many pairwise extreme objects.

For each extreme $H_i$, let $h_i(z)$ be its irreducible-walk series. Perron growth gives radius strictly greater than $q^{-1/2}$. The cumulative series $\widetilde h_i=h_i/(1-z)$ has the same radius at this scale. Choose $z_0>q^{-1/2}$ where all these finite series converge. Their tails beyond $S_0$ can be made arbitrarily small by increasing $S_0$.

Let $\widehat f$ count selective fixed-edge subwalks. Decomposing such a walk into a sequence of first passages beyond length $S_0$ and a final shorter remainder gives a majorant of the form

$$
\widehat f(z)\prec
\left(1-d\widetilde h^{S_0}(z)\right)^{-1}h(z).
$$

Choose $S_0$ so the denominator is positive at $z_0$.

Now insert long edges between fixed-edge subwalks. Each has length at least $S_0+1$ and at most $d$ choices at its insertion. Alternating decomposition gives

$$
f(z)\prec
\left(1-\widehat f(z)dz^{S_0+1}\right)^{-1}\widehat f(z).
$$

Increasing $S_0$ makes $\widehat f(z_0)dz_0^{S_0+1}<1$. Hence there is a common majorant $g$, depending only on the original type, with $g(z_0)<\infty$.

For a coefficient at length $L$,

$$
[z^L]f\leq g(z_0)z_0^{-L}.
$$

Each long-edge traversal costs length at least $B$, and each fixed-edge traversal costs at least 1. Aggregating by $M_1,M_2$ therefore gives, after constants,

$$
W_{\widetilde T,S}(M_1,M_2)
\leq Cz_0^{-BM_1-M_2}.
$$

Set $\beta=z_0^{-1}$. Since $z_0>q^{-1/2}$, $\beta<\sqrt q$, so choose $\eta=\sqrt q-\beta>0$. Then

$$
W_{\widetilde T,S}(M_1,M_2)
\leq C(\sqrt q-\eta)^{BM_1+M_2},
$$

which is the claimed exponential form, up to the paper's more explicit $(S_0+1)M_1$ intermediate exponent.

### Type check

$z$ tracks total length, whereas $M_1,M_2$ track traversal counts. Convergence at one fixed real $z_0$ yields exponential coefficient control for every length, uniformly over the finite extreme family.

### Hidden assumptions

- Every possible low-growth fixed subgraph is covered by the finite extreme family.
- Selectivity includes enough supercritical tangles to enforce $\lambda_{\mathrm{Irred}}(H)<\sqrt q$.
- $S_0$ can be chosen after fixing the type and family, and $B>S_0$.
- Constants may depend on the type, $B,S,d$, but not on $M_1,M_2$ or the walk length.

### Intuition

Below threshold, fixed regions have convergent walk series slightly beyond $q^{-1/2}$. Long edges and long forbidden segments occur so sparsely in weighted length that their geometric insertion series also converges. Convergence immediately becomes an exponential walk bound.

### Failure modes

Without selectivity, a fixed subgraph with $\lambda_{\mathrm{Irred}}\geq\sqrt q$ can destroy convergence at $z_0>q^{-1/2}$. If $S_0$ is too small, insertion denominators can hit zero. Treating infinitely many extreme subgraphs without a finite uniform majorant would block the argument.

### Numerically checkable

For one small explicit type and several candidate $z_0,S_0$, evaluate the finite rational truncations and denominators. This would test the mechanism only on that type, not prove the theorem. **Not run.**

### Remember this

Selectivity converts a spectral growth gap into generating function convergence at $z_0>q^{-1/2}$. That single convergence statement supplies the entire base $\sqrt q-\eta$.

## D7. From the selective gap to d-Ramanujan coefficients

### Target

Show why Theorem 6.6 makes the infinite new-type sums in Theorem 8.2 converge with d-Ramanujan bounds.

### Where it appears

Sections 5.4 and 8, especially Theorems 8.2, 8.3, 8.5 and Lemmas 8.6 and 8.8, pages 56 to 80.

### Inputs

**Paper.** A d-Ramanujan function satisfies

$$
f(k)=q^kp(k)+e(k),
\qquad |e(k)|\leq ck^cq^{k/2}.
$$

Theorem 8.5 estimates edge-length sums. Theorem 6.6 estimates selective walk multiplicities.

### Derivation

First reduce the compatible-word sums. Lemma 5.10 sums a polynomial in letter counts over irreducible length-$k_i$ words and obtains terms of the form

$$
q^{k_i}Q_1(k_i),\qquad(-1)^{k_i}Q_2(k_i),\qquad Q_3(k_i).
$$

Products over type edges reduce to exponential-polynomial expressions of the kind in Equations 33 and 34. The only exponentially large base is $q$, while other terms are harmless polynomially or with bounded base.

Fix multiplicities $\vec m$ and define $f_{\vec m}(k)$ by summing these expressions over edge lengths with $\vec k\cdot\vec m=k$. On a selected set of long edges, $m_i=1$ for $i\leq s$ and $m_i\geq2$ thereafter. Their lengths contribute a convolution with a polynomial $Q$, obtained from sums of products of powers by Lemma 8.7.

The remaining lengths define $g_{\vec m}(r)$. A repeated long edge loses the amount of $q$-exponential weight that would otherwise be available. Concretely, the proof uses $k_i\geq B$ on long edges and $k_i\geq1$ on fixed edges to obtain

$$
2\sum_{i=s+1}^u k_i
\leq r-BM_1-M_2+O(B).
$$

Thus, after absorbing constants depending on the new type,

$$
|g_{\vec m}(r)|
\leq Cr^c q^{(r-BM_1-M_2+O(1))/2}.
$$

Normalize $\widetilde g(r)=q^{-r}g_{\vec m}(r)$. Then

$$
|\widetilde g(r)|\leq Cr^c\rho^r
\quad\text{with}\quad
\rho=q^{-1/2}<1.
$$

Lemma 8.8 expands $Q(k-r)$ into finitely many moments. For fixed degree $D$, geometric moment series give a polynomial $h(k)$, and tails starting beyond $u$ carry a factor $u^{2D}\rho^u$ times constants. This converts the convolution into

$$
f_{\vec m}(k)=q^kp_{\vec m}(k)+e_{\vec m}(k),
$$

where, after the constants are absorbed,

$$
|p_{\vec m}|\leq Cq^{(-BM_1-M_2+c)/2},
$$

$$
|e_{\vec m}(k)|\leq Ck^cq^{(k-BM_1-M_2+Bc)/2}.
$$

Now write $L=BM_1+M_2$ and sum against selective walk counts. By Theorem 6.6, the principal coefficient factors are bounded, up to fixed constants, by

$$
q^{(-L+c)/2}(\sqrt q-\eta)^L
=Cq^{c/2}\left(1-\frac\eta{\sqrt q}\right)^L.
$$

The ratio is strictly below 1. The same comparison applies to the error after factoring out $q^{k/2}$:

$$
k^cq^{(k-L+Bc)/2}(\sqrt q-\eta)^L
=Ck^cq^{(k+Bc)/2}\left(1-\frac\eta{\sqrt q}\right)^L.
$$

The right side is summable over $M_1,M_2$, with a geometric loss that depends only on $B,S,\eta,q$. The polynomial degrees are uniformly bounded, so the principal parts can also be summed in coefficient norm. The result is d-Ramanujan.

Finally, finitely many types occur below a fixed order, and each has finitely many $B$-new types. Their sums give all $f_i$ in Theorem 8.1.

### Type check

The principal coefficient estimate uses the coefficient norm $|p|$, not pointwise evaluation at arbitrary real $k$. Since degree is bounded, an estimate in this norm also gives polynomial-in-$k$ evaluation bounds. The left side $f(k)$ is a scalar indexed by total length $k$.

### Hidden assumptions

- $B$ and $S$ are large enough for every type below the required finite order.
- Polynomial degrees and the function $\beta$ in Theorem 8.3 have fixed bounds.
- The geometric ratio is uniform after type-dependent constants are absorbed.
- Finitely many new types arise only after the order cutoff.

### Intuition

Long or repeated edges can have large individual sums, but selectivity makes their walk multiplicities smaller by slightly more than the inverse square-root growth of those sums. The product is geometric and can be summed without identifying any individual coefficient.

### Failure modes

Replacing $\sqrt q-\eta$ by $\sqrt q$ destroys the strict geometric ratio. Letting polynomial degrees grow with $M_1,M_2$ could overwhelm geometric gain. Omitting high-order forms in a way that loses control of their walk collection would invalidate the assembly.

### Numerically checkable

For a fixed set of values $L,C,\eta,q$, compute the ratio and partial sums of $(\sqrt q-\eta)^Lq^{-L/2}$ over a grid. This tests only geometric summability. **Not run.**

### Remember this

The theorem does not calculate unknown coefficients. It proves a strict geometric comparison after factoring out $q^k$ for principal parts and $q^{k/2}$ for errors.

## D8. Conditional tangle expansions and Möbius inversion

### Target

Explain why Section 9 can replace selective traces on tangle-free graphs by ordinary traces while retaining d-Ramanujan expansions.

### Where it appears

Section 9, pages 81 to 89, Lemma 9.2, Proposition 9.5, Theorem 9.3, and Corollary 9.4.

### Inputs

**Paper.** $\Psi$ is a finite set of pruned nonempty tangles of order at least 1. $\Psi'$ contains all supercritical tangles below expansion order $r$. $\chi_\Psi$ indicates at least one $\Psi$-tangle occurrence.

### Derivation

First establish finiteness of minimal supercritical tangles. If infinitely many minimal examples existed, infinitely many would share one compressed type by Theorem 5.20. Along a subsequence, each type-edge length is constant or tends to infinity. Delete the diverging edges to define $\psi_\infty$.

By Theorem 3.6,

$$
\lambda_{\mathrm{Irred}}(\psi_i)
\to\lambda_{\mathrm{Irred}}(\psi_\infty)
\geq\sqrt q.
$$

Deleting at least one edge lowers order. Therefore $\psi_\infty$ still belongs to the relevant bounded-order supercritical class and is contained in the large $\psi_i$, contradicting minimality. This proves $\Psi_{\min}[r]$ finite. The printed proof says that $\psi_\infty$ properly contains $\psi_i$, but the construction requires the reverse containment. The adjacent example's occurrence logic is consistent with $\psi_\infty\subset\psi_i$: containing the larger $\psi_i$ forces an occurrence of the smaller $\psi_\infty$.

Now convert the indicator to counts. Let $\Psi^+$ contain representatives of nonempty unions of $\Psi$-tangles. Generalized Möbius inversion finds real $\mu_\Omega$ satisfying

$$
\sum_{\Omega\leq\Omega'}N(\Omega,\Omega')\mu_\Omega=1
$$

for each derived $\Omega'$. The diagonal term $N(\Omega,\Omega)$ is the positive automorphism count, so lower-order $\mu$ can be solved inductively. Substituting into inclusion counts gives a signed expansion whose truncation can represent $\chi_\Psi$ up to controlled high-order derived tangles.

Why is truncation finite? A derived tangle of high order contains one of order in a bounded interval formed by successive $\Psi$ unions. Since every $\Psi$-tangle has order at least 1, low-order derived tangles involve only finitely many unions. Theorem 4.7 bounds discarded high-order occurrences by $O(n^{-r})$. The Möbius weights are fixed after truncation, so their absolute values can be placed in the constant.

For one retained $\Omega$, enrich a walk form by $\Gamma\cup\Omega$. Its factorial expansion has the same form as D4:

$$
\mathbb E[\Gamma,\Omega]_n
=\frac{n!}{(n-v)!}\prod_j\frac{(n-a_j)!}{n!},
$$

where $v=|V_{\Gamma\cup\Omega}|$ and $a_j$ counts labels in the union. Adding fixed $\Omega$ increases bounds on $v$ and $e$ only by constants. Consequently the generic error remains polynomial in $k$ times $q^k$, with polynomial degree shifted by $|V_\Omega|$.

The corresponding $\Omega$-type fixes every $\Omega$ edge at length 1 with its given label. Long and fixed walk counts obey the same type of selective bound as Theorem 6.6, with extra type-dependent constants. Theorem 8.2 therefore applies after a polynomial change of variables

$$
a_j(\Gamma,\Omega)=a_j(\Gamma)+a_j(\Omega\setminus\Gamma),
$$

because the second term is fixed in each new $\Omega$-type. This produces d-Ramanujan coefficients for $\mathbb E[\chi_\Psi\operatorname{IrSelTr}]$.

Corollary 9.4 is subtraction: Theorem 8.1 supplies the expansion on all graphs, Theorem 9.3 supplies the $\chi_\Psi$ term, and

$$
\mathbb E[(1-\chi_\Psi)\operatorname{IrSelTr}]
=\mathbb E[\operatorname{IrSelTr}]
-\mathbb E[\chi_\Psi\operatorname{IrSelTr}].
$$

Finally, if $\Psi'$ contains every supercritical tangle below $r$ and $\chi_\Psi=0$ for the corresponding minimal set, no such tangle occurs at all. Any forbidden selective segment would contain one. Hence selective and ordinary irreducible traces coincide on this event. The same reasoning applies to strong traces.

### Type check

$\chi_\Psi$ is an indicator, whereas $N(\Omega,G)$ is an integer inclusion count and $\mu_\Omega$ is a signed real coefficient. Products with trace counts remain random scalar variables. The $\Omega$-type uses union data rather than assuming walk and tangle are disjoint.

### Hidden assumptions

- Every $\Psi$-tangle has order at least 1. Order-0 cycles permit infinitely many disjoint unions at fixed order and break the stated truncation argument.
- Limit continuity of $\lambda_{\mathrm{Irred}}$ under diverging edge lengths is available.
- High-order tangle occurrence is bounded independently of the trace except for $q^k$ and polynomial factors.
- Finitely many low-order $\Omega$-types suffice after all truncations.

### Intuition

The proof never needs to understand precisely which walks selectivity deletes from a tangled graph. It expands both complementary strata and works on the high-probability one where deletion has no effect.

### Failure modes

Using expected inclusion counts directly in place of $\chi_\Psi$ ignores multiple occurrences and automorphisms. Reversing the inclusion in the finiteness proof would reverse the contradiction. Including cycles without modifying truncation destroys finiteness at order 0.

### Numerically checkable

For a small poset of two or three explicit tangles, solve the Möbius equations by substitution and compare the indicator with signed inclusion counts. **Not run.**

### Remember this

Finiteness controls which tangles must be named, Möbius inversion converts occurrence events to counts, and subtraction isolates graphs where selectivity changes nothing.

## D9. Strongly irreducible traces as pure power sums

### Target

Derive the recurrence leading to Theorem 10.3's roots $\mu_{1,2}(\lambda)$ and explain why nonreal roots have modulus $\sqrt q$.

### Where it appears

Section 10, pages 89 to 94, Theorem 10.3 and Lemma 10.4.

### Inputs

**Paper.** $\operatorname{SIT}$ counts closed irreducible walks with no reversal across the closure. For graphs without half-loops,

$$
\operatorname{SIT}(G,k)=\sum_i\mu_i^k
$$

where $\mu_i$ are eigenvalues of $G_{\mathrm{Irred}}$, with the appropriate indexing and $k\geq2$ convention.

### Derivation

Every irreducible closed walk can be decomposed uniquely as an outward path $p$, a strongly irreducible closed core at another vertex $w$, and the reverse of $p$. If the outward path has length $i\geq1$, there are $(d-2)q^{i-1}$ choices compatible with the core. This yields

$$
\operatorname{IrredTr}(G,k)
=\operatorname{SIT}(G,k)
+(d-2)\sum_{i=1}^{\lfloor(k-1)/2\rfloor}q^{i-1}\operatorname{SIT}(G,k-2i),
$$

apart from the explicitly computed half-loop correction. Subtracting $q$ times the length $k-2$ formula gives

$$
\operatorname{IrredTr}(G,k)-q\operatorname{IrredTr}(G,k-2)
=\operatorname{SIT}(G,k)-\operatorname{SIT}(G,k-2).
$$

Define the shift $\sigma f(k)=f(k+1)$ and, for fixed $\lambda$, the recurrence operators

$$
L_\lambda=\sigma^2-\lambda\sigma+q,
\qquad R=\sigma^2-q,
\qquad U=\sigma^2-1.
$$

D1 says that $q_k(\lambda)$ is annihilated by $L_\lambda$ for the relevant range. Lemma 10.4 says, spectrally, that $R$ applied to the irreducible sequence equals $U$ applied to the strong sequence and its corrections. The strong recurrence coefficients are independent of $\lambda$, so applying $L_\lambda$ and using commutativity gives

$$
U L_\lambda\,\widetilde q_k(\lambda)=0.
$$

The roots of $L_\lambda$ satisfy

$$
\mu^2-\lambda\mu+q=0,
\qquad
\mu_{1,2}(\lambda)=\frac{\lambda\pm\sqrt{\lambda^2-4q}}2,
$$

and $U$ contributes $1,-1$. Consequently the eventual trace polynomial has shape

$$
\widetilde q_k(\lambda)
=c_1\mu_1^k+c_2\mu_2^k+c_3+c_4(-1)^k.
$$

Initial conditions or the paper's analytic-continuation argument identify $c_1=c_2=1$ and $c_3=c_4=(d-2)/2$. Special root coincidences follow by polynomial continuity. Thus

$$
\operatorname{SIT}(G,k)
=\sum_i\left(\mu_1(\lambda_i)^k+\mu_2(\lambda_i)^k
+(1+(-1)^k)\frac{d-2}2\right).
$$

For nonreal roots, $\lambda^2-4q<0$. The roots are conjugate and their product is $q$, hence

$$
|\mu_1|=|\mu_2|=\sqrt{\mu_1\mu_2}=\sqrt q.
$$

For real $\lambda>2\sqrt q$, the larger root exceeds $\sqrt q$, and similarly for negative $\lambda<-2\sqrt q$ in absolute value.

### Type check

$G_{\mathrm{Irred}}$ has directed edges as vertices. For a $d$-regular graph without half-loops it has $nd$ vertices. Two $\mu$ roots and $(d-2)/2$ copies of each $\pm1$ per adjacency eigenvalue account for $2+(d-2)=d$ values per vertex, hence $nd$ in total.

### Hidden assumptions

- Initial recurrences have parity and small-$k$ exceptions, especially with half-loops.
- Root collisions and polynomial determinacy are handled by continuity.
- Nonreal pairs can have negative even-power sums, but their modulus remains exactly $\sqrt q$.
- Half-loops need the correction $\widehat q_k=\widetilde q_k-\lambda$ for odd $k\geq3$ in the paper's special case.

### Intuition

Strong irreducibility removes outward and inward decorations around a closed core. The remaining adjacency recurrence has two oscillatory or growing roots, with bookkeeping roots $\pm1$ from the edge graph.

### Failure modes

Ordinary irreducible traces are not pure power sums directly, which makes finite differences awkward. Ignoring the roots $\pm1$ or the half-loop adjustments gives incorrect multiplicities.

### Numerically checkable

For a cycle or complete graph, enumerate non-backtracking eigenvalues symbolically and compare the total $nd$ with the root multiplicities. **Not run.**

### Remember this

After strong reduction, every adjacency eigenvalue contributes two solutions of $\mu^2-\lambda\mu+q=0$ and fixed $\pm1$ terms. This is the input required by the sidestepping lemma.

## D10. The sidestepping lemma without knowing the coefficients

### Target

Unpack how finite differences, three spectral bands, and polynomial recovery prove Lemma 11.1.

### Where it appears

Section 11, pages 94 to 99, Lemma 11.1 and Sublemma 11.2.

### Inputs

**Paper.** $|1-\theta_i|\leq1$, with $\theta_i$ real whenever $|1-\theta_i|>q^{-1/2}$, and

$$
\mathbb E\sum_i(1-\theta_i)^k
=\sum_{j=0}^{r-1}p_j(k)n^{-j}
+O(k^{\widetilde r}n^{-r}+k^cq^{-k/2}).
$$

There are $Dn$ variables.

### Derivation

Let $s$ be even and larger than every polynomial degree. Applying $(\sigma-1)^s$ annihilates every $p_j(k)$ and gives

$$
\mathbb E\sum_i\theta_i^s(1-\theta_i)^k
=O(k^{\widetilde r}n^{-r}+k^cq^{-k/2}),
$$

since signs $(-1)^s$ are irrelevant. For $\log^2n\leq k\leq n^{r/(2\widetilde r)}$, the right side is $O(n^{-r/2})$ up to constants.

Compare this weighted expectation at $k_1=\lfloor\log^2n\rfloor$ and $k_2=\lfloor n^\gamma\rfloor$. Complex contributions are constrained by the reality hypothesis, while real positive $\theta$ give nonnegative differences. The key comparison divides the values into three bands:

$$
A_1:\theta<n^{-\alpha},
\qquad
A_2:n^{-\alpha}\leq\theta\leq\log^{-2}n,
\qquad
A_3:|\theta|>\log^{-2}n.
$$

On $A_2$, $(1-\theta)^{k_1}$ remains bounded below by a positive constant while $(1-\theta)^{k_2}$ becomes negligible when $\alpha<\gamma$. Since $\theta^s\geq n^{-s\alpha}$, the subtracted comparison gives an expected count or chance of landing in $A_2$ of size $O(n^{s\alpha-r/2})$. Choose $s\alpha<r/6$, so this is $O(n^{-r/3})$. Multiplying by $Dn$ variables gives the total allowed $n^{1-r/3}$ contribution.

On $A_1$, Taylor expansion of $(1-\theta)^k$ in $\theta$ produces

$$
(1-\theta)^k
=\sum_{j=0}^{J}\binom kj(-\theta)^j
+O(k^{J+1}|\theta|^{J+1}).
$$

Choose $J$ proportional to $r/\alpha$. Because $|\theta|<n^{-\alpha}$, the remainder is smaller than the required $n^{-r}$ scale after multiplying by the linear number of variables. The retained sum is a polynomial $q(k,n)$ in $k$.

On $A_3$, reality follows for sufficiently large $n$ because the complex modulus threshold is only $q^{-1/2}$. The circle $|1-\theta|\leq1$ plus $|\theta|>\log^{-2}n$ bounds $|1-\theta|$ away from 1 by a logarithmic amount. Once $k\geq\log^4n$, the $A_3$ powers are exponentially small in a power of $\log n$.

Subtracting the small-band expansion and controlling $A_2$ leaves an equation saying that the expected $A_3$ contribution equals a fixed-degree polynomial $p(k,n)-q(k,n)$ plus the allowed errors. The large-$k$ decay therefore bounds that polynomial throughout a long integer interval. It remains to extend the bound back to small $k$.

Sublemma 11.2 supplies the extension. If $g$ has degree below $s$, then $(\sigma-1)^sg=0$, so for step $h$,

$$
g(x)=\sum_{j=1}^s(-1)^{j-1}\binom sj g(x+jh).
$$

If $x+i<a$ and $h=a-i$, the $s$ sampling points lie in the known interval provided

$$
i\geq a-\frac{b-a}{s-1}.
$$

The binomial weights sum to $2^s-1$. Applying this backward from $k\asymp n^\gamma$ to $k\geq1$ extends the polynomial bound. Combining all three bands gives Equation 50.

### Type check

Finite differences act on the integer variable $k$, not on $n$ or graph vertices. $q(k,n)$ is polynomial in $k$ for each fixed $n$. The coefficients $p_j,p,q$ need not have signs, which is why positivity is only used on selected weighted differences after the reality hypothesis is applied.

### Hidden assumptions

- $r,s,J,\alpha,\gamma$ are fixed in the right order before $n$ grows.
- The number of $\theta_i$ is linear in $n$.
- Nonreal contributions lie inside the modulus threshold and are summable by the given error structure.
- Polynomial degree bounds are uniform.

### Intuition

Differentiating in the discrete exponent removes every unknown polynomial and weights each spectral defect by $\theta^s$. Tiny defects can be expanded by Taylor, intermediate ones are rare by comparison of two powers, and large ones already have strong exponential decay.

### Failure modes

Without the reality condition, cancellation destroys the positive comparison. Without a uniform degree bound, the finite-difference order cannot be fixed. Trying the same direct trick on Chebyshev trace polynomials reintroduces the algebraic complexity that Section 10 avoids.

### Numerically checkable

On a finite sample of artificial $\theta$ values satisfying the circle condition, compare the exact powers and their $s$-fold finite differences to verify the algebraic identity. **Not run.**

### Remember this

Unknown polynomial coefficients are eliminated first, not estimated. Three $\theta$ regimes then turn one expansion into bounds on all spectrally relevant terms.

## D11. Final logarithmic trace estimate

### Target

Reconstruct Section 13's conversion from selective expansions to the $O(n^{-\tau_{\mathrm{fund}}})$ spectral failure bound.

### Where it appears

Section 13, pages 106 to 108, especially Equation 66.

### Inputs

**Paper.** Sections 9 through 12. $A$ denotes the event that $\chi_\Psi=0$ and every nontrivial $\mu$ is at most $q-\epsilon'$ in modulus. $B=B(\eta)$ denotes existence of nontrivial

$$
|\mu_j(\lambda_i)|\geq e^\eta\sqrt q.
$$

### Derivation

Choose $\Psi'=\Psi_{\mathrm{eig}}[r-1]$ and $\Psi=\Psi_{\min}[r-1]$. By Lemma 9.2 and Theorem 4.7,

$$
\Pr(\chi_\Psi=1)=O(n^{-\tau_{\mathrm{fund}}}).
$$

On $\chi_\Psi=0$, selective and ordinary strong traces agree. The expansion therefore concerns the real graph spectrum on this event.

Let $\nu$ range over the $nd$ values appearing in the strong power sum and define

$$
\theta=1-\frac{(1-\chi_\Psi)\nu}{q}.
$$

Then

$$
1-\theta=(1-\chi_\Psi)\frac\nu q.
$$

The spectral bounds ensure $|1-\theta|\leq1$, and nonreal values occur only at modulus $q^{-1/2}$. Lemma 11.1 applies. After multiplying by $q^k$, it controls all contributions with

$$
|\nu|\leq q(1-\log^{-2}n)
$$

by

$$
O\!\left(Dn^{1-r/3}q^k+k^cq^{k/2}\right).
$$

On $A\cap B$, a small $\eta$ puts the hypothesized outlier in the retained range covered by this estimate. If all $\mu$ were real, even powers would be nonnegative and one outlier would contribute $(e^\eta\sqrt q)^k$. Nonreal conjugate pairs can cause cancellation. Their total even-power contribution is bounded below by

$$
-2(n-1)q^{k/2},
$$

since each has modulus $\sqrt q$. Thus

$$
\Pr(A\cap B)(e^\eta\sqrt q)^k
\leq O(Dn^{1-r/3}q^k+k^cq^{k/2})
+2(n-1)q^{k/2}.
$$

Choose

$$
k=2\left\lceil\frac{r\log n}{3\log q}\right\rceil,
$$

which is even, proportional to $\log n$, and within Lemma 11.1's allowed range. It satisfies

$$
n^{-r/3}\leq q^{1-k/2}.
$$

After division by $e^{\eta k}q^{k/2}$, polynomial-in-$k$ terms are absorbed by exponentials for large $n$. The dominant form is

$$
\Pr(A\cap B)\leq Cn e^{-\eta k}
=Cn^{1-\alpha r},
\qquad
\alpha=\frac{2\eta}{3\log q}.
$$

Choose $r$ large enough that $\alpha r-1>\tau_{\mathrm{fund}}$. Then $\Pr(A\cap B)=O(n^{-\tau_{\mathrm{fund}}})$. Since $\Pr(A^c)=O(n^{-\tau_{\mathrm{fund}}})$ from tangle rarity and spreading,

$$
\Pr(B)\leq\Pr(A\cap B)+\Pr(A^c)
=O(n^{-\tau_{\mathrm{fund}}}).
$$

Finally, for $\lambda>2\sqrt q$, the larger real root

$$
\mu(\lambda)=\frac{\lambda+\sqrt{\lambda^2-4q}}2
$$

strictly increases with $\lambda$ and equals $\sqrt q$ at $2\sqrt q$. Given $\epsilon>0$, choose $\eta>0$ such that $|\lambda|\geq2\sqrt q+\epsilon$ implies $|\mu|\geq e^\eta\sqrt q$. Event $B$ is therefore exactly the spectrally dangerous non-backtracking event up to the chosen threshold. This proves the main adjacency bound.

### Type check

The normalized $\nu/q$ are dimensionless spectral values in the unit disk. Scaling Lemma 11.1 by $q^k$ restores $\nu^k$. The probability bound is dimensionless and the selected $k$ is an integer depending on $n$.

### Hidden assumptions

- $\eta$ is small enough that the outlier remains below $q-\epsilon'$ on $A$.
- The complex-pair lower bound is used only for even $k$.
- Tangle order and expansion length $r$ can be enlarged after fixing $d,\epsilon$, hence $\eta$.
- Constants in $O$ may depend on the now fixed $r,d,\epsilon$.

### Intuition

A large eigenvalue raised to logarithmic order overwhelms a linear number of Ramanujan-scale background terms. The $1/n$ expansion cancels enough structured background that only rare tangles or an actual outlier can account for the remainder.

### Failure modes

If $k$ is too small, $n q^{k/2}$ swamps an outlier. If $k$ is too large, the truncation error in $n$ grows too quickly. If $\eta\to0$, as happens when $\epsilon\to0$, $\alpha\to0$ and no uniform fixed expansion order follows from this argument.

### Numerically checkable

Given numerical $r,q,\eta,n$, compute both sides of $n^{-r/3}\leq q^{1-k/2}$ and the exponent $1-\alpha r$. This checks scale arithmetic only. **Not run.**

### Remember this

The final proof is a balance among $n^{1-r/3}q^k$, $nq^{k/2}$, and $(e^\eta\sqrt q)^k$. Logarithmic $k$ makes the balance polynomial in $n$.

## D12. Model-specific tangle exponents and transfer logic

### Target

Derive the basic $\tau_{\mathrm{fund}}$ formulas and isolate the $\mathcal J_{n,d}$ statement tension.

### Where it appears

Theorems 1.1 to 1.3, Section 4.7, Sections 6.3 and 6.4, and Section 14.

### Inputs

**Paper.** Tangle order $E-V$, non-backtracking growth, model-specific feasible edge labels.

### Derivation

For $\mathcal G_{n,d}$, pruning and contraction reduce the extremal low-order candidate to one vertex with $m$ whole-loops. Its order is $m-1$, and its non-backtracking Perron value is $2m-1$. Supercriticality requires

$$
2m-1\geq\sqrt q
\quad\Longleftrightarrow\quad
m\geq\frac{\sqrt q+1}2.
$$

The smallest feasible integer order is therefore

$$
\tau_{\mathrm{fund}}(\mathcal G)
=\left\lceil\frac{\sqrt q+1}2\right\rceil-1.
$$

Hypercriticality uses strict inequality. The least order of a hypercritical loop tangle is

$$
s(\mathcal G)=\left\lfloor\frac{\sqrt q+1}2\right\rfloor.
$$

For $\mathcal H_{n,d}$ and $\mathcal I_{n,d}$, two vertices joined by $\tau+2$ edges play the analogous role. Their order is $\tau$ and their non-backtracking growth is $\tau+1$. The resulting threshold is

$$
\tau_{\mathrm{fund}}=\lceil\sqrt q\rceil-1.
$$

Theorem 6.10 treats $\mathcal H_{n,4}$ and $\mathcal H_{n,6}$ separately because the generic multiedge candidate would need too many permutation labels. The alternative order calculations preserve the same final tau formula.

For $\mathcal J_{n,d}$, Theorem 6.12 permits half-loops and uses a four-state transition matrix for two vertices with $a,c$ half-loops and $b$ connecting edges. Its row sums are bounded by $a+b+c-1$, while order is $a+b+c-2$. Therefore growth is at most order plus 1. Two-vertex multiedge examples meet this scale, giving the same tau formula as $\mathcal I_{n,d}$.

Section 14 then transfers the proof using six properties: labels with inverses, bounded coincidence probability, factorial expansion with error, simple word sum, known $\tau_{\mathrm{fund}}$, and spreading. Domination in Corollary 1.4 needs only that the bad event tends to zero.

There is a presentation problem for $\mathcal J_{n,d}$. Theorem 1.3 imports Theorem 1.1's $\mathcal G_{n,d}$ exponents, whereas Theorem 4.13 and Theorem 6.12 calculate the larger $\mathcal I_{n,d}$ style exponents. Section 12.4 also says $\mathcal I_{n,d}$ and $\mathcal J_{n,d}$ have the same tau. These formulas cannot all describe the same lower failure exponent. For the high-probability conclusion, the stronger detailed computation implies the weaker imported rate, since a polynomial bound with larger negative exponent implies one with smaller negative exponent. For the lower probability of a strict Ramanujan violation, this inference does not apply. The paper does not supply a separate derivation reconciling that imported lower bound.

### Type check

The one-vertex and two-vertex candidates have different order formulas because $V=1$ versus $V=2$. A whole-loop contributes twice to adjacency degree but once to $E$, which is essential for $\tau_{\mathrm{fund}}(\mathcal G)$.

### Hidden assumptions

- Extremal claims include pruning and contraction reductions, not just the displayed examples.
- Feasibility in each model constrains the number of permutations or matchings available as distinct labels.
- Special small-degree cases are treated by explicit alternative tangles.
- Polynomial upper rates can weaken, polynomial lower rates cannot be weakened by the same monotonicity direction.

### Intuition

Different ensembles make different finite graphs cheap. The Ramanujan threshold stays the same, but the least costly bad local structure changes and so does the failure exponent.

### Failure modes

Assuming all models share $\tau_{\mathrm{fund}}$ because they share the Alon conclusion is invalid. Transferring a polynomial exponent through contiguity is also invalid without a further quantitative argument.

### Numerically checkable

For the $d=6$ matrix in Equation 30,

$$
M=\begin{pmatrix}4&2\\6&1\end{pmatrix},
$$

its Perron value is $(5+\sqrt{57})/2>6$. The non-backtracking growth is $\sqrt{\lambda_1(M)}$, so $\lambda_{\mathrm{Irred}}>\sqrt6>\sqrt5$. The printed sentence equating $\lambda_{\mathrm{Irred}}$ directly with $\lambda_1(M)$ conflicts with its preceding square-root statement. The square-root reading gives a valid threshold conclusion. **Not run.**

### Remember this

The Alon threshold is model independent, but tangle feasibility and exponents are model dependent. For $\mathcal J_{n,d}$, read Theorems 4.13 and 6.12 alongside Theorem 1.3 before quoting exact polynomial rates.
