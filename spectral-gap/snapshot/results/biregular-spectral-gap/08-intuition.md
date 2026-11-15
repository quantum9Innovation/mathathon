# Intuition at several altitudes

## One sentence

Typical random biregular graphs are almost Ramanujan because their non-backtracking non-leading spectra can be confined to the universal-cover bulk radius, and Ihara-Bass turns that confinement into sharp control of every adjacency spectral edge.

## One paragraph

The adjacency matrix is awkward to study through moment methods because powers count walks with complicated immediate reversals. The non-backtracking matrix removes that local nuisance but is non-normal and complex-spectrum valued. Ihara-Bass gives the dictionary: in the bulk, squared $B$ eigenvalues lie on $|x|=\sqrt{ab}$, above-bulk adjacency outliers create real $B$ outliers, below-bulk ones create imaginary outliers, and left nullvectors of $X$ create $\pm i\sqrt a$. The authors then center the matching that generates $B$, take a high Schatten moment, and count circuits by their cycles and repeated edges. Repeated-edge tree-like circuits dominate. Rare or complicated circuits pay for their complexity. With no non-leading outliers in $B$, no such adjacency outliers can exist either.

## Five-minute whiteboard version

Write these four objects first:

$$a=d_1-1,\qquad b=d_2-1,\qquad \rho=\sqrt{ab},\qquad \tau=(ab)^{1/4}.$$

Then draw Figure 3B abstractly:

- A circle of radius $\tau$.
- Two dominant real points at $\pm\rho$, outside it.
- Orange non-leading eigenvalues clustered around the circle.
- A few real and imaginary finite-sample outliers to be ruled out asymptotically.

Next write the dictionary:

$$y=x+\frac{ab}{x}+a+b,\qquad x=\lambda^2,\quad y=\xi^2.$$

Draw the same circle in $x$. Explain adjacency bulk values by $\operatorname{Im}y=v(1-ab/|x|^2)=0$. Complex $x$ requires $|x|=\sqrt{ab}$. Then draw two arrows:

$$\xi^2>(\sqrt a+\sqrt b)^2
\Longrightarrow \text{real outer }\lambda>\tau,$$

$$\operatorname{rank}X<n
\Longrightarrow \pm i\sqrt a\in\sigma(B).$$

Finally draw four alternating circuit legs like Figure 4. Say exactly why they exist:

$$\mathbb E\|C\|^{2k}
\leq\mathbb E\operatorname{Tr}((CC^*)^k).$$

Repeated-edge circuits are leading, excess-cycle circuits have extra inverse-$n$ powers, and large-vertex circuits pay centering penalties. Taking the $\ell$th root finishes with radius $\tau+o(1)$.

## Geometric picture of the main theorem

The transformation is not “second eigenvalue of $A$ equals second eigenvalue of $B$.” That would be false and would also miss the rank argument. Instead, there is a many-to-one spectral map. Each nonzero adjacency pair generates four $B$ roots, while every zero adjacency direction generates an imaginary $B$ root with a precise side-dependent scale.

**Interpretation:** The non-backtracking plane unfolds the two-sided adjacency spectrum into a complex circle together with radial and angular exceptions. The probabilistic proof removes all non-leading radial exceptions at once. Figure 3 is the static picture of that mapping. Figure 4 explains why the removal is proved through segmented traces rather than ordinary vertex walks.

## Why the threshold looks the way it does

On the infinite biregular tree, non-backtracking branching alternates between $a=d_1-1$ and $b=d_2-1$. Over a two-step alternation, the mean branching factor is $\sqrt{ab}$. That is the leading $\rho$.

The bulk radius of the non-backtracking spectrum is smaller, $\tau=\sqrt{\rho}=(ab)^{1/4}$. This square-root-of-Perron relation is the non-backtracking analogue of the familiar relationship between dominant adjacency and non-backtracking spectra in expander analysis.

The upper adjacency edge then satisfies

$$(\sqrt a+\sqrt b)^2
=2\sqrt{ab}+a+b
=f(\sqrt{ab}),$$

and $\sqrt{|\sqrt{ab}|}$ recovers $\tau$. The lower edge comes from the other real meeting of branches, at $y=(\sqrt a-\sqrt b)^2$.

## Small example: the complete bipartite sanity case

Take $K_{2,3}$, the small graph at the left of Figure 2. Here $n=2,m=3,d_1=3,d_2=2$, so the adjacency nonzero singular values are only $\pm\sqrt6$. All other adjacency eigenvalues are zero. This graph is small and highly non-generic, so its $\eta=\sqrt6$ should not be expected to illustrate the large-random-graph theorem. It does illustrate two robust pieces:

1. The signed adjacency pair comes from a single nonzero singular value.
2. The rank of $X$ is $n=2$, but forced zero directions remain because $m>n$.

The right graph in Figure 2 has the same side sizes and degree sequence as two disjoint copies of $K_{2,3}$, but its wiring destroys any identical-lift interpretation. Equal local statistics do not determine global topology or spectral gaps.

## A purely algebraic rank example

Suppose a hypothetical tall $X$ lost row rank, so some $w\neq0$ satisfied $X^*w=0$. The Ihara-Bass block equations do not care how rank loss arose probabilistically. They immediately manufacture a $B$ eigenvector $(w,0)$ with value $\lambda=i\sqrt a$ because $a+\lambda^2=0$. That single deterministic observation is powerful: to prove almost-sure rank, it is enough to prove that $B$ cannot have such a large non-leading eigenvalue asymptotically almost surely.

## The trace proof as three accounting rules

1. **Repeated edges are cheap enough.** A circuit of fixed traversal budget can visit relatively few distinct edges if each edge repeats. These terms determine the $\tau$ power.
2. **Extra cycle structure costs inverse size.** Each independent cycle leaves an additional factor resembling $1/n$, after the vertex choices and matching probability are canceled.
3. **Too many new edges trigger centering costs.** When a circuit exceeds the repeated-edge vertex budget, many singleton edges appear. Centered matching products penalize them with extra $k\ell/\sqrt{|E|}$ factors.

This is why Figure 4 is not an isolated illustration. Every arrow and shared purple join matters to the accounting.

## What Figure 5 adds to intuition

A naive encoding stores the entire walk. Figure 5 shows that repeating a single cycle adds almost no new information if its location and one discovery pattern are already known. The triple encoding stores the *instructions for rediscovery*, not every physical step. This is how the path count becomes subpolynomial. The incorrect numeric labels in the figure do not change that conceptual compression, but they make the caption unsuitable as an arithmetic example.

## What Figure 6 adds to intuition

Frame graph vertices behave like a small quotient graph. The left panel is a set of wiring rules, the right panel is a large inflation of those rules. Frame eigenvectors are constant within colors, while non-frame eigenvectors vary inside classes. Making all degrees large suppresses that internal fluctuation relative to the quotient spectrum. Different arrow widths on the frame are not aesthetic. They encode unbalanced reciprocal degrees, balanced only after class proportions are included.

## What is surprising here

- A second-spectral-gap theorem also proves a lower positive spectral edge and rectangular full row rank, with almost no extra probabilistic work.
- The non-leading non-backtracking eigenvalues do not sit merely inside the disk at finite $n$. Figure 3 has eight explicit finite-sample outliers. Only asymptotic radial control is claimed.
- Tree-like repeated-edge circuits dominate even though the entire assembled circuit may be tangled.
- The biadjacency matrix for matrix completion yields stronger constants than the cited square adjacency sampling setup, with the same core expander-mixing idea.

## What would naive baselines do?

| Naive approach | Why it is inadequate |
| --- | --- |
| Apply an ordinary regular-graph theorem verbatim | Biregular adjacency has two degree scales and structural zero eigenvalues, and the non-backtracking roots split into more cases |
| Replace the configuration model by a random lift | Figure 2 shows that desired degree sequences include graphs outside a single lift construction. Non-contiguity is suggested as a concern, not assumed away |
| Use only Alon-Boppana lower bound | It rules out being substantially better than Ramanujan, but not bad upper outliers |
| Bound $\Vert B^\ell\Vert$ by uncentered walk counts | Deterministic dominant modes and excessive walk multiplicity swamp the target scale |
| Treat $\bar B^\ell$ as Hermitian | $B$ and its centered variants are not symmetric. Ordinary eigenvalue traces are insufficient, hence $CC^*$ moments |
| Count each full circuit as globally tangle-free | Individual matrix-factor legs are tangle-free, but their union need not be |
| Read Figure 3 as a proof | It is one sample with no rate or probability. Its eight outliers emphasize why a real proof is necessary |
| Drop $\epsilon_n$ in the code example and call the bound finite-$n$ certified | The theorem's unspecified asymptotic error prevents that inference |
| Use biadjacency singular values as if the negative adjacency eigenvalues were independent | They are exact partners, and signs vanish after $y=\xi^2$ |

## The best mental compression

**Configuration model supplies random matchings, tangle-free paths supply small encodings, centered traces suppress non-leading $B$ outliers, and Ihara-Bass converts that one-dimensional radial statement into upper, lower, and rank conclusions for $A$.**
