# Executive map

## 1. Problem and significance

**Paper.** For fixed $d\geq3$ and $\epsilon>0$, Alon's conjecture predicts that a random $d$-regular graph on $n$ vertices has

$$
\lambda_2(G)\leq2\sqrt{d-1}+\epsilon
$$

with probability tending to one, subject to choosing a reasonable random regular graph model. Alon-Boppana says that the constant $2\sqrt{d-1}$ cannot be improved by a fixed positive amount as $n\to\infty$. Friedman proves stronger absolute bounds on every nontrivial adjacency eigenvalue for four explicit models and transfers the qualitative conclusion to dominated models by contiguity (Section 1, Theorems 1.1 to 1.3 and Corollary 1.4).

Small nontrivial spectrum implies strong expansion. The striking point is not merely that random regular graphs expand, already known earlier, but that their near-Ramanujan scale is typical with a fixed degree and an arbitrarily small additive spectral allowance.

**Interpretation.** The paper turns a heuristic based on the $d$-regular tree into a rigorous probabilistic theorem. The tree's adjacency norm $2\sqrt{d-1}$ supplies the target scale. The proof must explain why local finite subgraphs that have larger tree-completion norms do not control the global random graph with nonvanishing probability.

## 2. Main contribution

### Simplest honest form

**Paper.** In the model $\mathcal G_{n,d}$ formed by $d/2$ independent uniform permutations, for fixed even $d\geq4$ and $\epsilon>0$,

$$
\Pr\!\left[\max_{2\leq i\leq n}|\lambda_i(G)|\leq2\sqrt{d-1}+\epsilon\right]
=1-O(n^{-\tau_{\mathrm{fund}}}),
$$

where

$$
\tau_{\mathrm{fund}}
=\left\lceil\frac{\sqrt{d-1}+1}{2}\right\rceil-1.
$$

Theorem 1.1 also gives a lower bound of order $n^{-s}$ for the probability that $\lambda_2>2\sqrt{d-1}$, with $s=\lfloor(\sqrt{d-1}+1)/2\rfloor$ (pages 2 and 3).

### Strongest form in this text

**Paper.** The same near-Ramanujan conclusion, with model-specific polynomial failure rates, is proved for:

- $\mathcal H_{n,d}$, using $d/2$ independent $n$-cycles,
- $\mathcal I_{n,d}$, using $d$ independent perfect matchings for even $n$,
- $\mathcal J_{n,d}$, using $d$ independent near-perfect matchings with half-loops for odd $n$.

The simple-word and factorial estimates are abstracted into six sufficient model conditions in Section 14, pages 108 to 112. Corollary 1.4 transfers the $1-o(1)$ conclusion to any dominated model. The method does **not** set $\epsilon=0$ and does not prove typical exact Ramanujan spectrum.

## 3. Core mechanism in one display

**Paper plus derived compression.** The standard trace expansion mixes two quantities:

$$
\underbrace{\text{number of legal walks on a type}}_{\text{can grow too fast}}
\quad\times\quad
\underbrace{\text{sums over beaded edge lengths}}_{\text{have inverse exponential decay}}.
$$

For ordinary types this product can fail to converge with error below $(d-1)^{k/2}$. Selective traces discard any walk with a short segment tracing a supercritical tangle. Theorem 6.6 then gives, for long-edge and fixed-edge multiplicities $M_1,M_2$,

$$
W_{\widetilde T,S}(M_1,M_2)
\leq c\bigl(\sqrt{d-1}-\eta\bigr)^{BM_1+M_2}.
$$

The edge-length sums contribute inverse factors like

$$
(d-1)^{(-BM_1-M_2+O(1))/2}
$$

to principal coefficients and analogous factors to error terms. Multiplying produces geometric decay in $BM_1+M_2$ because

$$
\frac{\sqrt{d-1}-\eta}{\sqrt{d-1}}<1.
$$

This makes the $1/n$ coefficients d-Ramanujan through arbitrarily high finite order (Theorems 8.1 and 8.2). The expansion coefficients themselves do not need to be computed.

**Interpretation.** The whole technical architecture exists to create and exploit that strict spectral gap $\eta>0$.

## 4. Handling the discarded walks

**Paper.** Selective traces are not the original traces on a tangled graph. Section 9 therefore expands the expected selective trace separately on the event that prescribed tangles occur. Möbius inversion converts tangle indicators into finite inclusion counts. Lemma 9.2 proves that the minimal supercritical tangles of order at most $r$ form a finite set. Corollary 9.4 then gives an expansion on the tangle-free stratum, where selective and ordinary strongly irreducible traces coincide (Sections 9 and 13).

Section 10 rewrites strongly irreducible traces as pure power sums of

$$
\mu_{1,2}(\lambda)=\frac{\lambda\pm\sqrt{\lambda^2-4(d-1)}}2.
$$

Section 11 applies finite differences in $k$ to annihilate unknown polynomial coefficients. Magnification provides a priori spectral separation. Finally, a logarithmic trace length converts a possible outlier $\mu$ into a probability bound $O(n^{-\tau_{\mathrm{fund}}})$.

## 5. Main assumptions

- $d$ is fixed as $n\to\infty$, with parity restrictions tied to each model.
- $\epsilon>0$ is fixed and independent of $n$.
- The primary permutation model allows loops and multiple edges and uses whole-loop adjacency weight 2.
- The models satisfy vertex-relabelling symmetry and suitable occurrence, coincidence, and word-sum estimates.
- Selective traces exclude short segments containing tangles with $\lambda_{\mathrm{Irred}}\geq\sqrt{d-1}$.
- Several key identities are cited as inputs, notably Ihara-Bass, adjacency magnification bounds, and contiguity results.

## 6. Main techniques

1. Adjacency and non-backtracking trace methods.
2. Rayleigh quotients and two-dimensional subspaces for $\lambda_2$ lower bounds.
3. Variable-length graphs, realization, generating functions, and Perron growth rates.
4. Tree completion $\operatorname{Tree}_d(\psi)$ and the Ihara-Bass determinant relation.
5. Tangle order $|E|-|V|$ and expected occurrence $n^{-\operatorname{ord}(\psi)+O(1)}$.
6. Walk forms, compressed types, and new types recording fixed versus long edges.
7. Selective traces and generating function majorants.
8. d-Ramanujan functions, convolution, and inverse factorial expansions.
9. Möbius inversion over tangle inclusion.
10. Strongly irreducible traces, finite differences, and spreading estimates.

## 7. What the two visuals contribute

**Paper and derived.** Figure 1 on page 31 depicts a finite $\psi$ beside its infinite 4-regular tree completion. It makes the local defect and its infinite branching continuation visible. The accompanying Theorem 3.13 says that this infinite graph exceeds the $2\sqrt{d-1}$ threshold exactly when $\lambda_{\mathrm{Irred}}(\psi)>\sqrt{d-1}$.

Figure 2 on page 41 depicts the same traced walk before and after degree-two vertices are suppressed. It clarifies why a form remembers traversal data while a type retains only the compressed topology. Repeated traversal does not create new form edges. New types later add fixed labels and length constraints, information not drawn in Figure 2.

## 8. Mastery targets

After mastering this paper, the user should be able to:

- State all four random graph models and keep their exponents distinct.
- Explain why trace powers grow like $\lambda^k$ but also like counts of closed walks.
- Derive the non-backtracking recurrence and the $\mu^2-\lambda\mu+(d-1)=0$ relation.
- Explain critical, supercritical, and hypercritical tangles without conflating them.
- Reproduce $\operatorname{E}[\Gamma]_n=n^{v-e}(1+O(1/n))$ and relate $e-v$ to tangle order.
- Walk through Figure 2 and show which edges survive compression.
- Derive the strict walk bound in Theorem 6.6 at the level of its generating function decomposition.
- Explain why tangle-free strata restore the ordinary trace.
- Apply one finite difference to a power sum and explain why strong irreducibility helps.
- Reconstruct the final probability scale and name what fails when $\epsilon=0$.

## 9. Honest reading boundary

**Interpretation.** The main argument is coherent at the level of its architecture and central calculations. The supplied text also contains local algebraic and inclusion-direction defects. They are documented separately rather than used to inflate or dismiss the paper's contribution. A complete referee-grade audit of all 118 pages remains beyond this comprehension dossier.
