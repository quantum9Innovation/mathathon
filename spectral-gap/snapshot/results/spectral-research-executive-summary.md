# Spectral graph research: executive summary

## Bottom line

Eight research directions were reviewed and retained with clear limits. The main
progress is a better map of which spectral quantity controls each setting. A single
universal second-eigenvalue formula is not the right goal. The useful distinctions are
between bulk bands, isolated defect eigenvalues, old and new cover spectra, trivial
multiplicities, and lattice sampling effects.

The next work should focus on explicit estimates that current qualitative theorems do
not provide.

## What we progressed on

1. **Periodic lattices.** Finite abelian quotients are described exactly by Bloch
   sampling. With a positive-definite band Hessian, the leading spectral gap is a
   shortest-coset calculation for a quadratic form. Skew and cubic sublattices produce
   two different gap orders at the same index. This replaces the faulty shortest-lattice
   argument with a valid torus-packing proof.

2. **Irregular random lifts.** The biregular universal-cover radius and the correct
   nonbacktracking-to-adjacency conversion are now explicit. A corrected tree example
   has an eigenvalue above its radial periodic bands, showing why essential bands alone
   need not determine the spectral radius. The earlier non-radial explanation was
   withdrawn. Qualitative new-spectrum convergence is already in the literature, so
   novelty must come from quantitative rates and sharper spectral information.

3. **Hypergraphs and gap indexing.** The incidence identity $A_H+dI=XX^T$ explains the
   lower spectral plateau and its multiplicity. The top clique-expansion gap must use
   the correct Perron value $(k-1)d$. Higher indices do not acquire new meaning merely
   because a hypergraph is uniform. Periodic digraphs are different: their peripheral
   spectrum explains when the first informative index really is $3$ or $4$.

4. **Almost regular graphs.** For a rooted tree with one degree defect, the bulk stays
   unchanged and a discrete outer eigenvalue appears exactly when
   $\Delta>2(d-1)$. An exact determinant identity also describes adding one vertex to a
   finite graph. These calculations distinguish the infinite defect tree from the
   finite-host prediction, which remains conditional.

5. **Cayley graphs, directed spectra and multiplicities.** Binary Cayley spectra are
   translated exactly into code weights. General finite-group spectra are translated
   into irreducible blocks, with exact small-group classifications and identified
   obstructing blocks. For digraphs, the universal singular-value bound is separated
   from eigenvalue bounds controlled by normality and period. Exact Seidel and product
   examples show why higher gaps and multiplicities cannot be handled by one simple
   index rule or by two moments alone.

All three initially rejected arguments that were central to their submissions were
revised and rechecked. The experimental and exact-computation records are preserved.
These are reviewed research dossiers, not formal proof certificates or exhaustive
novelty claims.

## The three open problems to focus on next

### 1. Prove the finite-defect resolvent estimate

**Question.** For a random regular host, prove that resolvent entries on a fixed finite
vertex set converge to the Kesten-McKay prediction away from the bulk. The required
window is between the bulk edge and the host's Perron eigenvalue, together with the
region above that eigenvalue.

**Why it matters.** This is the missing input for turning the finite-defect fixed point,
the predicted threshold $2(d-2)$, and the near-trivial finite-size correction into
proved asymptotics rather than strongly supported conjectures.

**First concrete step.** Expand local resolvent entries through nonbacktracking paths
on a fixed compact spectral interval. Combine local tree-likeness with a concentration
estimate that controls the local entries themselves. A proof for one fixed $\lambda$
would already be meaningful progress before seeking uniformity in $\lambda$.

### 2. Obtain quantitative adjacency bounds for irregular lifts

**Question.** Convert polynomial-probability control of new nonbacktracking eigenvalues
into the same control for new adjacency eigenvalues of a lift with nonconstant degrees.

**Why it matters.** Bordenave-Collins already settles qualitative convergence. The
useful remaining advances are explicit exceptional probabilities, optimal exponents,
and filling or exclusion inside spectral gaps. The biregular quartic conversion is now a
working template. General degrees lead to a matrix pencil, not a scalar quadratic.

**First concrete step.** Prove the conversion for the next smallest irregular family,
using oriented-edge types or the degree-matrix pencil. Keep old, new, zero and auxiliary
modes separate. In parallel, the existing $K_{4,3}$ inner-gap result needs a matching
minimal-tangle lower bound before its generic $O(1/N)$ rate can be called optimal.

### 3. Build a hypergraph relative-tangle theory

**Question.** For random covers of a regular hypergraph incidence graph, determine the
exceptional-probability exponent at the known biregular spectral threshold and classify
the smallest hypergraph obstructions controlling it.

**Why it matters.** The threshold itself offers no relative improvement over the
universal-cover value. The open content is the exponent and the combinatorics behind it.
This is where the graph tangle machinery genuinely needs a hypergraph extension.

**First concrete step.** Enumerate the small feasible pieces for $(2,3)$-regular
incidence graphs and compute their relevant nonbacktracking growth. Use the established
biregular conversion rather than assuming the regular-graph quadratic applies. At the
negative end, separately classify rank-deficient incidence matrices before claiming a
complete two-sided cover result.

## How to read the supporting record

Start with the [full synthesis](030-spectral-research-synthesis.md) for the eight-way
comparison and proof boundaries. The [detailed review notes](spectral-research/reviews/d2-d4-review-notes.md)
record the last two corrections and their remaining qualifications. The [independent
bound-state check](spectral-research/reviews/d4_bound_state_review.py) reproduces the
exact relative-cover example.

No Lean verification or complete citation audit was performed. Numerical evidence is
marked as evidence, not proof. The three priorities above are selected because each has
a precise missing estimate and a concrete first computation, not because novelty is
already certified.
