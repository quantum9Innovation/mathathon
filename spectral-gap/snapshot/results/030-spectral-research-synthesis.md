# Referee synthesis of eight spectral research directions

## State

Swarm `smwgfcleu` has finished. All eight submissions have named accepted verdicts,
each with an explicit scope. Three initial submissions were rejected and revised. The
accepted record contains proved statements, exact finite computations, numerical
experiments and conjectures. These categories are not interchangeable.

This is a referee synthesis, not mathematical certification. No proof assistant was
used, and no exhaustive novelty audit was performed. Numerical convergence was not
promoted to an asymptotic theorem. The accepted artifacts and their remaining caveats
are linked below.

The eight members used `deepseek/deepseek-v4.1-flash` at maximum reasoning effort.
Three directions required correction before acceptance. The swarm has no live members.

## 1. Verdict ledger

| Direction | Accepted scope | Important limitation |
| --- | --- | --- |
| Periodic lattices, `m1`, `d2` | Exact Bloch decomposition, coset range theorem, band-edge law for positive definite Hessian | Semidefinite remainder claim not accepted, positivity and sharp packing constant open |
| Directed spectra, `m2`, `d6` | Singular-value lower bound, normal aperiodic constant, real Joukowski transfer, period bookkeeping | Periodic normal constant and random singular-value limit open |
| Multiplicity, `m3`, `d8` | Seidel trace bound, equality criterion, Moore bound, exact Cartesian-product examples | No sublinear multiplicity theorem follows from two moments alone |
| Relative irregular covers, `m4`, `d4` | Biregular radius and bands, quartic equivariant conversion, exact root-defect bound state | General irregular polynomial-rate conversion remains open |
| Degree defects, `m5`, `d3` | Spiked-tree spectrum outside the bulk and exact added-vertex secular identity | Finite-host asymptotic remains conditional on an off-bulk resolvent estimate |
| Binary Cayley graphs, `m6`, `d5` | Character-code dictionary, degree barrier, Plotkin and shortening bounds | Coding crossover and missing near-half-distance bound open |
| Non-abelian Cayley graphs, `m7`, `d7` | Irreducible-block law, exact small-group classifications, coset and prism calculations | Uniform per-block trace bound and asymptotic conjectures open |
| Hypergraphs, `m8`, `d1` | Incidence Gram identity, top and lower multiplicities, signed-cover identity, exact examples | Random-lift exponent, tangle calculus and edge fluctuations open |

Earlier review records are in [the review directory](spectral-research/reviews/). The
last two detailed decisions and their repairs are in [lattice and relative-cover
review notes](spectral-research/reviews/d2-d4-review-notes.md).

## 2. Results that survive review

### 2.1 Periodic covers have arithmetic, not tree, second-order defects

For a connected $\mathbb Z^d$-periodic graph, a finite-index sublattice $\Lambda$
has quotient spectrum equal to the Bloch spectrum sampled at $\Lambda^*/\mathbb Z^d$.
Let $M$ be minus the Hessian of the top Bloch band at $0$, assuming $M>0$. Away from
the small-quotient plateau, the top-gap law is governed by the nonzero coset minimum

$$
\mu_M(\Lambda)=\min_{z\in\Lambda^*\setminus\mathbb Z^d} z^{T}Mz,
\qquad
\lambda_1-\lambda_2=\tfrac12\mu_M(\Lambda)+O(\mu_M(\Lambda)^2).
$$

The corrected fixed-index range is

$$
\frac{\lambda_{\min}(M)}{N^2}\leq \mu_M(\Lambda)
\leq 4N^{-2/d}\left(\frac{(\det M)^{1/2}}{\omega_d}\right)^{2/d}.
$$

The lower order is attained by skew sublattices and the upper order by cubic
sublattices. The important correction is that the minimum is over a finite group on a
torus, not over all nonzero lattice vectors. Minkowski's shortest-vector theorem alone
cannot prove its upper endpoint.

In the abelian Cayley case the constant is the arithmetic minimum of the sum-of-squares
coordinate form, not merely the smallest eigenvalue of the Hessian. This exact constant
and the range statement complement, but do not improve, the known
Friedman-Murty-Tillich exponent.

**Not accepted:** the remainder argument uses $\lambda_{\min}(M)>0$. A singular-Hessian
law needs its own proof. The numerical script checks 17 selected indices up to $256$,
not every index up to $256$ as the submission report says.

[Dossier](../.ultramath/smwgfcleu/m1/DOSSIER.md) and [proof file](../.ultramath/smwgfcleu/m1/PROOF-band-edge-law.md).

### 2.2 For irregular covers, qualitative convergence is settled but rates are not

Bordenave-Collins already gives Hausdorff convergence of the new adjacency spectrum to
the universal-cover spectrum in probability. Re-proving that qualitative threshold is
therefore not a research target. The open quantitative problems are polynomial error
probabilities, internal-band filling and nonbacktracking-to-adjacency conversion.

For the $(d_1,d_2)$-biregular tree, with $a=d_1-1$ and $b=d_2-1$, the period-two
Collatz-Wielandt weight gives

$$
\rho(A_T)=\sqrt a+\sqrt b,
$$

rather than merely $2\sqrt{\max(a,b)}$. The latter is exactly the optimum over
single-exponential radial weights. The biregular quartic conversion, its correct branch
and its deck-group equivariance give the sharp upper-edge transport to the
nonbacktracking threshold. This is the useful input for both biregular graph lifts and
hypergraph incidence lifts.

The corrected root-defect example shows why periodic bands are not automatically the
whole spectrum. Its radial Jacobi essential spectrum is
$\pm[\sqrt2-1,\sqrt2+1]$, but $\sqrt6$ is an exact discrete eigenvalue. The explicit
Jacobi eigenvector satisfies $u_{k+2}=u_k/\sqrt2$ in the tail and has squared norm $8$.
The full-tree eigenfunction is $u_k/\sqrt{|S_k|}$ on sphere $S_k$.

This proves an essential-versus-discrete distinction. It does not prove the withdrawn
claim that non-radial modes increased the radius, and the defect tree is not promoted
to a finite-base universal cover. The old unqualified spectrum equivalence in the
header of `scripts/floquet_bands.py` remains a documentation trap and is not accepted.

[Dossier](../.ultramath/smwgfcleu/m4/dossier.md), [independent exact certificate](spectral-research/reviews/d4_bound_state_review.py), [certificate output](spectral-research/reviews/d4_bound_state_review.json).

### 2.3 Hypergraph gap indices need operator and end-of-spectrum bookkeeping

For a $k$-uniform $d$-regular hypergraph $H$ with incidence matrix $X$, the Feng-Li
adjacency satisfies

$$
A_H+dI=XX^{T},\qquad \lambda_{\min}(A_H)\geq -d.
$$

The multiplicity of $-d$ is $n-\operatorname{rank}X$. It is forced both by
rectangularity and by strong $k$-colourings. At the top, the Perron value of the clique
expansion is $(k-1)d$ with multiplicity equal to the component count. Hence
$(k-1)d-\lambda_2$ is the first top gap. The formulas $d-\lambda_3$ and $d-\lambda_4$
do not acquire structural meaning merely from uniformity.

The same Gram identity controls signings of $2$-covers. The clean lower two-sided
consequence under stated full-rank hypothesis must not be paraphrased as an unconditional
rank-deficient classification. The exact rank formula remains the right statement.

For strongly connected period-$m$ regular digraphs, there are instead $m$ peripheral
eigenvalues. There the first informative index is $m+1$. Thus $d-\lambda_3$ or
$d-\lambda_4$ can be appropriate for period two or three, but for a fundamentally
different reason. The common rule is to remove the trivial spectrum before naming a
gap.

[Dossier](../.ultramath/smwgfcleu/m8/README.md) and [open directions](../.ultramath/smwgfcleu/m8/04-open-directions.md).

### 2.4 One defect distinguishes three limits

For the rooted tree with one degree-$\Delta$ vertex and all other degrees $d$, the
essential bulk stays $[-2\sqrt{d-1},2\sqrt{d-1}]$. A discrete outer pair occurs
exactly for $\Delta>2(d-1)$:

$$
\lambda_*=\frac{\Delta}{\sqrt{\Delta+1-d}}.
$$

This is the correct spectrum outside the bulk. Embedded bulk eigenvalues were not
classified.

Adding a vertex adjacent to a fixed set $T$ to any finite host has the exact
characteristic-polynomial factor

$$
\det(\lambda I-A_G)\left(\lambda+\mathbf1_T^{T}(A_G-\lambda I)^{-1}\mathbf1_T\right).
$$

The finite-host prediction uses the full Kesten-McKay transform, not the one-sided
tree branch. The corresponding prospective threshold $2(d-2)$ differs from the tree
threshold $2(d-1)$. The finite-host result remains conditional, and the spiked rooted
tree is a local limit at the defect, not a substitute for the universal cover of a
finite irregular graph.

[Spiked-tree and secular dossier](../.ultramath/smwgfcleu/m5/DOSSIER.md) and [review](spectral-research/reviews/d3-first-review.md).

### 2.5 Multiplicity, representations and normality are separate faces

The exact Seidel two-moment proof gives, for eigenvalue multiplicity $q$ at $\theta$,

$$
q\leq\frac{n(n-1)}{n-1+\theta^2}.
$$

Equality forces two distinct Seidel eigenvalues. This reproduces the standard relative
equiangular-line estimate, but cannot alone give a sublinear fixed-degree
second-eigenvalue multiplicity theorem. The connected equality case also obeys
$n\leq d^2+1$. Exact $K_4\square C_k$ examples have $\lambda_2=\lambda_3$ and a
positive fraction of eigenvalues above a fixed degree-relative threshold.

For $G=\mathbb F_2^r$, the spectrum of $\operatorname{Cay}(G,S)$ is the weight
enumerator of the binary row-space code generated by $S$. This makes the degree barrier
$r\leq d$, negativity rigidity and shortening bounds exact. In general finite groups,
the adjacency decomposes into irreducible-operator blocks, with multiplicities governed
by representation degrees. The exhaustive $S_4$, $A_5$ and $S_5$ cubic computations
identify which blocks obstruct Ramanujan behavior. Girth alone and the tested coset
bound do not explain all failures.

For $k$-regular digraphs, the bipartite double cover gives the universal
$\sigma_2\geq2\sqrt{k-1}-o(1)$ bound. Normal aperiodic digraphs convert it to the same
nontrivial eigenvalue threshold, while line digraphs attain the $\sqrt k$ threshold in
the $2$-normal class. The real Ihara-Bass/Joukowski correspondence explains the
coordinate change. Unrestricted strongly non-normal digraphs do not inherit either
eigenvalue bound.

[Multiplicity dossier](../.ultramath/smwgfcleu/m3/dossier/main.md), [binary-code dossier](../.ultramath/smwgfcleu/m6/dossier.md), [finite-group dossier](../.ultramath/smwgfcleu/m7/dossier/README.md), [directed dossier](../.ultramath/smwgfcleu/m2/dossier/main.md).

## 3. Corrections that must not be lost

1. **Old shortest-vector range argument:** rejected. A coset minimum is not a
   shortest full-lattice vector. The torus-packing replacement is correct.
2. **Old irregular-tree angular explanation:** rejected. Radial and full-tree top
   finite-ball eigenvalues agree. The valid example has a radial discrete bound state
   above the essential bands.
3. **Old directed claims:** a free cyclic automorphism does not fix the period, the
   real Joukowski equivalence does not extend directly to complex adjacency values,
   singular values are not signed eigenvalues, and root degrees belong in walk counts.
   The accepted revision corrects all four.
4. **Old-spectrum multiplicity:** an $n$-lift contains one copy of the base spectrum
   on fibre-constant functions, not $n$ copies.
5. **Finite versus infinite defect equation:** the local rooted tree does not contain
   the finite host's Perron pole. The branch resolvent and Kesten-McKay transform are
   different objects.
6. **Incidental numerical errors:** the lattice enumeration is sampled rather than
   exhaustive over all indices up to $256$. $Q_4$ does not belong in the Seidel
   zero-slack equality list. Neither affects the accepted exact results.

The earlier board findings that repeated the withdrawn angular or shortest-lattice
claims are historical records, not reusable lemmas.

## 4. Prioritised research programme

### 1. Prove an off-bulk resolvent local law for finite degrees

**Target:** for a uniform random $d$-regular host, fixed finite $T$, and $\lambda$ on
compact subsets of $(2\sqrt{d-1},d)\cup(d,\infty)$, prove convergence of
$\mathbf1_T^T(A-\lambda I)^{-1}\mathbf1_T$ to the corresponding Kesten-McKay
diagonal sum, with a rate.

This would turn the finite-defect fixed point, its threshold $2(d-2)$, and the finite
near-trivial correction into theorems. The missing ingredient is control of local
resolvent entries, not just global eigenvalue locations. Local tree-likeness and
resolvent path expansions are available ideas, but concentration must be proved rather
than inferred from simulations. Multi-defect interaction and sublinear defect density
are follow-up problems, not established consequences.

### 2. Establish polynomial-rate adjacency conversion for irregular lifts

**Target:** transport new nonbacktracking bounds to new adjacency bounds through the
degree matrix pencil, with an explicit exceptional probability.

The biregular quartic and its equivariant injection supply a working model. General
irregular degrees eliminate a scalar eigenvalue quadratic. A convincing attack needs
oriented-edge-type spectral data or a genuine matrix-pencil perturbation estimate. A
vertex-type Floquet edge alone is insufficient, and essential bands alone can miss
isolated bound states.

A concrete internal-gap companion is already recorded in [the two-band assessment](../results/040-internal-gap-theorem.md): generic quantitative strong convergence gives an
$O(1/N)$ exclusion for $K_{4,3}$ on compact intervals strictly inside its gap. The
unsolved task is a matching minimal-tangle lower bound and an optimal exponent. It
must distinguish new modes from old, zero and auxiliary modes.

### 3. Build the hypergraph relative tangle calculus

The incidence universal-cover threshold is already pinned. Relative lifts therefore
offer no threshold improvement. The open issue is the failure exponent and the
classification of minimal hypergraph tangles.

Start with $(2,3)$-regular incidence graphs, where small feasible pieces can be
enumerated. Use the existing biregular quartic transport instead of treating scalar
Ihara-Bass as automatically valid. At the lower end, classify rank-deficient incidence
matrices for $d<k$ before claiming a complete two-sided cover theorem. At fixed higher
indices, study joint edge fluctuations after checking the limiting density's edge
exponent, rather than assuming $d-\lambda_3$ is a new invariant.

### 4. Prove bounds for the actual extremal blocks

Two precise versions survive:

* a uniform near-half-distance coding bound explaining the transition of sparse binary
  Cayley graphs beyond the proved shortening regime,
* a uniform estimate for individual Cayley irreducible blocks, adequate to control
  irreducible-degree-weighted quasi-indices.

The finite classifications show why aggregate trace estimates and abelianization alone
are too coarse. A useful next proof should identify the block that carries the extremum
before estimating it. Low-degree induced or monomial blocks are specific test cases.

### 5. Settle positivity of the periodic effective mass, or consult its precise literature status

The goal is either a proof that the top Bloch band of every connected periodic graph
has positive definite Hessian at its trivial-character maximum, or a connected singular
counterexample. The accepted strictness argument requires arbitrary complex
eigenvector phases. Cycle-winding integrality then gives torsion characters. That is
the correct basis for a revised exposition.

This problem gates the clean $N^{-2/d}$ periodic sampling rate. Current numerical
scans are evidence only. The existing effective-mass literature must be checked before
calling the conjecture new.

### 6. Resolve the remaining directed and multiplicity regimes

Determine the sharp normal $k$-regular digraph constant for fixed period $m\geq2$, and
decide whether the permutation model has $\sigma_2\to2\sqrt{k-1}$. The latter needs a
random-model argument, because its double cover is not a uniform simple biregular
graph.

For undirected fixed-degree multiplicity, move beyond two moments to walk support,
short-cycle arguments or representations. The exact equality and product examples
show why a universal positive-index or two-moment shortcut cannot work.

## 5. Verification record and boundaries

The review ran the decisive member scripts and independent calculations. These include
the exact secular and spiked-tree tests, Seidel and bounded Nauty enumerations, periodic
and line-digraph repairs, binary characteristic-polynomial comparisons, finite-group
spectrum calculations, hypergraph determinant identities, biregular transfer checks,
and the new independent root-defect certificate. The revised lattice coset script and
the new bound-state scripts were run again in this continuation.

The earlier individual verdicts name checks and exclusions in detail. Not every random
experiment or bibliographic assertion was exhaustively rerun. No Lean files were
created or checked. Generic numerical scripts are reproducibility evidence, not proof
certificates.

The initial [common threshold framework](spectral-research/00-threshold-framework.md)
and [source notes](spectral-research/SOURCE-NOTES.md) remain the literature baseline.
In particular, qualitative irregular-lift convergence and standard hypergraph bulk
thresholds must not be advertised as new. The genuinely unresolved opportunities are
the explicit estimates, minimal defects and blockwise mechanisms listed above.
