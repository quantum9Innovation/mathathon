# Batch 050 preparation: finite-defect resolvent and eigenvalue limits

## Purpose and scope

Attack one theorem-sized problem from the accepted synthesis: the finite one-defect
secular equation. The exact determinant identity is established. The proposed limiting
roots are not established, because the resolvent hypothesis remains unproved.

The queue entry is pending. Its three-hour budget covers six research members, source
checks, independent judging and the response report. No swarm has been launched by this
preparation. The selected model for a future run is `deepseek/deepseek-v4.1-flash` at
maximum reasoning effort.

## Exact target

Let $G_n$ be uniformly random $d$-regular with fixed $d\ge3$, $A_n$ its adjacency and
$T_n$ a set of $\Delta$ distinct vertices with $\Delta$ fixed. Adding one vertex adjacent
exactly to $T_n$ gives the exact spectrum factor

$$p_{G_n}(\lambda)\left(\lambda+\mathbf1_{T_n}^T(A_n-\lambda I)^{-1}\mathbf1_{T_n}\right).$$

Here $\lambda$ belongs to an interval strictly inside
$(2\sqrt{d-1},d)\cup(d,\infty)$. Symbolically define $R_n(\lambda)$ only where
$A_n-\lambda I$ is invertible, and account explicitly for host eigenvalues.

The candidate resolvent statement is

$$\mathbf1_T^T(A_n-\lambda I)^{-1}\mathbf1_T\longrightarrow-\Delta G_d(\lambda),$$

using the full Kesten-McKay Stieltjes transform. It is not the one-sided tree branch.
The earlier dossier asks for this convergence in probability, ultimately uniformly on
compact spectral intervals. A first proof at one fixed $\lambda$ would be genuine
progress, but an expectation limit alone does not establish the eigenvalue limits.

The desired fixed-point law is $\lambda=\Delta G_d(\lambda)$. The proposed threshold
$\Delta>2(d-2)$ and the proposed limiting top two eigenvalues are conditional until the
corresponding root stability and absence of other spectral roots are proved.

## The six roles and what each must produce

1. **Local-cycle concentration.** Prove the effect of bounded local excess, including
   trees, triangles and short cycles. Distinguish a diagonal entry, an average over
   fixed $T$ and an average over random $T$. Establish whether variance vanishes,
   determines a limiting random law or creates a counterexample.
2. **Source applicability.** Read the precise theorem statements, not just abstracts.
   Either derive the target from published work with every hypothesis checked or record
   the exact mismatch that prevents the import. Cover later relevant literature too.
3. **Nonbacktracking exterior expansion.** Prove summability and tail estimates for
   real $\lambda$ above the tree bulk. Then address random configuration cycles and
   concentration. A path sum on a tree is only the deterministic base case.
4. **Local-law boundary extension.** Identify the specific excluded domain and which
   estimate fails there. Obtain a valid exterior case from the proof machinery or give
   a precise counterargument. Do not simply take $\eta$ to zero in a bulk theorem.
5. **Eigenvalue reduction.** Prove the root-location consequences from the weakest
   adequate resolvent input. Resolve host Perron poles, invertibility, local
   neighbourhoods of $d$, uniformity in $\lambda$, and the two possible orderings of
   the limiting eigenvalues.
6. **Adversarial verifier.** Check all strong claims against local graphs, source
   hypotheses and a corrected model of numerical randomness. Preserve executable
   counterexamples and review the final theorem line by line where feasible.

## Gate decisions

### Gate A: is the target correct?

Within the first 45 minutes of swarm work, every direction must distinguish its needed
random limit from expectation and from averaging over vertices. Continue proving the
fixed-set hypothesis only if there is a feasible argument whose finite local pattern
terms are controlled. If it is false, replace it with a correct weaker statement rather
than re-labelling numerical agreement as concentration.

**Pass:** a precise surviving hypothesis and an actionable proof or import route.

**Replace:** a rigorous counterexample or a demonstrated loophole, with a corrected
fixed-set, random-set, averaged-set or growing-set target.

### Gate B: is a real proof route available?

Within 90 minutes, at least one route must have a complete reduction to a named estimate.
The estimate's domain, model and probability statement must be explicit. If no such
route exists, stop general exploration and concentrate on the strongest delimited
result and the exact obstruction.

**Pass:** a written reduction with no uncharacterised step called standard concentration.

**Fallback:** retain only results meeting the lower evidence tiers below. An unfinished
collection of plausible calculations is not a successful proof attempt.

### Gate C: independent acceptance

The last 45 minutes are reserved for review. Every accepted claim must have a named
reviewer, a checked statement and an explicit boundary. New exploratory work stops.
No result receives the word breakthrough without a theorem-level deliverable.

## Exact evidence required for success

### Tier 1: a fixed-degree limit theorem

This is the primary mathematical success. All of these are required:

1. **A complete theorem.** It states $d$, the random graph ensemble, the vertex sets,
   the spectral domain, what converges and in what stochastic sense. Fixed vertex sets
   may not silently be replaced by uniformly random ones.
2. **A valid resolvent proof.** It establishes the limit, not only expectation or local
   weak convergence. Bounded local cycles, off-diagonal terms and their variances must
   be controlled. Any uniformity claimed over a compact interval must have its own
   argument, such as equicontinuity or monotonicity with endpoint control.
3. **Checked imported inputs.** Every external theorem is cited with version and theorem
   number. The report explicitly verifies that fixed versus growing degree, graph
   ensemble and complex versus limiting real energy match what is asserted.
4. **A valid root argument.** Finite roots are related to candidate limits despite host
   poles. Any asserted top-one or top-two eigenvalue limit has the corresponding
   exclusion or interlacing argument. The finite $1/n$ correction is optional and
   cannot be claimed merely by neglecting higher terms.
5. **Adversarial validation.** At least one independent reviewer checks the proof's
   central estimate. Discriminating examples, scripts and raw outputs are preserved.
   Numerical checks corroborate rather than substitute for the proof.
6. **Honest novelty boundary.** If an existing theorem already gives the statement,
   report that resolution with its exact citation and scope, not a new-result claim.

A Lean file is not mandatory. If formal verification is claimed, the Lean build must
pass, the statement must be checked against the mathematical target and there must be
no `sorry` or unacknowledged nonstandard axiom.

### Tier 2: a substantial but limited theorem

This qualifies if it proves at least one of the following with the same proof and
source standards as Tier 1:

- a genuine growing-degree result, with degree and spectral scaling stated, not a
  fixed-degree claim disguised by taking $d$ large after the limit,
- a fixed-energy result at some fixed $d\ge3$ sufficiently strong to locate the
  prospective defect eigenvalue,
- a rigorously delimited averaged or random-vertex result that does not claim control
  for every deterministic finite set,
- a complete conditional root theorem with one precisely stated resolvent lemma whose
  proof is still missing and with no numerical step hidden in the implication.

The report must say immediately whether $d$ is fixed or growing, whether $T$ is fixed
or random, and exactly what remains unproved.

### Tier 3: a rigorous negative result or corrected target

This qualifies if it demonstrates a material restriction on the initial programme:

- a proof that the proposed deterministic resolvent limit is false, or
- a corrected limit with a proved bounded-local-pattern contribution, or
- a reduction to a precise necessary lemma with the previously attempted implications
  isolated and the corrected target stated.

A numeric sample with a few percent fluctuation is not a disproof. A finite numerical
counterexample is effective only when exactly checked and shown to address the limit
claim, not merely a finite-size effect.

### Report-only completion

If neither theorem nor rigorous delimitation is achieved, close honestly. Such a report
must identify the strongest attempted reduction, the exact missing analytic estimate,
all failed routes and the next feasible test. This can complete the assessment batch,
but it is not a mathematical breakthrough and must not be described as one.

## What explicitly does not count as success

- another eight-topic research map or a large collection of dossier files,
- eigenvalue delocalization or empirical spectral measure convergence alone,
- treating tree local weak convergence as a substitute for a probabilistic resolvent proof,
- averaging over $T$ while claiming a theorem for deterministic fixed $T$,
- importing a bulk complex-$z$ estimate without a valid passage to real exterior energy,
- experiments using a noncertified sampler described as proofs about the uniform model,
- an unfinished proof containing a lemma equivalent to the original target,
- a swarm verdict without coordinator review and source applicability checks.

## Prepared files

- [Source baseline and exact theorem cautions](source-baseline.md).
- [Exact source PDFs and extracted text](sources/).
- [Future member task](launch-task.md).
- Queue file `.orchestrator/queue/050-finite-defect-resolvent.md`, pending with budget
  10,800 seconds.

The final artifact for the eventual batch is `results/050-finite-defect.md`. It does not
exist until the work has actually been performed and reviewed.
