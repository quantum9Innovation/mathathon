# Assumptions, limitations, and source weak points

**Label convention.** Conditions and author-stated limitations are **Paper**. Assessments, counterexamples, and repairs are **Derived**. Speculative concerns are labeled separately from demonstrated defects.

## 1. What the assumptions do

| Assumption | Why it is needed | Essential or convenient | What changes without it |
| --- | --- | --- | --- |
| Fixed finite base $B$ and $n\to\infty$ | Keeps the base Hashimoto basis, finite types, tangle constants, and algebraic coefficient formulas fixed | Essential for the stated theorem | Joint limits in $d,B,n$ are not covered |
| $d\ge3$ regular for main adjacency results | Makes $R=d-1>1$ and gives the clean Ihara quadratic | Essential for this threshold and conversion | Irregular bases retain only the weaker Section 3.1 result |
| Connected base of negative Euler characteristic in the core | Provides nontrivial covering models, $\rho(H_B)>1$, and tangle order at least one | Core proof assumption | Reducible or degenerate cases need separate treatment rather than direct use of the chapter's statements |
| No half-loops in Chapter 2 | Permits ordinary uniform permutations and factorial formulas | Technical convenience | Section 3.4 adds odd factorials, fixed points, and type memory for half-loops |
| Independent uniform permutations or algebraic variants | Produces exact algebraic expansion coefficients | Model-specific and essential to this proof | A generic cover distribution need not have factorial-like expansions |
| Strictly non-backtracking closed walks | Gives $\operatorname{Tr}(H_G^k)$ and forced beaded-path traversal | Essential for type-form simplification | Backtracking adjacency walks need a different combinatorics |
| Fixed expansion order $r$, then sufficiently large $r$ | Ensures finite types and allows error bounds independent of $k,n$ within specified ranges | Essential to the proof | Constants and type counts grow with $r$ |
| Controlled $k$ relative to $n$ | Makes falling-factorial Taylor remainders and coincidence bounds uniform | Essential technical range | Unrestricted $k,n$ uniformity is not claimed |
| Large non-real eigenvalues excluded from side-stepping | Even powers of $Q$ give signed control only for real outliers | Essential to the stated abstract lemma | Complex outliers outside the disk would require another idea |
| Pruned positive-order subgraphs for occurrence lower bounds | Forces two distinct copies to have strictly larger-order union | Essential to the first-order inclusion-exclusion | Pair interactions can spoil the simple lower bound without additional analysis |
| Absolute summability in cone decomposition | Allows infinite rearrangement and finite-support approximation | Essential to Theorem 2.4.24 | Formal inclusion-exclusion alone does not justify infinite sums |
| Ramanujan base for the fine exponent | Leaves only $\pm(d-1)$ outside the critical Hashimoto disk | Essential to the specific refinement | Extra large base eigenvalues complicate coefficient principles |
| Spreading and no small components | Excludes concentrations near $\pm(d-1)$ at the needed probability level | Essential to the Ramanujan exponent | Side-stepping alone does not prove the two-sided tangle exponent |

## 2. Scope limitations stated or evident in the paper

### Not all random-cover models

**Paper, Sections 0.2.1 and 3.4.** Contiguity results for random-cover models were much less available than for ordinary random regular graphs. The fundamental exponent can differ substantially between models, for example when permutations are restricted to full cycles.

**Derived.** Do not silently transfer either the $O(n^{-1})$ constant or $\eta_{\mathrm{fund}}$ from $\mathcal C_n(B)$ to uniform simple random covers. Algebraic expansion is the actual structural requirement used here.

### The irregular conjecture is not solved in full strength

**Paper, Sections 0.2.3, 3.1, and 3.6.** The general irregular method uses $2\sqrt{d_{\max}-1}$, which can exceed $\rho(A_{\widehat B})$ substantially. The authors note examples where the conclusion is weaker than a trivial spectral bound.

**Derived.** The universal regular theorem should not be paraphrased as a full proof of Conjecture 0.2.5 for arbitrary $B$.

### Conditional trace is not obtained

**Paper, opening of Section 2.1.** The authors explicitly state that they do not obtain the required coefficient information for the raw trace conditioned on tangle-freeness. They use expectations multiplied by an indicator instead.

**Derived.** Replacing $\mathbb E[\mathbb I_{\mathrm{TF}}X]$ by $\mathbb E[X\mid\mathrm{TF}]$ in an oral defense would change the theorem being proved.

### Constants and algorithmic effectiveness are weak

**Paper.** $C_{B,\varepsilon}$, $C_r$, $r$, and logarithmic moment constants are largely unspecified. The fundamental-order procedure is finite through algebraic separation, but no practical complexity bound is provided.

**Derived.** The theorem is not a ready-to-use finite-$n$ numerical guarantee, and the finite algorithm is not automatically an efficient computational tool.

### The two-sided Ramanujan result is local in $\varepsilon$

**Paper, Theorem 0.1.3.** The lower bound is stated at a chosen small $\varepsilon_0$, while the upper bound holds for $0<\varepsilon<\varepsilon_0$.

**Derived.** "Probability proportional to $n^{-\eta}$" means matching powers up to constants in that regime, not an asymptotic equivalent at every threshold and not convergence of rescaled probabilities to one universal constant.

## 3. Demonstrated source defects

The following are not speculative concerns. Each can be checked against the rendered PDF and a direct algebraic counterexample.

### A. Tree Euler characteristic has the wrong sign

**Paper, Definition 2.2.1 and Glossary.** A tree is defined as connected with Euler characteristic $-1$.

**Derived.** With the paper's own no-half-loop convention $\chi=|V|-|E|$, a tree has $\chi=1$ and $\operatorname{ord}=-\chi=-1$. This also agrees with Subsection 1.2.4's tree discussion. The tree definition should therefore use $\chi=1$, or order $-1$. The surrounding argument only makes consistent use of the latter order convention.

### B. Section 2.7 contains non-literal trace and parameter displays

**Paper, printed pages 102 to 103.** Equation (2.94) writes an expectation involving $H_G^k$ where $\operatorname{Tr}(H_G^k)$ is intended. The displayed new-trace coefficient formula uses one uniform-plus-sign convention even though level zero requires subtraction of the old trace. The parameter list sets $\tau_1=\tau_0^{1/2}$ despite the abstract requirement $\tau_0<\tau_1$, and the final exception threshold becomes $\tau_0^{1/2}+\varepsilon$ instead of $\tau_0+\varepsilon$.

**Derived consequence.** These displays cannot be copied literally into a valid verification. The coherent reconstruction is:

1. Use $\operatorname{Tr}(H_G^k)-\operatorname{Tr}(H_B^k)$ for the new trace.
2. Kill the level-zero principle part by subtracting the old trace, with separate handling of tangle-probability coefficients at later levels.
3. Choose $\tau_1$ as an outer spectral bound greater than $\tau_0$, for example $\rho(H_B)$ in the regular application.
4. Keep the target threshold $\tau_0+\varepsilon$ from Theorem 0.2.6.

D10 in `06-derivations.md` records this repair. This dossier does not claim that replacing those tokens alone certifies every estimate in Section 2.7.

### C. Theorem 3.3.2 uses the full radius and is false as written

**Paper, printed page 117, PDF page 124.** The upper bound states

$$
\Pr\{\rho(H_G)\ge \rho(H_B)^{1/2}+\varepsilon\}
\le C(\varepsilon)n^{-\eta_{\mathrm{fund}}(B)}
$$

for a connected $d$-regular base and sufficiently small positive $\varepsilon$.

**Direct counterexample, Derived.** Every $d$-regular cover has the old Hashimoto eigenvalue $d-1$. Whenever

$$
0<\varepsilon<d-1-\sqrt{d-1},
$$

every cover satisfies

$$
\rho(H_G)\ge d-1>\sqrt{d-1}+\varepsilon.
$$

The event on the left therefore has probability $1$, while the proposed upper bound tends to zero as $n\to\infty$. This is impossible.

**Required reading.** The proof follows the new-spectrum argument from Section 2.7, so the natural intended quantity is $\rho_B^{\mathrm{new}}(H_G)$. Proposition 3.3.1's lower bound is also insufficient for Theorem 0.1.3 if interpreted using only the full radius, since the old dominant eigenvalue already makes such an event unavoidable. These statements must be read with the new-spectrum repair, not cited as printed.

### D. Theorem 3.3.4 has a direct bouquet counterexample

**Paper, printed pages 119 to 120, PDF pages 126 to 127.** It claims $\eta_{\mathrm{fund}}(B)>\sqrt{d-1}$ for every connected $d$-regular $B$.

**Direct counterexample, Derived.** Take $B=W_2$, one vertex with two whole-loops. Then:

- $d=4$ and $\operatorname{ord}(W_2)=1$.
- Hashimoto transitions have three non-backtracking choices, so $\rho(H_{W_2})=3$.
- $3>\sqrt3$, and the identity $W_2\to W_2$ is étale.

Thus $W_2$ is itself a strict tangle of order $1$ under Definition 2.4.8, so $\eta_{\mathrm{fund}}(W_2)=1$, not greater than $\sqrt3$. The paper's own bouquet formula immediately before the theorem also gives $\eta_{\mathrm{fund}}(W_2)=m-1=1$ because the least $m$ with $2m-1>\sqrt3$ is $m=2$.

**Additional inconsistency in the proof text.** The claim that any one-vertex graph with $s+1$ whole-loop edges has Hashimoto radius $s$ is not valid for whole-loop bouquets. For example $W_2$ corresponds to $s=1$ but has radius $3$. The intended extremal statement requires feasible graphs and the half-loop extremizer, not the displayed universal assertion.

**Assessment.** The universal growth inequality must be discarded unless a different definition or additional restriction is supplied. This does not negate the computable exponent or the main $O(n^{-1})$ theorem, but it invalidates the abstract's ancillary assertion when read literally.

### E. The algorithm's initial upper-bound sentence also conflicts with the same example

**Paper, Proposition 3.3.3's proof.** It says $\eta_{\mathrm{fund}}(B)\le\operatorname{ord}(B)-1$ after invoking the identity étale map.

**Derived.** The identity map directly proves only $\eta_{\mathrm{fund}}(B)\le\operatorname{ord}(B)$. With $B=W_2$, the displayed stronger claim would give $\eta_{\mathrm{fund}}\le0$, contradicting both $\eta_{\mathrm{fund}}\ge1$ and the explicit value $1$ above. The finite-search idea can still be motivated using order below $\operatorname{ord}(B)$, but the stronger sentence is defective without an extra definition or argument.

### F. Odd-$k$ weighted-convolution formulas are inconsistent

**Paper, Example 2.2.13 and the beginning of Section 3.5.** Two different closed forms are printed for the same odd-$k$ weighted convolution of $q^k$ with weights $(1,2)$.

**Direct calculation, Derived.** The defining sum over nonnegative integers gives

$$
F(k)=\sum_{j=0}^{\lfloor k/2\rfloor}q^{k-j},
$$

hence, for odd $k$,

$$
F(k)=\frac{q^{k+1}-q^{(k+1)/2}}{q-1}.
$$

At $k=1$, only $(k_1,k_2)=(1,0)$ contributes and $F(1)=q$. Example 2.2.13 yields $0$ from its odd formula, while Section 3.5 yields $q+1$ from its different formula. Both are inconsistent with the defining sum. The derived formula above and the case analysis in D5 should be used instead.

### G. Local notation slips compound the reading burden

Verified examples include:

- Theorem 2.4.7 writes the random occurrence count with second argument $B$ where the random graph $G$ is required.
- Definition 2.4.25's prose mentions an order cutoff before the formal truncation is introduced. The displayed collection itself has no $r$ restriction.
- One sentence in the certified growth discussion flips the sign of the radius exponent, while the defining certified condition uses $<R^{1/2}$.
- Some later formulas use the base Hashimoto trace where the random cover Hashimoto trace is evidently intended.

**Derived reading rule.** Prioritize displayed definitions, dimensional checks, and the surrounding logical role over isolated prose repetitions. Keep a local list of repairs rather than harmonizing the whole paper silently.

## 4. Potential mathematical concerns not established as errors

These are boundaries of this dossier, not claims that the paper is wrong:

- I did not independently verify every combinatorial estimate in Sections 2.4.5, 2.5, 2.6.4, 3.2, and 3.5 to a publication-referee standard.
- The generalized $\Omega$-type section largely verifies a checklist by analogy with earlier sections. A formal proof would require checking each adaptation and its modified constants explicitly.
- The finite fundamental-order algorithm depends on exact algebraic comparison and correct finite-search bounds. I verified the mechanism, not an implementation.
- No source compiler was run, and no Lean formalization was produced.
- No numerical experiment was used to support or refute a theorem. Small examples in this note are exact algebraic counterexamples or checks, not empirical evidence.

## 5. Fair overall assessment

**Paper's strongest durable idea.** Certified traces provide a clear structural method: an upper-set admissibility condition, finite cone decomposition, subcritical coefficient growth, and eventual recovery of true tangle-free trace expansions. The separation between expansion construction and side-stepping is also conceptually clean.

**Derived assessment.** The manuscript should be read as a research preprint with meaningful notation and statements that need repair, not as a mechanically polished proof text. The main architecture is understandable and largely reconstructible from the definitions, but several displayed claims outside its central certified-trace mechanism fail direct checks. A cautious reader can learn a great deal from the method while refusing to quote the defective formulas unchecked.

## 6. What a formal follow-up would have to settle first

1. Freeze a corrected notation sheet for $\tau_0,\tau_1,R$, full and new spectral radii, and tangle-free versus tangle-present indicators.
2. Repair Section 2.7's old-trace coefficient formulas, including level zero separately.
3. Restate Proposition 3.3.1 and Theorem 3.3.2 with the new Hashimoto radius and verify the lower-bound passage to adjacency new spectra.
4. Reconcile Definition 2.4.8 with the claimed fundamental-order inequality and the algorithm's initial bound.
5. Verify Theorem 2.4.31's growth estimates with the positive square-root threshold throughout.
6. Correct weighted-convolution closed forms against the defining sum before building mod-$S$ refinements on them.
7. Only after those repairs, attempt a complete line-by-line or formal verification of the main theorem and the fine exponent.
