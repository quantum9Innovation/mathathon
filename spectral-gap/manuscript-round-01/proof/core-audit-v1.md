# Fresh reconstruction of the three starting proofs

Task: SG-M1. Sender: proof investigator. Intended recipient: problem 21 integrator. Frozen revision: 1, November 14, 2026 Pacific.

## Outcome and exposure

The three specified mathematical statements are supported by direct reconstruction. No counterexample or unsupported load-bearing inference was found. The mixed-product proof admits an exact factorial correction and an optimal universal prefactor $\sqrt e$, improving its earlier $e$ prefactor. A separate note makes the critical-scale error constant explicit.

This is a fresh reconstruction, not a blind audit. The inherited context included the claim ledger and reported earlier review outcomes. No earlier review files were read for this reconstruction. The three proof inputs and local primary-source formulas were inspected directly. The earlier exact-check program was inspected for its scope after the first analytic reconstruction, but its output was not used as evidence here. A new exact checker supplies the finite corroboration listed below.

## Frozen inputs

| Input | SHA256 |
| --- | --- |
| inputs/permutation-proof-v2.md | a660dae8d97b5b9d0bb17cbfa6122518d488c48464804fda1ee0b1e7184c85af |
| inputs/sharp-scaling-v2.md | 4eefcef438bbac40639e2324076bd9c0bf96dc50600acf8b75f2152529a38a4e |
| inputs/critical-scale-v1.md | ea79cdd43ae88afcc2ca5008e4c4a95e50e12b37ca87904db25ce7cdad0b5596 |

The fourth input, source-findings-v2.md, has SHA256 75b8db08e453eaf67a98021c4404febc910d1c34fa0ace3e59b68af78c527be8. The earlier reviews are not part of this input table.

## 1. Mixed-product estimate, SG-02

The compatible-set conditioning is correct. A compatible set of $r$ arrows has probability $1/(n)_r$ and leaves a uniform permutation on exactly $n-r$ rows and columns. A good singleton has a row and column disjoint from every other requested cell of its color, so it always survives any compatible prescribed subset of the other cells.

The collision identity $Z_uZ_v=-Z_u-Z_v-1$ is exact. After removing either collided entry, the remaining entries have distinct rows and columns. Thus each shorter expectation really is the same $\mu_{j-1}$ by relabeling. This justifies the positive recurrence without a conditional independence assumption.

The recurrence supersolution is valid. The original sentence deriving the first induction step from (P4) is compressed, but the needed inequality is true:

$$\frac r{n-r}\le\frac{a-1}{n-a+1}\le\beta_{n,a}.$$

The case $r=n,h=0$ uses only $\mu_0=1$, so it does not require a positive-size remaining matrix. The sharper proof now states this boundary explicitly.

The affine coefficients are nonnegative for $n\ge2$. Under $a\ge2$ and $a\le n$, this restriction follows automatically. The separate one-cell treatment covers $n=1$. The global factorial estimate across colors is sound, and the proof never multiplies an uncontrolled universal constant once per color.

### SG-M1-R1: exact depletion correction

Status: supported refinement, not an error in the frozen input.

The selected compatible subset has at most $a-h$ entries. Monotonicity and factorial merging give

$$\prod_c\frac{n^{r_c}}{(n)_{r_c}}\le\frac{n^{a-h}}{(n)_{a-h}}.$$

Use this exact factor instead of the earlier coarser exponential correction. Resolution: `permutation-proof-v3.md`, equations (V3.6) and (V3.7).

### SG-M1-R2: sharp universal prefactor

Status: supported refinement, not an error in the frozen input.

For every repeated centered cell, the affine weight is at most $1-1/n$, so the earlier factor $\exp(a/n)$ can be removed. Together with SG-M1-R1 this gives

$$|\mathbb E P|\le2^bn^{-a}\beta^h\frac{n^{a-h}}{(n)_{a-h}}.$$

If $a^2\le n$, the remaining factor is below $\sqrt e$. A family of compatible uncentered products with $n=a^2$ approaches $\sqrt e$, so the universal constant is optimal for the arbitrary mixed-product class. Resolution: `permutation-proof-v3.md`, Sections 5 and 6.

### Source application

The local primary source `snapshot/reading-sources/friedman-second-eigenvalue-lifts/source/catane-arxiv.tex`, Proposition labelled leM:exppath, explicitly orients each base edge and assigns an independent uniform permutation to it. The map to the color formulation preserves distinct-cell multiplicities and the consistency condition. The source's $a_1$ equals $h$. Since $a\le k\le\sqrt n$, $2\sqrt a\le3k$, as needed.

In `snapshot/reading-sources/biregular-spectral-gap/source/expectation_bounds.tex`, the lemma labelled expectation_bound explicitly writes the matching matrix with an off-diagonal permutation block on $|E|=nd_1=md_2$ half-edges. Same-side factors vanish. Reorienting each remaining pair gives the same moment model with dimension $|E|$. No claim about all later circuit bounds follows from this identification alone.

These source files were inspected, not earlier source summaries. Current publication metadata and broader priority are assigned to the source investigator.

## 2. Cubic threshold, SG-04

Starting from the unconditioned row-sum identity reproduces

$$a_k=\frac{2(k-1)}{N(N-k+1)}a_{k-1}
+\frac{k-1}{N^2(N-k+1)}a_{k-2}.$$

Substituting the stated even and odd leading terms gives (S7) and (S8), with the stated initial values. The zero-order error variable in the even summation is merely an auxiliary seed, not an undefined moment ratio. The term involving $E_1$ in the odd recurrence has zero coefficient at $m=1$ and is properly omitted.

The even polynomial follows by summing the positive forcing term. The odd polynomial satisfies the displayed weighted recurrence exactly. Its comparison with $2(2m+1)^3/27$ is positive for all $m\ge1$. This validates the lower bound throughout $2\le k\le N$, including $k=N$.

For the upper bound, $2k\le N$ guarantees every denominator is at least $N/2$. The nonnegative coefficient sums bound the running maximum by the rational product in Section 6. The exponential estimate follows from $\log(1+x)\le x$ and $\sum_{j=2}^k j^2\le k^3$. Both implications in relative convergence and bounded comparability are valid. A bounded $k_N^3/N$ forces $2k_N\le N$ eventually, so there is no hidden range gap.

No correction is required. No recurrence or normalized recurrence is treated as a new result.

## 3. Critical-scale transition, SG-05

The paired recurrence is algebraically correct, including $e_0=o_0=1$ and the fact that the coefficient of $o_0$ vanishes at the first step. The coefficient inequalities in (C7) follow under $N\ge4M+2$.

The functions $E_N$ and $O_N$ satisfy the displayed differential identities exactly. Their power series in $x^3/N$ are analytic at zero, despite the apparent $1/x$ in the second differential equation. This gives the uniform derivative bounds, including the endpoint.

The even residual decomposition is exact. Its largest discarded term is proportional to $m^4/N^2$, which is at most $T m/N$ on the stated range. The odd residual uses an exact identity with coefficient $-3/[m(2m+1)]$. Multiplying this by $E_m-O_m=O_T(m^3/N)$ gives the required $O_T(m/N)$ residual. This includes the first step.

The odd error depends on the current even error. Substituting the even recurrence before taking the maximum gives the stated product of coefficient sums. The factor multiplying the local even residual is at most two. Thus the error propagation estimate is valid. The bounds $\sum m^2\le M^3$ and $\sum m\le M^2$ hold for every integer $M\ge1$.

The fixed-critical-parameter limits follow because $M^2/N\to0$. In the small-error regime with $k\to\infty$, the residual bound is smaller than $k^3/N$ by a factor of order $1/k$. This proves the two constants $2/9$ and $2/27$, and the optimality of the universal lower-bound constant $2/27$. No parity-independent limit is claimed when the parameter is positive.

### SG-M1-R3: an explicit uniform constant

Status: supported refinement, not an error in the frozen input.

`critical-constants-v1.md` supplies one fully explicit choice

$$C_T=81(1+T)\left(2+6\alpha+\frac32\alpha^2T\right)
 e^{16T+\sqrt{\alpha T}},\qquad\alpha=32/9.$$

It follows by coefficientwise derivative bounds and explicit residual estimates. The constant is generous and does not improve the convergence rate. This new note requires independent review before promotion.

## 4. Executed corroboration

The new `check_core.py` completed successfully and wrote `core-checks-v1.json`.

| Check | Exact finite cases |
| --- | ---: |
| Depleted recurrence versus direct subset expansion | 6544 |
| Improved repeated-cell affine inequality | 3969 |
| Factorial correction merging | 47904 |
| Original scaling lower bounds | 12720 |
| Rational upper-product estimate | 6241 |
| Total | 77378 |

All arithmetic is rational. The moment identity checks cover $1\le n\le32$ and all compatible depletion and order values, including zero-size residual blocks. Lower-bound checks cover $2\le N\le160$ and every $2\le k\le N$. These are corroboration, not a substitute for the written uniform proofs. No kernel verification has been performed.

## 5. Proposed integration and remaining limits

Retain the supported status of SG-02, SG-04, and SG-05 at their frozen input revisions. Add the sharper mixed-product theorem only after a second reviewer checks revision 3. The explicit critical-scale constant can be placed in an appendix or retained as supporting evidence, depending on manuscript readability.

No defective claim in the assigned inputs was found, so no new issue-registry entry is requested. Priority of the strengthened prefactor, full mixed estimate, threshold, and critical functions remains a separate literature question. The finite checks do not establish broader trace estimates or a new spectral-gap theorem.

Requested next action: the integrator should audit `permutation-proof-v3.md` and decide whether the explicit constant belongs in the manuscript. This task stops after freezing these outputs. A new assigned extension review can proceed separately without changing these bytes.
