# Assumptions, audit findings, and weak points

This file distinguishes **model assumptions**, **proof dependencies**, **definite local inconsistencies**, **scope limitations**, and **unresolved verification questions**. A local print error is not evidence by itself that the main theorem is false. Conversely, a repairable-looking proof sketch is not treated as a full independent verification.

## 1. Model assumptions and what they do

| Assumption | Why it is needed | Technical convenience or essential? | What breaks without it |
| --- | --- | --- | --- |
| Bipartiteness | Gives the $X$ block form, signed spectral pairs, alternating non-backtracking blocks, and degree-balance cancellations | Essential to this proof | The quadratic transfer and separate $a,b$ nullspace roots need replacement |
| Side-wise regularity | Makes the shifted Ihara-Bass matrix block scalar and gives $nd_1=md_2$ | Essential to the exact formulas | $D$ no longer has only two values, and circuit degrees no longer factor neatly |
| Simple graph, uniform conditional law | Identifies the target distribution and its biadjacency matrix as zero-one | Part of the theorem's model | The parallel-edge configuration ensemble has different local statistics. Theorem statements must specify whether conditioning occurred |
| Fixed degrees while $n\to\infty$ | Keeps all degree-dependent constants finite, gives bounded-away-from-zero simplicity probability, and controls local branching | Essential to the estimates as written | Growing degrees require new uniformity and a fresh simplicity or sparsity analysis |
| $n\leq m$ and $d_1\geq d_2$ | Orders $a\geq b$ and makes $n$ the full-row-rank target | Mostly convenience | Swap sides. The strict rank conclusion still needs unequal degrees |
| $a>b$, equivalently $d_1>d_2$, for rank | Supplies $\sqrt a>\tau$ | Essential to this argument | At $a=b$, nullspace eigenvalues have exactly the non-leading radius, so no exclusion margin is available |
| Bounded-degree configuration model | Controls factorial half-edge counts and tangle-free probabilities uniformly | Essential for the proof's constants | Many fixed-degree and polylog factors lose their meanings |
| Logarithmic $\ell$ with $c<1/32$ | Ensures local tangle-freeness, subpolynomial circuit encoding, and polynomially small remainders | Technical parameter choice | Larger neighborhoods permit overlapping cycles and much larger encodings |
| Nonzero frame eigenvalues and scalable block degrees | Separates exact frame modes from the stochastic remainder in Theorem 19 | Essential to this sufficient condition | A zero frame eigenvalue stays at zero regardless of common degree scaling |
| Code-distance positivity | Makes Janwa-Lal's bound informative | Essential for a positive result | The bound can be negative and then carries no useful distance information |
| Fixed expander sampling graph for matrix completion | Lets one deterministic discrepancy bound hold uniformly for all targets | Essential to the deterministic guarantee | Independent target-submission sampling requires a different probabilistic interpretation |
| Bounded sampled mean-square noise | Bounds observed residual norm by $2\delta\sqrt{\lvert E\rvert}$ in Theorem 25 | Directly used in the noise calculation | Arbitrary outlier noise can defeat the observed-error constraint only through additional modeling |

## 2. Imported dependencies that were not independently re-proved

1. **General Ihara-Bass determinant identity.** The paper quotes it as Theorem 1. This dossier uses the biregular block specialization and checks dimensional consistency, but does not reconstruct the general determinant proof.
2. **Bordenave's matching-product estimate.** Lemma 7 ultimately invokes Proposition 28 of that work after block reordering. This is an important external input to every norm estimate.
3. **Lemma 5's broader exploration method.** The proof cites a regular-graph tangle-free argument and adapts it. Its main bound is summarized here, not independently optimized.
4. **Proposition 18 on frame eigenvalues.** This application-level result belongs to Wan and Meila. Its exact printed block-matrix notation also needs a transpose correction.
5. **Janwa-Lal and cited regular-SBM recovery results.** These supply the code bound and comparison benchmark respectively.
6. **Expander mixing and Grothendieck comparison.** These are standard external inputs in Section 8.

This does not mean they are doubtful. It means mastery of this paper and verification of all external mathematics are different scopes.

## 3. Definite local inconsistencies found in the paper

### 3.1 Lemma 2's imaginary-root multiplicities

The paragraph immediately before Lemma 2 correctly derives multiplicity $m-r$ for $\pm i\sqrt b$ and $n-r$ for $\pm i\sqrt a$. Printed Lemma 2 instead gives $m-r$ with $\sqrt a$ and $r$ with $\sqrt b$. This conflicts both with the nullspace calculation and with the total $2|E|$ eigenvalue count. The corrected classification is derived in `06-derivations.md`.

### 3.2 Kernel and range confusion below Equation 13

The text identifies $\ker S$ and $\ker T$ with the span of the leading eigenvectors. In fact,

$$\ker S=\ker T=\{x:\text{both block means of }x\text{ are zero}\},$$

while

$$\operatorname{range}S=\operatorname{span}\{\mathbf1_\alpha,\mathbf1_{-\alpha}\}.$$

The range is two-dimensional. The kernel has codimension two. Subsequent cancellation uses $S$ acting on block-mean-zero vectors.

### 3.3 Equation 16 is off by one relative to Equation 14

Equation 14's telescoping identity has $j-1$ centered factors before $S$. Therefore the central matrix product should involve $\bar B^{(j-1)}SB^{(\ell-j)}$, not the printed $\bar B^{(j)}SB^{(\ell-j)}$. The same displayed decomposition's surrounding kernel explanation is also confused as noted above.

### 3.4 Equation 15 repeats a $j$ sum inside a fixed-$j$ object

$R_{ef}^{\ell,j}$ is defined with the fixed split family $T_{ef}^{\ell,j}$, but its first printed line contains another $\sum_{j=1}^{\ell}$ inside that object. This appears redundant and would multiply the intended term erroneously if read literally.

### 3.5 Appendix A's tree excess has reversed signs

The appendix writes $\chi=|V|-|E|+1$. Lemma 9 and all subsequent estimates use $\chi=\mathscr E-\mathscr V+1$. Trees have $\chi=0$, one independent cycle has $\chi=1$, so the appendix's sign is incompatible with the proof.

### 3.6 Non-backtracking zero is impossible in this degree regime

The introduction to Section 2.1 correctly explains that $\det D\neq0$, which excludes $\lambda=0$ for $B$. The later Figure 3 discussion mentions zero eigenvalues and black dots in the $B$ plot. This is inconsistent wording. It should not be read as a new zero-eigenvalue category for $B$.

### 3.7 Figure 5 has three linked indexing inconsistencies

The cycle blocks end at $9+6i$ for $i=0,\ldots,c$. Therefore the next edge is $10+6c$, not the drawn $10+6(c+1)$. The caption gives $10+6c$, then says $c=1$ gives $\ell=22$ although its own total length is $3+6(c+1)+1=16$. Under the same length formula, $\ell=22$ corresponds to $c=2$. These are visual and caption errors, not merely ambiguous prose.

### 3.8 Equation 34 names the wrong matrix in the event

Theorem 16 and its expectation are about $\bar B^{(\ell)}$, but the displayed event in Equation 34 uses $B^{(\ell)}$. The intended event is clear from the fraction immediately following it.

### 3.9 Proposition 18's symmetric block matrix has a transpose mismatch

For $k\neq\ell$, the intended operator is

$$\begin{pmatrix}0&L^{(kl)}\\L^{(lk)}&0\end{pmatrix}
=\begin{pmatrix}0&L^{(kl)}\\(L^{(kl)})^*&0\end{pmatrix}.$$

One printed equivalent form uses $(L^{(lk)})^*$, which is incompatible with $L^{(lk)}=(L^{(kl)})^*$ and has the wrong dimensions for the intended lower-left block.

### 3.10 Sign-vector dimensions in Theorem 24's proof

For a rank-one sign matrix $S=uv^*$, the needed objects are $u\in\{\pm1\}^n$ and $v\in\{\pm1\}^m$. The printed joint domain $\{\pm1\}^{n\times m}$ is dimensionally incorrect.

## 4. Important audit issues with the main trace computation

### 4.1 Corollary 12 is not a general weakening of Lemma 11 as printed

This is the strongest objection found to the paper's displayed computation. Let $L=\mathscr V-\mathscr R$, $a=d_1-1$, and $b=d_2-1$. Lemma 11 gives residual degree factors

$$a^{\mathscr E-L}b^{\mathscr E-\mathscr R}.$$

After cancellation, Corollary 12 uses

$$a^Lb^{\mathscr R}(d-1)^{2(\chi-1)}.$$

The first divided by the second is

$$\left(\frac ab\right)^{2\mathscr R-\mathscr E}
=\left(\frac ab\right)^{2\psi}.$$

This is not always at most a fixed universal constant independent of circuit geometry. It is signed through $\psi$.

For a particularly concrete check, take a path support with $\mathscr V=4$, $L=\mathscr R=2$, $\mathscr E=3$, and $\chi=0$. Alternating transpose legs can traverse such a path forwards and then backwards. Lemma 11 gives residual $(d_1-1)(d_2-1)$ beyond the side initial factors, while Corollary 12's packaged form supplies extra $(d_1-1)^2(d_2-1)^2/(d-1)^2$. Under $d_1>d_2$, the inequality from the lemma to the corollary has the wrong direction by $(d_1-1)/(d_2-1)$.

**Status:** Unresolved. The later estimates might be repairable by restoring the true degree factors and using a sharper two-sided imbalance estimate, but that repair has not been carried out here. Headline conclusions should therefore be reported as the paper's claims, not as independently certified by this dossier.

### 4.2 Lemma 13 is one-sided although anisotropic estimates can involve either sign

The statement gives $\psi\leq16k^2$, with no absolute value around $\psi$. Factors involving $(b/a)^\psi$ grow when $\psi$ is negative. A complete biregular audit needs either $|\psi|$ controlled, a structural reason negative $\psi$ cannot be troublesome, or a separate estimate for the true degree factors. This interacts directly with Corollary 12 rather than being an isolated prose issue.

### 4.3 Uniformity over $j$ in the final remainder sum is needed

Section 5.9 sums $j=1,\ldots,\ell$ remainder norms. Separate unquantified claims that each fixed $j$ fails with probability $o(1)$ would not automatically imply a union bound when $\ell\asymp\log n$. On a favorable reading, the proof's moment estimates have constants independent of $j$ and provide a common explicit probability bound. That uniformity should be made explicit. It is an exposition weakness, not necessarily a mathematical gap.

### 4.4 Tangle-free decomposition depends on correcting local indices first

The intended formula in `06-derivations.md`, D3, can be reconstructed after using a $j-1$ prefix and correcting the range-versus-kernel language. This audit is not claiming those typographical issues invalidate the method. It is saying the printed display alone is not a proof to copy blindly.

## 5. Application-specific limitations

### 5.1 Corollary 22's unscaled error does not follow directly from Theorem 4

Suppose Theorem 4 gives $\eta\leq\eta_0+\tilde\epsilon_n$. Deterministic substitution into Janwa-Lal gives the error

$$-\frac n{d_2}\frac{\tilde\epsilon_n}{2}(\delta_1+\delta_2)$$

outside or inside parentheses. Corollary 22 prints $-\epsilon_n$ inside the $n/d_2$-scaled bracket as if it were vanishing independent of $n$. The asymptotic theorem gives no rate ensuring $n\tilde\epsilon_n\to0$.

A correct qualitative conclusion needs a version with the actual factor $n\tilde\epsilon_n$ handled explicitly, a stronger spectral convergence rate, or a fixed-epsilon positive-distance formulation. The published corollary as written needs repair or clarified notation.

### 5.2 The $(14,9)$ code example is not a finite-size spectral certificate

At $n=216$, the idealized substitution $\eta_0=\sqrt{13}+\sqrt8$ yields distance about $4.30$ and relative distance about $0.0014218$. The rate calculation is exactly $1/63\approx0.015873$. These agree with the paper's rounded $4$ and approximately $0.0014$ and $0.016$.

However, Theorem 4 is asymptotic. No finite $n$ error bound is supplied, so the example cannot certify $\eta\leq\eta_0$ for the sampled finite graph. It is an illustration of the formula after dropping the asymptotic error, not a proof that the specific code at $n=216$ has the stated lower bound.

### 5.3 Binary versus $\mathbb F_{16}$ alphabet interpretation

Section 7 initially frames local codes as binary, then the example uses Reed-Solomon codes over $\mathbb F_{16}$ and assigns four bits per edge. Over $\mathbb F_{16}$, distance is naturally measured in symbols. Representing each symbol by four bits does not, without a separate binary concatenation analysis, preserve the same binary Hamming-distance lower bound. The arithmetic of the symbol-code example is understandable, but the text conflates the two alphabets.

### 5.4 Frame clustering is sufficient, not sharp

The paper explicitly compares the large-degree threshold from its spectral sufficient condition with the sharper cited two-block recovery condition. The loss factor $(1+\beta)/\beta$ is real and acknowledged. Theorem 19 is broad and exact-recovery oriented, not an optimal information-theoretic detection threshold.

### 5.5 Figure 6B is a multigraph, not a simple model realization

The caption says so explicitly. The visual is a configuration-model illustration before conditioning, not a sample from the simple graph ensemble. Reading it as a theorem-qualified graph would overstate what the picture shows.

### 5.6 Matrix completion is a guarantee, not exact recovery

Theorems 24 to 26 bound mean-square error in terms of $\eta$, $\gamma_2(Y)$, and noise. They do not promise exact low-rank recovery, optimal sample complexity, or robustness to arbitrary missingness or adversarial noise. Their deterministic nature applies once the observation graph is fixed and good.

## 6. Scope and verification limits of this dossier

- All paper pages and visuals were read. No visual was skipped.
- The source image data, random graph seed, sampling method, and original plotting code for Figure 3 were not supplied in the paper source archive. The plots were interpreted visually, not regenerated.
- No optional numerical checks were run. The coding arithmetic and spectral examples in the notes are direct calculations and marked as derived approximate calculations where relevant.
- The exact central quadratic and rank arguments were derived independently. The complete probabilistic proof was checked structurally and at critical algebraic transitions, not line-by-line certified against all external sources.
- The Corollary 12 compatibility issue and one-sided imbalance statement remain unresolved proof-repair questions. They must be distinguished from definite local typos whose intended corrections are obvious.
- No Lean formalization was attempted, and no claim of formal theorem verification is made.

## 7. Fair overall assessment

**Paper:** It presents a complete and influential proof architecture, an exact biregular Ihara-Bass dictionary, and three clear applications. The strongest conceptual insight is that one non-backtracking radial estimate handles adjacency upper outliers, lower positive outliers, and rank loss together.

**Derived assessment:** The spectral transfer is clean and highly reusable. The moment-proof architecture is also coherent, with well-chosen $k,\ell,g(n)$ and a clear three-regime circuit decomposition. The main unresolved reading burden is not the broad method but the exact anisotropic circuit arithmetic following Corollary 12.

**Interpretation:** The best way to learn the paper is to master the spectral map and proof architecture first, then read the circuit calculation in a repair-oriented manner. The best way to cite a specific application is to retain the asymptotic qualifiers and avoid converting figures or numerical examples into finite-size guarantees.
