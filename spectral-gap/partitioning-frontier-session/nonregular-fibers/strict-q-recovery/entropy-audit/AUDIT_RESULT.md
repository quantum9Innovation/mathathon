# Strict-weight entropy component: source audit

15 November 2026. Mathematical proof complete; no historical priority claim.

Frozen proof source: `strict-weight-entropy-gap.tex`, SHA-256
`3ad4038397fc6469344b29c0e96922dc17ab41deec48783ce0084c75748f5320`.
The PDF has eight pages. Two successful `pdflatex -halt-on-error` passes resolve the references; the final pass has no warnings or overfull boxes.

The strict hypothesis is exactly symmetry, physical-slot normalization
`Σ_j d_ij q_ij=1`, and `0<q_ij<1/2` on every active factor. No condition is imposed on absent factors. Internal weights use the same `q_ii`, with edge mass `α_i d_ii/2` and loss coefficient `1−2q_ii`. Internal degrees zero and one are covered.

Theorem 1 proves, for all compatible integer one-hot candidate laws,

\[
 \Phi\leq-\frac{9\delta^2}{2D^5C_q},\qquad
 C_q=\max\{1/q_{\min},\,2(D-1)/c_{\min}\},\quad
 c_{\min}=\min(1-2q_{ij}).
\]

This was checked by reconstructing the full chain: weighted entropy cancellation; the exact retained-law KL identity; the global bound `Σ_i α_i Σ_t κ_it≤C_q L`; the bounded one-hot variance test and Pinsker; weighted Cauchy–Schwarz; and the reversible identity `Σ_i α_i Σ_j d_ij V_j=Σ_j α_j d_j V_j`. The last expression is at least `3δ`. The comparison uses a maximum of KL coefficients, with no duplicated use of the total loss.

The zero phase is precisely a deterministic old-type map `T` satisfying `QT=TR`. The argument never requires an injective row map, distinct rows, or nonsingularity of the candidate quotient. Unused labels have zero root mass and contribute nothing; legality forces every occupied candidate row to have the old root's total degree. There is no division by a candidate class mass. The compactness corollary retains all simplex boundary faces, and the quantitative gap makes its bound uniform even for shrinking candidate classes.

Theorem 2 proves the macroscopic integer-candidate count with exponent `−c_q η² n` and explicit polynomial prefactor. Theorem 3 proves the unconditional modular solution-count moment, separately from the real variance calculation. The exact star count includes root assignments once. Internal factorials, parity constraints, zero factors, and the half-edge normalization were checked against the frozen exact-count source.

For fixed `K,D`, connected reversible integer frames form a finite family with determined positive old proportions. A rational strict-margin LP chooses weights with a uniform positive margin across this family. Thus the gap, polynomial moments, and eventual simplicity thresholds can all be uniform. Old-block lower bounds enter the pool/simplicity and support arguments; they do not enter the local gap constant.

The actual frozen support source was read in full. Its witness argument changes `2a+b=ds` to `2a+b=Σ_(v∈S)deg(v)≥3s`, retaining the excess bound `e−s−|W|≥s/2`; all remaining bounds use `D` and the old pool lower bound. Its clean-vertex integer compatibility argument does not need equal total row degrees. The independent full support and enumeration components remain part of the parent's assembled recovery theorem.

Read-source hashes are listed at the end of the proof. All writes for this task were confined to this `entropy-audit/` directory; the preceding weighted note and earlier packets remain unchanged.
