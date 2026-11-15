# Finite components for the close-pair transition

November 15, 2026, America/Los_Angeles.

The frozen [source-v1](source-v1) packet contains 20 new checked theorem declarations. They support finite sampling, the far-row stationary correction, the symmetric pair test, and a concrete augmented Rayleigh witness. They are separate from the 27 declarations in the previous growing-defects packet. Neither declaration count is a count of new research results.

[Source manifest](SOURCE_MANIFEST-v1.json) and [compiler receipt](validation-v1/CHECK.json) bind the exact revision. All prior frozen source files remain unchanged.

## Exact finite sampling

`FiniteSampling.lean` works with the actual collection of all m-element subsets of `Fin n`. For each distinct ordered pair, it counts the subsets containing both coordinates. The count is

\[
\binom{n-2}{m-2}.
\]

Summing these incidences and dividing by the actual number of m-element subsets gives, for 2<=m<=n and any real kernel K,

\[
\frac1{\binom nm}\sum_{|S|=m}\sum_{i,j\in S,\ i\ne j}K_{ij}^2
=\frac{m(m-1)}{n(n-1)}\sum_{i\ne j}K_{ij}^2.
\]

The code proves the more general identity for arbitrary real pair weights before specializing to squares. It does not assume the pair-inclusion probability. The formulas for m=0 and m=1 are outside the stated formal theorem.

This is the deterministic finite average needed by equation (4.1) of [the nonbacktracking upper proof](../root/nonbacktracking-upper-v1.md). Passing from this average over subsets to predetermined labels in a random graph requires the separate graph-law exchangeability argument. No random graph distribution or probability measure is encoded in this file.

## Far-row stationary correction

`FarRowBound.lean` defines the actual n by n constant matrix P with entries 1/n. Given real matrices satisfying

\[
R=T-\alpha P+W,
\qquad T_{cj}=0\text{ for }j\in S,
\]

it proves for n positive and an arbitrary finite coordinate set S that

\[
\sum_{j\in S}R_{cj}^2
\le 2\sum_jW_{cj}^2+\frac{2\alpha^2}{n}.
\]

This matches equation (13) of [the Chebyshev proof](../probability/chebyshev-proof-v1.md). The code derives the cardinality correction and finite row sum bound. It does not identify T with a graph polynomial, prove finite propagation, or establish the approximation error W.

## Symmetric pair and augmented witness

`PairWitness.lean` defines y=e_a+e_b using actual coordinate vectors, with distinct a and b. It proves that y is nonzero and has squared norm two. For

\[
F=2zI-z^2G+H,
\]

with symmetric cross entries of G and zero H entries on the selected pair, its Rayleigh quotient is exactly

\[
\frac{y^\top Fy}{y^\top y}
=2z-\frac{z^2}{2}(G_{aa}+G_{bb})-z^2G_{ab}.
\]

The formal statement only needs equality of the two selected cross entries, not a hidden global symmetry premise. It then proves the upper bound 2z-z^2g-z^2gt from the three lower bounds G_aa>=g, G_bb>=g and G_ab>=gt. A negative scalar upper bound yields a negative quadratic form. These are the finite equations in Section 2.2 of [the close-pair obstruction](../obstruction/proof-v1.md).

`SchurWitness.lean` defines the actual augmented matrix

\[
\mathcal A=\begin{pmatrix}A&B\\B^\top&0\end{pmatrix}.
\]

For an invertible zI-A, it constructs

\[
x=(zI-A)^{-1}By,\qquad v=(x,y),
\]

and proves the exact identity

\[
z\|v\|^2-v^\top\mathcal Av
=y^\top\bigl(zI-B^\top(zI-A)^{-1}B\bigr)y.
\]

If the right side is negative, the constructed v is nonzero and satisfies z||v||^2<v^top A_aug v. The final theorem uses an actual inverse under its invertibility assumption. It does not merely assume that an unspecified vector solves the desired eigenvalue equation.

The identification of this full Schur matrix with the pair-test matrix F is not encoded in this packet. The final largest-eigenvalue conclusion additionally uses symmetry of the host and the variational principle, which are applied in the written proof rather than proved here.

## Exact theorem list

Every declaration has namespace `ClosePair`.

| File | Theorem | Content |
| --- | --- | --- |
| FiniteSampling | pair_membership_count | Exact subset incidence count for a distinct ordered pair |
| FiniteSampling | sum_offDiag_as_indicator | Exact indicator representation over the ambient off-diagonal pairs |
| FiniteSampling | sum_subset_offDiag | Double-counted weighted off-diagonal sum |
| FiniteSampling | choose_pair_ratio | Exact real binomial ratio |
| FiniteSampling | uniform_subset_offDiag_average | General finite weighted averaging identity |
| FiniteSampling | uniform_subset_frobenius | Exact averaging identity for squared matrix entries |
| PairWitness | pairPlus_quadratic | Actual pair-vector quadratic form |
| PairWitness | pairPlus_norm_sq | Squared norm equals two |
| PairWitness | pairPlus_nonzero | The pair vector is nonzero |
| PairWitness | pairSchur_rayleigh | Exact normalized pair quotient |
| PairWitness | pairSchur_bound | Lower entry bounds imply the stated quotient upper bound |
| PairWitness | pairSchur_negative | Negative scalar upper bound implies a negative pair form |
| FarRowBound | far_row_entry | Exact far-entry identity including stationary subtraction |
| FarRowBound | far_row_energy | Finite row energy bound including 2 alpha squared over n |
| SchurWitness | augmented_quadratic | Actual augmented matrix quadratic form |
| SchurWitness | block_norm_sq | Norm decomposition of the joined vector |
| SchurWitness | schur_witness_identity | Exact quadratic Schur identity |
| SchurWitness | negative_schur_gives_rayleigh | Negative Schur form gives a strict augmented Rayleigh inequality |
| SchurWitness | negative_schur_witness_nonzero | The constructed witness is nonzero |
| SchurWitness | actual_inverse_schur_witness | Both conclusions for the actual inverse of zI-A |

Each theorem is printed with `#print axioms`. All lists contain only `propext`, `Classical.choice` and `Quot.sound`. There are no placeholder proofs, custom axioms or native computation certificates.

## Replay

From the workspace root, run:

```text
python3 mathathon/spectral-gap/close-pair-transition-round-01/formalization/validate.py
```

The pinned compiler is Lean 4.31.0 and the mathlib revision is `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The wrapper checks source hashes and every pinned dependency checkout revision. It reads the existing dependency cache without changing its source or build files. Compiler outputs are temporary, and only logs and the validation receipt remain in this packet.

Each source compilation has two threads, a 4096 MB memory bound and a 120-second timeout. All four files must compile without warnings, and every theorem must have an axiom list containing only the three permitted standard axioms. The `--lean` and `--packages-root` options allow another locally available copy of the same pinned dependencies. There is no network step or dependency build.

The cached dependencies and installed compiler are trusted inputs. Checking their source revisions does not cryptographically verify every cached compiled object. The full dependency tree was not rebuilt in this run.

## Unproved application bridges

- Exchangeability of the labelled graph law, including any good event or distance cutoff.
- The nonbacktracking path count, second moment and graph separation probability.
- The polynomial approximation, finite propagation and associated row norm estimate.
- The tree Green kernel, universal-cover comparison and its entrywise lower bounds.
- The resolvent and Schur identification B=AE with the exact pair-test matrix.
- Host spectral bounds implying the relevant inverse exists.
- The Taylor estimates that make the scalar pair upper bound negative at the selected scale.
- The variational step identifying the largest eigenvalue of the actual symmetric augmented adjacency.
- The close-pair occurrence probabilities, critical and supercritical limits, and historical novelty.

These finite components support the written proofs. They do not give end-to-end verification of the log-free subcritical range or the close-pair transition theorem.
