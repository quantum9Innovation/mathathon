# Finite attachment and arrow components, revision 2

Frozen November 15, 2026. This revision preserves all six Lean files from [revision 1](README-v1.md) byte for byte and adds [ArrowSchur.lean](source-v2/ArrowSchur.lean). It contains 57 current-round checked declarations, consisting of the previous 48 and nine additional finite arrow declarations. There are also 16 unchanged declarations reused from the earlier growing-defects round. The total is 73. Do not add the two revision totals.

The [manifest](SOURCE_MANIFEST-v2.json) binds the complete source packet and both paper targets. The [receipt](validation-v2/CHECK.json) records the fresh replay. The first source revision, its manifest, its validator, its receipt, and README-v1 remain unchanged.

The full attachment, inverse construction, cancellation eigenspace, and K1,7 scope is described in README-v1. That scope is unchanged. The addition supports Section 4 of [collective-self-energy-v1](../probability/collective-self-energy-v1.md), SHA256 `a3c6b1b42bed9f7f3c7c5d45c1292df5a207951e709e318db24f6f711c9d9d4d`.

## Actual finite Schur quadratic

The source defines the real symmetric arrow matrix

\[
H=\begin{pmatrix}a&b^\top\\b&\operatorname{diag}(w)\end{pmatrix}
\]

on a distinguished coordinate plus an arbitrary finite leaf set. It constructs the diagonal matrix R(z) with entries 1/(z-w_i), and proves both inverse products against zI-diag(w), assuming every denominator is nonzero.

For the actual vector v=(1,R(z)b), it proves

\[
z\|v\|^2-v^\top Hv
=z-a-\sum_i\frac{b_i^2}{z-w_i}.
\]

This is a finite matrix identity with a constructed inverse and vector. It is not merely a scalar formula imposed as a hypothesis. The source does not deduce a random eigenvalue or an inertia theorem from this identity.

## Sign of the corrected leading coupling

On coordinates consisting of a collective coordinate, one distinguished pair coordinate, and an arbitrary finite set of other pair coordinates, the source defines

\[
S_0=\operatorname{diag}(-\kappa,w_0,w_1,\ldots),
\]

and S1 with entries kappa between the collective coordinate and each pair coordinate. Let e0 be the collective coordinate vector, and let a have value minus one on each nondistinguished pair coordinate and zero elsewhere. The source proves exactly

\[
S_1e_0+(S_0+\kappa I)a
=(0,\kappa,-w_1,-w_2,\ldots).
\]

It also defines the actual coordinate projection Q=I-e0 e0 transpose and checks that projecting the left side gives the same vector. This verifies the finite cancellation responsible for the coefficient minus w_j instead of kappa at a nondistinguished pair.

The code does not prove the asymptotic expansions of the graph's collective vector or matrix. It does not formally identify these finite S0, S1, and a as derivatives of the full m-dependent graph model. The positive collective direction and other directions that do not enter this leading column are omitted from this finite coordinate calculation. Their decoupling and complementary gap remain paper steps.

## Complementary correction and combined finite sum

For the actual pair diagonal matrix D=diag(w0,w1,...), let b0=(kappa,-w1,...). The code proves

\[
b_0^\top R(-\kappa)b_0
=-\frac{\kappa^2}{\kappa+w_0}
-\sum_j\frac{w_j^2}{\kappa+w_j}.
\]

The inverse interpretation uses the nonzero denominator hypotheses from the inverse theorems. At w0=kappa, and with nonzero kappa and every kappa+w_j nonzero, it proves the combined identity

\[
\sum_i w_i+b_0^\top R(-\kappa)b_0
=\sum_i\frac{\kappa w_i}{\kappa+w_i},
\]

where the sum includes the distinguished weight kappa. Thus the bounded-weight expression arises from an actual finite inverse quadratic and its coupling vector. The code does not prove convergence of compensated infinite sums or a probability law.

## Added declarations

All nine new names have namespace `StructuralDefects`.

| Declaration | Exact content |
| --- | --- |
| `diagonal_resolvent_right` | Constructed right inverse of the shifted finite diagonal matrix |
| `diagonal_resolvent_left` | Constructed left inverse |
| `diagonal_resolvent_quadratic` | Exact finite inverse quadratic |
| `arrowMatrix_symmetric` | Symmetry of the actual arrow matrix |
| `arrow_schur_witness` | Schur quadratic for the actual reconstructed vector |
| `leading_projected_column` | Exact first-order algebraic column with the corrected signs |
| `leading_column_projection` | The actual coordinate projection preserves that column |
| `leading_pair_self_energy` | Exact complementary pair quadratic |
| `finite_screened_correction` | Combined finite sum with weights kappa w/(kappa+w) |

Every declaration has a printed axiom list. The full revision uses only `propext`, `Classical.choice`, and `Quot.sound`, with no placeholder proofs, custom axioms, or native computation certificates.

## Replay and remaining scope

From the workspace root:

```text
python3 mathathon/spectral-gap/structural-defects-round-01/formalization/validate-v2.py
```

The compiler, dependency revisions, and bounded source-only procedure are the same as in revision 1. Each source has two threads, a 4096 MB memory limit, and a 120-second timeout. The validator verifies hashes and pinned dependency revisions, rejects warnings, compiles into fresh temporary outputs, and checks the full axiom inventory. Copy the directory to a temporary location before an independent replay to preserve the retained receipt.

All general graph bridges listed in README-v1 remain unformalized. In addition, the finite-to-asymptotic arrow expansion, its uniform remainder, the actual graph complementary gap, cutoff-resolvent comparison, joint Poisson coupling, compensated infinite sums, and the next-scale eigenvalue and eigenvector theorem remain paper arguments. This is finite supporting verification, not an end-to-end formalization of the retuned resonance law.

Exposure is unchanged from revision 1, with the additional reading of the frozen collective self-energy proof before coding these nine declarations. That exposure is disclosed and is not independent review of that probability proof.
