# Formal finite-matrix components for growing defects

November 15, 2026, America/Los_Angeles.

Current frozen revision: [source-v2](source-v2). It contains machine-checked finite-matrix components of the proposed collective-resonance argument. It does not formalize the random-graph theorem. [Source bindings](SOURCE_MANIFEST-v2.json) identify the exact files, and [validation receipt](validation-v2/CHECK.json) records the compiler result and all printed axiom lists.

The first revision and its receipt remain available in [source-v1](source-v1) and [validation-v1](validation-v1). Revision 2 adds an actual projected-inverse construction and keeps both earlier proof files byte-identical.

## Actual encoded objects

`CollectiveModes.lean` defines a real matrix indexed by `Option (Fin m)`. The `none` coordinate represents the retained host mode, and the `some i` coordinates represent the m defect modes. Its only nonzero entries are the coupling b between the host coordinate and each defect coordinate. This is an actual finite matrix, not an assumed action of an unspecified operator.

The bright vector has host coordinate t and all defect coordinates equal to one. When t squared equals m, matrix multiplication gives eigenvalue bt. For m positive, this vector is proved nonzero using one actual defect coordinate. Specializing

\[
b=\frac{3/\sqrt8}{\sqrt m}
\]

gives genuine eigenvectors with eigenvalues plus and minus 3/sqrt(8). Every real eigenvalue is proved to belong to the set consisting of these two values and zero. For nonzero b and positive m, the kernel is characterized exactly by a zero host coordinate and zero sum of defect coordinates.

The dimension m-1 of that kernel and the full ordered eigenvalue multiplicities are not proved in this packet. The code also does not formalize the congruence that produces this effective matrix from the original graph pencil.

`ProjectedResolvent.lean` uses actual real matrices A, P and R, and proves

\[
ARA=z^2R-zI-A+(z+d)P
\]

from the two projected inverse equations and PA=dP. It compresses this identity by an isometric marked-coordinate matrix. The selector is explicitly encoded from an embedding `Fin m` into `Fin n`. Its isometry is proved rather than assumed in the final marked statement. The stationary matrix has every entry equal to 1/n, and its compression is proved to be the m by m matrix with the same entry 1/n.

`InverseBridge.lean` closes the arbitrary-R premise at z=d. It defines

\[
M=dI-A+P,
\qquad R=M^{-1}-P,
\]

under an explicit invertibility assumption on M. From AP=PA=dP and P squared equal to P, it proves both projected inverse equations and PR=RP=0. For the actual constant stationary matrix, idempotence follows from n positive, while AP=PA=dP follows from constant row and column sums of A.

The final `actual_constructed_marked_identity` therefore proves, for actual distinct-coordinate selection E,

\[
dI_m-E^\top ARAE
=2dI_m-d^2E^\top RE+E^\top AE-2dE^\top PE,
\qquad E^\top PE=\frac1n\mathbf1_m\mathbf1_m^\top.
\]

It assumes invertibility of dI-A+P and the row and column sums. It does not assume the desired marked identity or an arbitrary resolvent identity.

## Exact theorem inventory

The namespace for all declarations is `GrowingDefects`.

| Source | Theorem | Checked content |
| --- | --- | --- |
| CollectiveModes | collectiveMatrix_none | Exact host row of matrix-vector multiplication |
| CollectiveModes | collectiveMatrix_some | Exact defect row of matrix-vector multiplication |
| CollectiveModes | brightVector_eigen | Matrix eigen-equation when t squared equals m |
| CollectiveModes | darkVector_kernel | Zero host coordinate and zero defect sum imply kernel membership |
| CollectiveModes | kernel_iff | Converse kernel characterization for positive m and nonzero coupling |
| CollectiveModes | bright_hasEigenvector | Bright vector is an actual nonzero eigenvector |
| CollectiveModes | nonzero_eigenvalue_square | Every nonzero eigenvalue satisfies mu squared equal to m b squared |
| CollectiveModes | eigenvalue_trichotomy | Excludes other real eigenvalues for the general coupling |
| CollectiveModes | effective_positive_mode | Exact positive effective eigenvector |
| CollectiveModes | effective_negative_mode | Exact negative effective eigenvector |
| CollectiveModes | effective_eigenvalue_trichotomy | Excludes other nonzero eigenvalues after normalization |
| ProjectedResolvent | projected_resolvent_polynomial | Exact ARA identity with stationary correction |
| ProjectedResolvent | marked_schur_identity | Compression by an isometric matrix E |
| ProjectedResolvent | selection_isometry | Actual distinct-coordinate selector satisfies E transpose E equal to identity |
| ProjectedResolvent | marked_stationary_matrix | Actual stationary compression is the constant 1/n matrix |
| ProjectedResolvent | stationary_mul_of_column_sum | Constant column sums imply PA=dP |
| ProjectedResolvent | actual_marked_schur_identity | Marked identity for actual selectors, conditional on projected inverse equations |
| InverseBridge | regularized_mul_projector | MP=P |
| InverseBridge | projector_mul_regularized | PM=P |
| InverseBridge | regularized_inverse_mul_projector | M inverse P=P |
| InverseBridge | projector_mul_regularized_inverse | PM inverse=P |
| InverseBridge | constructed_projected_inverse_left | The constructed R satisfies the left projected inverse equation |
| InverseBridge | constructed_projected_inverse_right | The constructed R satisfies the right projected inverse equation |
| InverseBridge | constructed_projected_inverse_centered | Both PR and RP vanish |
| InverseBridge | stationary_idempotent | The actual stationary matrix is idempotent for n positive |
| InverseBridge | mul_stationary_of_row_sum | Constant row sums imply AP=dP |
| InverseBridge | actual_constructed_marked_identity | Marked identity for the constructed centered R at z=d |

Each theorem is printed with `#print axioms`. All 27 declarations use only `propext`, `Classical.choice` and `Quot.sound`, which are the standard logical foundations of this library. There are no placeholder proofs, new axioms or native computation certificates in the source files. The theorem count includes helper identities and is not a count of new research results.

## Reproduce the check

From the workspace root, run:

```text
python3 mathathon/spectral-gap/growing-defects-round-01/formalization/validate.py
```

The validator defaults to revision 2. Pass `--revision v1` to replay the preserved first revision. The `--packages-root` and `--lean` options accept equivalent locally available pinned dependencies and compiler paths.

The checked toolchain is Lean 4.31.0. The mathlib revision is `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The remaining dependencies are pinned in each source revision's `lake-manifest.json`. The existing cache under `/home/acru/angelo/proj/sadim/lean/.lake/packages` is read only during validation. No source, package configuration or build output in that project is modified.

The validation command verifies frozen source hashes and each dependency checkout revision, then invokes the compiler directly. Each source has two threads, a 4096 MB memory limit and a 120-second timeout. Local compiled outputs live in a temporary directory under this packet and are removed afterward. The validator checks that every theorem has a printed axiom list, rejects nonstandard axioms and source placeholders, and requires a warning-free successful compiler exit.

The pinned dependencies' existing compiled caches and the installed compiler are trusted inputs. They were not rebuilt from source or independently kernel-audited in this run. Dependency revision checks are not cryptographic verification of every cached object.

## Unproved application bridges

- The actual random graph law, the host gap event and the probability of that event.
- The implication from that host gap to invertibility of dI-A+P.
- The marked resolvent estimates R1 and R2 for growing m, including all uniform probability bounds.
- The derivative expansion, shrinking spectral window and operator-norm error control.
- The full retained-host Schur congruence, its inertia relation and the ordered graph eigenvalue conclusions.
- The dimension of the dark kernel, eigenvalue multiplicities and limiting distribution of dark modes.
- Any historical novelty assertion.

The inverse construction does remove the earlier need to assume arbitrary projected inverse equations at z=d. It does not remove these analytic, probabilistic or spectral-ordering obligations.
