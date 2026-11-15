# Finite subspaces and resonance components

November 15, 2026, America/Los_Angeles.

The frozen [source-v1](source-v1) packet contains 24 new checked declarations in three files. They verify exact dark modes of the coupled finite matrix, an invariant aggregate subspace, and concrete resonance matrices. Two unchanged source files from the preceding critical-law packet contribute 23 reused declarations. Reused declarations are not counted as new. Neither count is a count of new research results.

The [source manifest](SOURCE_MANIFEST-v1.json) and [compiler receipt](validation-v1/CHECK.json) bind the revision. The finite targets follow [the written normal form](../resonance/finite-normal-form-v1.md), whose revision hash is `59bebac4b6a96d148d48830bf27130223d6820e53e16627720fb7f2f7216eed7`.

## Actual finite matrix

The code reuses the preceding packet's actual matrix on the coordinate type

\[
\operatorname{Option}(\operatorname{Fin}q)
\ \sqcup\ (\operatorname{Fin}p\times\operatorname{Bool}).
\]

Here q counts free defect coordinates, p counts disjoint pairs and m=q+2p. The code's q is not the graph branching factor d-1. The `none` coordinate is the host mode. Each pair has two Boolean coordinates.

`coupled q p b w` has entry b between the host and every defect coordinate, with pair interaction w_k inside pair k. Its remaining entries are zero. The general exact-mode statements allow arbitrary real b and w_k. The aggregate normal form assumes all pair weights equal the same real w.

The copies of `PairModes.lean` and `CouplingError.lean` are byte-for-byte copies from `critical-law-round-01/formalization/source-v1`. Their source hashes are respectively `fdca785c3d9f59e873fac413f2c56e8161178ff230cb5101f4e76454a3f812ca` and `552925ff656fcb19c7a24e0f2e568dca14862188fbd1fa22103019c945e2e7de`. All earlier frozen packets remain unchanged.

## Exact dark modes

`ExactModes.lean` derives the actual coordinate action of the full coupled matrix.

For every pair k, its antisymmetric vector with coordinates (1,-1) and zero elsewhere is a nonzero exact eigenvector with eigenvalue -w_k. The host coupling cancels exactly.

For distinct pairs i and j with w_i=w_j, the difference of their symmetric vectors is a nonzero exact eigenvector at w_i. It has zero host coordinate and nonzero coordinates on both selected pairs. More generally, for equal pair weights w, any symmetric profile a with sum a_k=0 satisfies the eigenvector equation at w. The profile theorem allows the zero vector, while the separate symmetric-difference theorem proves nonzero eigenvectors.

These statements support the use of subspaces when pair weights coincide. They do not assert that a graph eigenvector must select one pair. The source does not prove the dimension of either dark eigenspace or a complete decomposition of the full finite space.

## Aggregate subspace and exact matrix

For q>0 and p>0, the code defines the linear embedding

\[
J(x_0,x_1,x_2)=
\left(x_0,\frac{x_1}{\sqrt q}\mathbf 1_q,
\frac{x_2}{\sqrt{2p}}\mathbf 1_{2p}\right).
\]

It proves injectivity and the exact squared Euclidean norm identity

\[
\|Jx\|_2^2=\|x\|_2^2.
\]

For alpha=b sqrt(q) and beta=b sqrt(2p), it proves the actual intertwining relation

\[
T J=J M,
\qquad
M=\begin{pmatrix}
0&\alpha&\beta\\
\alpha&0&0\\
\beta&0&w
\end{pmatrix}.
\]

The range of J is encoded as the range of an actual linear map, and the code proves that T preserves it. It also lifts every nonzero eigenvector of M to a nonzero eigenvector of the full T. The zero-pair case is outside this three-coordinate embedding and is covered by the preceding pure-star results.

The actual characteristic determinant is

\[
\det(zI-M)
=(z-w)(z^2-\alpha^2-\beta^2)-\beta^2w.
\]

For b=kappa/sqrt(q+2p), the code proves the exact normalized formula

\[
\det(zI-M)
=(z-w)(z^2-\kappa^2)
-\frac{2\kappa^2 p w}{q+2p}.
\]

## Collective basis and two-level model

The code defines the concrete orthogonal basis matrix whose columns are

\[
\frac{(1,1,0)}{\sqrt2},
\quad \frac{(1,-1,0)}{\sqrt2},
\quad (0,0,1).
\]

It proves Q transpose Q=I and the exact matrix relation

\[
MQ=Q\begin{pmatrix}
\alpha&0&\beta/\sqrt2\\
0&-\alpha&\beta/\sqrt2\\
\beta/\sqrt2&\beta/\sqrt2&w
\end{pmatrix}.
\]

Separately, it defines the actual two-level matrix

\[
L(a,\tau)=\begin{pmatrix}0&a\\a&\tau\end{pmatrix}.
\]

For nonzero a and sigma squared equal to one, it constructs a nonzero eigenvector (a,lambda_sigma), where

\[
\lambda_\sigma=
\frac{\tau+\sigma\sqrt{\tau^2+4a^2}}2.
\]

It proves the two displayed roots are distinct. At tau=0, each constructed vector has exactly half its squared norm in each of the two coordinates.

This last mass statement concerns the two coordinates of L. It is not a statement about the physical host mass of a graph eigenvector, and it is not asserted to hold exactly for the finite three-coordinate matrix. The limiting reduction from M to L, including a=kappa sqrt(p), remains in the written proof rather than the formal source.

## New theorem inventory

All new declarations have namespace `CriticalSubspaces`.

| File | Theorem | Content |
| --- | --- | --- |
| ExactModes | coupled_host | Actual host coordinate action |
| ExactModes | coupled_free | Actual free-coordinate action |
| ExactModes | coupled_pair | Actual pair-coordinate action |
| ExactModes | removedCoupling_pairVector | Exact host leakage of a signed pair vector |
| ExactModes | coupled_pairVector_action | Full signed pair action including leakage |
| ExactModes | antisymmetric_pair_hasEigenvector | Exact nonzero antisymmetric mode |
| ExactModes | symmetricDifference_hasEigenvector | Exact nonzero difference for equal-weight pairs |
| ExactModes | symmetricDifference_zero_host | The symmetric difference has zero host coordinate |
| ExactModes | symmetricProfile_dark | Every zero-sum symmetric profile obeys the dark eigenvector equation |
| AggregateBlock | brightMatrix_action | Actual three-coordinate matrix action |
| AggregateBlock | aggregateVector_injective | Normalized embedding is injective |
| AggregateBlock | aggregateVector_squaredNorm | Embedding preserves squared Euclidean norm |
| AggregateBlock | aggregateVector_intertwines | Actual full-matrix intertwining identity |
| AggregateBlock | coupled_preserves_aggregate_range | The actual linear-map range is invariant |
| AggregateBlock | aggregate_eigenvector_lift | Nonzero aggregate eigenvectors lift to the full matrix |
| AggregateBlock | brightMatrix_characteristic | Exact characteristic determinant |
| ResonanceBlock | collectiveBasis_orthogonal | The concrete collective basis matrix is orthogonal |
| ResonanceBlock | collectiveBasis_intertwines | Exact collective-coordinate matrix action |
| ResonanceBlock | normalized_bright_characteristic | Exact normalized characteristic determinant |
| ResonanceBlock | twoLevel_characteristic | Actual two-level characteristic determinant |
| ResonanceBlock | twoLevelRoot_equation | Displayed roots satisfy the quadratic equation |
| ResonanceBlock | twoLevelRoot_hasEigenvector | Explicit nonzero eigenvectors for both displayed roots |
| ResonanceBlock | twoLevelRoots_distinct | The two roots are distinct when a is nonzero |
| ResonanceBlock | twoLevel_resonant_masses | Equal squared coordinate fractions at zero detuning |

Every new and reused declaration is printed with `#print axioms`. All recorded lists contain only `propext`, `Classical.choice` and `Quot.sound`. There are no placeholder proofs, custom axioms or native computation certificates.

## Replay

From the workspace root, run:

```text
python3 mathathon/spectral-gap/critical-subspaces-round-01/formalization/validate.py
```

The pinned compiler is Lean 4.31.0, with mathlib revision `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The wrapper checks every source hash and every pinned dependency checkout revision. The existing compiled dependency cache is read without modifying its sources or build outputs. There is no network step or dependency build.

The two reused files and three new files are compiled in dependency order. Each compilation has two threads, a 4096 MB memory bound and a 120-second timeout. All files must compile without warnings, and every theorem's axiom list must pass the allowed-list check. Compiled outputs are temporary. The retained logs and receipt distinguish 24 new declarations from 23 reused declarations.

The receipt records manifest, validator, compiler and source hashes. Any previous success receipt is removed before replay begins. The `--lean` and `--packages-root` options permit another local copy of the same pinned dependencies. A reviewer can copy this formalization directory to a temporary location and execute the copied validator, preserving this packet's receipt.

The installed compiler and cached dependency objects remain trusted inputs. Dependency source revision checks do not cryptographically verify every compiled dependency object. The dependency tree was not rebuilt.

## Unformalized application bridges

- A complete orthogonal decomposition, dark-space dimensions and full eigenvalue multiplicities of the coupled finite matrix.
- The asymptotic reduction from the exact three-coordinate block to the two-level matrix and its error bound.
- The characteristic-root expansions and all next-scale resonance limits.
- The critical graph event, pair counts, disjointness and the integer-distance phase.
- Identification of the graph Schur operator with the finite star and pair model at the required precision.
- Uniform graph remainder bounds strong enough to determine resonance-scale mixing.
- Spectral projector perturbation estimates, rank stability and the graph subspace approximation theorem.
- Host resolvent reconstruction, normalization and spatial mass or localization statements for actual graph eigenvectors.
- Random selection of a basis inside a repeated limiting eigenspace.
- Probability limits and historical novelty.

These are finite supporting components. They do not establish the random-graph subspace theorem or identify a random resonance basis from end to end.
