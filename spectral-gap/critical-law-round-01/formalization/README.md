# Finite matrix components for the critical spectral law

November 15, 2026, America/Los_Angeles.

The frozen [source-v1](source-v1) packet has 30 checked declarations implementing three finite components: the disjoint-pair spectrum, removal of exceptional star couplings, and the exact finite normalization. The count includes supporting lemmas and specializations. It is not a count of new research results. The earlier packets with 27 and 20 declarations remain separate and unchanged.

[Source manifest](SOURCE_MANIFEST-v1.json) and [compiler receipt](validation-v1/CHECK.json) bind the exact revision. No probability space, random graph, limiting point process or historical novelty claim is encoded here.

## Actual matrix model

Let q be the number of free defect coordinates and p the number of exceptional pairs, so m=q+2p. In this packet, q does not denote the graph branching factor d-1.

The coordinate type is

\[
\operatorname{Option}(\operatorname{Fin}q)
\ \sqcup\ (\operatorname{Fin}p\times\operatorname{Bool}).
\]

The `none` coordinate is the host mode. The q `some` coordinates are free defects. Each pair of Boolean coordinates is one exceptional pair.

`freeStar q b` has coupling b between the host and each free coordinate. `pairMatrix p w` has the block

\[
\begin{pmatrix}0&w_k\\w_k&0\end{pmatrix}
\]

on pair k. `decoupled q p b w` is the actual block diagonal matrix formed from these two matrices.

`removedCoupling q p b` has entries b between the host and every exceptional pair coordinate, with all other entries zero. `coupled` is the sum of `decoupled` and `removedCoupling`. Thus it is the full constant host star plus the disjoint pair blocks.

The statements allow arbitrary real b and w. Positivity of pair weights is not needed for this finite algebra.

## Spectrum and finite correction

For each pair k and real sigma with sigma squared equal to one, the code constructs an eigenvector with pair coordinates (1,sigma) and zero elsewhere. Its eigenvalue is sigma times w_k.

For q positive, it constructs a collective eigenvector with host coordinate sigma sqrt(q), all free coordinates one and all pair coordinates zero. Its eigenvalue is sigma b sqrt(q).

The coverage theorem proves that every real eigenvalue of `decoupled` belongs to

\[
\{0,b\sqrt q,-b\sqrt q\}\cup\{w_k,-w_k: k\in\operatorname{Fin}p\}.
\]

This is a coverage statement plus explicit realization of every pair mode and both collective modes. It does not prove an ordered spectrum, algebraic multiplicities or the dimension of the zero eigenspace. Zero is included as a possible eigenvalue, without asserting that it occurs for every parameter choice.

For b=kappa/sqrt(q+2p), `normalizedDecoupled` keeps the exact collective eigenvalues

\[
\pm\kappa\sqrt{\frac q{q+2p}}.
\]

The code does not replace this finite expression by its asymptotic value plus or minus kappa.

## Exact Euclidean decoupling bound

For an actual finite real vector v, `squaredNorm v` is the sum of its squared coordinates and `euclideanNorm v` is the square root of that sum. These definitions use the Euclidean norm directly, rather than the default norm on a function space.

The code proves that the restricted constant coupling vector has squared norm 2p b squared. It derives the actual action of the removed-coupling matrix D and proves, for every v,

\[
\|Dv\|_2^2\le 2pb^2\|v\|_2^2,
\qquad
\|Dv\|_2\le |b|\sqrt{2p}\|v\|_2.
\]

The proof uses the finite Cauchy-Schwarz inequality and the coordinate decomposition into host, free and paired coordinates. It does not assume an operator estimate as a premise.

The normalized statement is

\[
\|(\widehat T-\widehat T_0)v\|_2
\le |\kappa|\sqrt{\frac{2p}{q+2p}}\|v\|_2,
\]

where the two matrices are the actual `normalizedCoupled` and `normalizedDecoupled` objects. This uniform vector inequality is the finite Euclidean estimate needed by the written operator argument. The source does not additionally package it as a theorem about a continuous linear map's operator norm.

## Exact theorem list

Every declaration is in namespace `CriticalPairs`.

| File | Theorem | Content |
| --- | --- | --- |
| PairModes | pairMatrix_action | Exact action on a coordinate of an actual pair block |
| PairModes | pairVector_eigen | Explicit pair eigenvector identity |
| PairModes | pairVector_nonzero | Pair vector is nonzero |
| PairModes | freeStar_host | Host coordinate of the free star action |
| PairModes | freeStar_leaf | Free coordinate of the free star action |
| PairModes | freeBright_eigen | Explicit collective eigenvector identity |
| PairModes | decoupled_pair_eigen | Pair identity embedded into the full decoupled matrix |
| PairModes | decoupled_pair_hasEigenvector | Nonzero pair eigenvector in the standard eigenspace interface |
| PairModes | decoupled_bright_eigen | Collective identity embedded into the decoupled matrix |
| PairModes | decoupled_bright_hasEigenvector | Nonzero collective eigenvector when q is positive |
| PairModes | pair_eigenvalue_coverage | Every real pair eigenvalue equals a signed pair weight |
| PairModes | freeStar_nonzero_eigenvalue_square | Every nonzero real free-star eigenvalue has square q b squared |
| PairModes | decoupled_eigenvalue_coverage | Every real eigenvalue belongs to the displayed finite union |
| CouplingError | removedCoupling_host | Exact host action of removed couplings |
| CouplingError | removedCoupling_free | Removed couplings vanish on free coordinates |
| CouplingError | removedCoupling_pair | Exact pair-coordinate action of removed couplings |
| CouplingError | restrictedCoupling_squaredNorm | Restricted constant vector has squared norm 2p b squared |
| CouplingError | squaredNorm_split | Euclidean squared norm splits into three coordinate groups |
| CouplingError | removedCoupling_squaredNorm | Exact squared norm of the removed-coupling action |
| CouplingError | pair_sum_square_bound | Finite Cauchy-Schwarz estimate on the paired coordinates |
| CouplingError | removedCoupling_squaredNorm_bound | Uniform squared Euclidean bound for the actual matrix |
| CouplingError | removedCoupling_euclideanNorm_bound | Uniform Euclidean norm bound for the actual matrix |
| CouplingError | coupled_difference_bound | The bound for the actual coupled-minus-decoupled difference |
| NormalizedModes | normalized_collective_coefficient | Exact finite collective normalization |
| NormalizedModes | normalized_eigenvalue_coverage | Real eigenvalue coverage after normalization |
| NormalizedModes | normalized_bright_hasEigenvector | Both normalized collective modes |
| NormalizedModes | normalized_pair_hasEigenvector | Both normalized pair modes |
| NormalizedModes | normalized_restrictedCoupling_squaredNorm | Exact squared coupling mass kappa squared times 2p/m |
| NormalizedModes | normalized_error_coefficient | Exact normalized error coefficient |
| NormalizedModes | normalized_decoupling_bound | Uniform Euclidean error factor absolute kappa times sqrt(2p/m) |

Every declaration is printed with `#print axioms`. All recorded lists contain only `propext`, `Classical.choice` and `Quot.sound`. There are no placeholder proofs, custom axioms or native computation certificates.

## Replay

From the workspace root, run:

```text
python3 mathathon/spectral-gap/critical-law-round-01/formalization/validate.py
```

The pinned compiler is Lean 4.31.0. The mathlib revision is `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The wrapper checks every source hash and every pinned dependency checkout revision. It reads the existing dependency cache without changing its sources or compiled files. There is no network step or dependency build.

Each of the three compilations has two threads, a 4096 MB memory bound and a 120-second timeout. The wrapper requires warning-free compilation and checks each theorem's axiom list. Compiled outputs are temporary. Logs and the new receipt are retained. An old success receipt is removed before replay begins.

The receipt records source, manifest, validator and compiler hashes. The `--lean` and `--packages-root` options allow another local copy of the same pinned dependencies. An independent replay can copy this formalization directory to a temporary location and execute its copied validator, leaving this packet's receipt unchanged.

The installed compiler and cached compiled dependencies remain trusted inputs. Checking dependency source revisions does not cryptographically verify each compiled dependency object. The dependency tree was not rebuilt in this run.

## Unproved application bridges

- The random graph law and the replacement of predetermined marks by uniform sampled coordinates.
- Joint marked-pair counts, overlap estimates, host geometry and convergence to a point process.
- The event that relevant pairs are disjoint and the probabilistic bound on their number.
- Identification of the graph resolvent or Schur matrix with the finite constant star and pair blocks.
- A uniform operator approximation for the discarded interaction tail and all graph-dependent remainder terms.
- The graph-specific formulas for kappa, the pair weights and the integer-distance phase.
- Weyl inequalities or other variational bounds transferring this finite matrix estimate to ordered graph eigenvalues.
- Full eigenvalue multiplicities, an eigenbasis, zero-eigenspace dimension and any spatial localization statement.
- The finite-to-infinite truncation argument, subsequential limiting laws, nonexistence of a full-sequence limit and historical novelty.

The packet verifies finite supporting algebra. It does not verify the critical random-graph law from end to end.
