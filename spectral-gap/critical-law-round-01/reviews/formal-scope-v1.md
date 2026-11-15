# Independent audit of the finite critical-law components

November 15, 2026. Reviewer: root. Verdict: accepted at the scope stated below. All 30 declarations passed an independent isolated source replay. No correction is required.

## Exact revision and exposure

The reviewer read the three source files, the complete validator and the final README. The reviewer did not author these sources, but supplied the intended finite matrix target and authored the written effective-operator argument. This is an independent implementation and scope audit, not independent discovery of the finite algebra.

| Item | SHA256 |
| --- | --- |
| formalization/SOURCE_MANIFEST-v1.json | f03a52bc3edd6bbeb5206a2e721f0a64e3abaad216a4b70021897fea3cef6432 |
| formalization/README.md | a4d7532778f933f152d35993b3f540d9c98b3510ac51b587b82d10f08b44f90e |
| formalization/validate.py | ac0757f32309302198dc3c7a6485deec41cbe0a4bbdfe39189c251f36335d163 |
| Author compilation receipt | e718f2e268c2d3a64995545f11cf9ab02a0fa2e8dc05af8f84d729fa483db5f6 |
| [Independent replay receipt](formal-replay-v1.json) | ed3591abea1a578bcfe788eda6bbfc720cc5c918d5ca0b7b5009d6c4754844e6 |

The manifest binds all individual sources and dependency configuration. The independent receipt repeats those bindings and records the compiler and validator hashes.

## Actual matrix and eigenvalue coverage

PairModes uses an explicit coordinate type consisting of a host coordinate, q free coordinates and p Boolean-indexed pairs. Here q is a free-coordinate count, not the branching factor in the written graph theorem. Its pairMatrix has precisely one off-diagonal weight in each row, and freeStar couples every free coordinate to the host with the same b.

The explicit pair vector has coordinates (1,sigma) in the selected block, sigma squared equal to one, and zero elsewhere. Its nonzero property is proved. The collective vector has host coordinate t, all free coordinates one, and t squared equal to q. It is nonzero when q>0. Both types are embedded into the actual block diagonal matrix and stated through the standard HasEigenvector interface.

The coverage proof starts from an actual nonzero eigenvector. A nonzero pair coordinate forces the square of its eigenvalue to equal the corresponding weight squared. A nonzero free-star eigenvalue forces a nonzero host coordinate and then the equation mu squared equal to q b squared. The direct-sum decomposition establishes the claimed union of all possible real eigenvalues. No proposed eigenvalue list is assumed as a premise.

This is coverage and realization, not a multiplicity theorem. The source does not prove the zero eigenspace dimension, an eigenbasis or the full characteristic polynomial. The paper's elementary direct-sum multiplicity argument remains a bridge. The README states this accurately.

## Actual removal of exceptional couplings

CouplingError defines the actual removed matrix with entries b between the host and every exceptional paired coordinate, and zero elsewhere. Its coupled matrix is the decoupled matrix plus that explicit matrix. The proof derives each coordinate of the removed action rather than assuming a desired norm estimate.

The Euclidean squared norm is the actual finite sum of squared entries, and the Euclidean norm is its square root. This avoids confusing the Euclidean norm with a default function-space norm. The source derives the exact squared action and uses finite Cauchy-Schwarz to bound it by 2p b squared times the input squared norm. Taking square roots gives a bound for every vector, including arbitrary real b. It is a genuine uniform Euclidean matrix-action bound. The separate continuous-linear-map operator-norm packaging is not encoded, but its usual finite-dimensional interpretation is immediate and is not overstated in the README.

## Exact finite normalization

NormalizedModes substitutes b=kappa/sqrt(q+2p) into the actual matrices. It retains the collective coefficient kappa sqrt(q/(q+2p)) and the coupling-removal coefficient absolute kappa times sqrt(2p/(q+2p)). The unrestricted algebraic identities also cover the zero-denominator convention in the ambient field. The nonzero collective eigenvector statement explicitly requires q>0, as required in the application.

There is no assumption that the finite coefficient already equals kappa. Passing from q/(q+2p) to one requires the separate probabilistic estimate that p is tight and m=q+2p tends to infinity.

## Fresh source replay

Before execution, the validator was inspected. It verifies frozen source hashes, Lean 4.31.0 and each pinned dependency checkout. It deletes a prior success receipt before compiling, puts fresh local outputs first on the import path, compiles each source with two threads, a 4096 MB setting and a 120-second timeout, and requires warning-free success. It also compares printed axiom reports with the complete theorem inventory.

The replay copied the packet to /tmp/spectral-critical-formal-bwnxurov and ran the copied validator. It passed 13 PairModes declarations, 10 CouplingError declarations and 7 NormalizedModes declarations. Every printed axiom list contains only propext, Classical.choice and Quot.sound. Source inspection found no placeholder proof or custom axiom. The author receipt was verified unchanged after the replay. The independent receipt is retained with this review.

The installed compiler and compiled dependency cache are trusted inputs. The dependency tree was not rebuilt, and checking source checkout revisions does not cryptographically verify every compiled dependency object.

## Formal boundary

The packet does not encode the random graph law, pair-count distribution, geometric matching event, graph-to-matrix approximation, analytic Schur transfer, Weyl ordering, full finite multiplicities, infinite Poisson family, cutoff removal, phase-dependent weak limit or historical novelty. It verifies the finite disjoint-pair eigenvalue structure and the small coupling-removal estimate that the written proof uses.

The 30 declarations include helper lemmas and specializations. They are neither 30 new research results nor a complete formal proof of the critical law. The precise scope is accepted with no unresolved finding.
