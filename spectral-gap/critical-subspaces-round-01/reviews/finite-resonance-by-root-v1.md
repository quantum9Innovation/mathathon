# Separate reconstruction of the finite resonance theorem

November 15, 2026. Reviewer: root. Decision: accepted at the exact revision below, with its conditional graph scope unchanged.

Target: [finite-normal-form-v1.md](../resonance/finite-normal-form-v1.md), SHA256 59bebac4b6a96d148d48830bf27130223d6820e53e16627720fb7f2f7216eed7.

## Exposure and method

The reviewer proposed the candidate positive two-dimensional resonance matrix before this proof was written and is developing the separate graph subspace transfer. The proof author's intermediate finite conclusions were also discussed. This is a separate algebraic reconstruction with disclosed exposure, not an independent discovery.

The full target was read. The reviewer recomputed the invariant coordinate actions, determinant, signed root expansions, mixing projectors and integer tuning. No numerical experiment is used to establish these identities.

## Checks

The antisymmetric pair vector has zero total defect coordinate, so its host coupling vanishes exactly. Its pair action is multiplication by -w. Symmetric pair differences have cancelling host couplings and eigenvalue +w. The dimensions p, p-1, f-1 and three sum to m+1, so the decomposition includes all multiplicities.

The aggregate host coupling is kappa sqrt(2p/m). Expanding the three-dimensional determinant gives (z-w)(z squared-alpha squared)-beta squared times z. Since alpha squared plus beta squared equals kappa squared, this becomes exactly (z-w)(z squared-kappa squared)-2 kappa squared p w/m. The factors of two and signs in the proof are correct.

Changing to the positive and negative collective coordinates divides each host-to-aggregate coupling by sqrt(2), giving kappa sqrt(p)/sqrt(m). The negative collective coordinate is separated by a gap tending to 2 kappa. Its elimination produces an order 1/m correction, so it vanishes after division by m^(-1/2). The two positive roots and the upper collective weight (1-tau/Delta)/2 follow from the actual two-by-two spectral projector. The dark eigenspace remains grouped. There is no individual basis claim inside it.

At the negative collective root, the product (z-w)(z-kappa) tends to 4 kappa squared. Isolating z+kappa gives the coefficient +kappa p/(2m) for the isolated equal-pair model. Substituting z=-w gives w squared=kappa squared(1-p/m), confirming the exact finer crossing. Additional nonresonant blocks can change this order 1/m coefficient, as the proof explicitly states.

The bounded off-resonant extension has an order 1/sqrt(m) coupling to a uniformly separated complement. Its Schur correction is order 1/m. This suffices for the positive normal form but does not control infinitely many weak modes or a random-graph remainder.

For the integer construction, m_j squared divided by 2 times 4^j tends to c cubed. The chosen even n_j has relative rounding error O(1/n_j), which is negligible after multiplication by sqrt(m_j). Its distance phase tends to 1/2 from the prescribed detuning, and its distance floor is j for all sufficiently large j. Thus all finite tau values are compatible with integer graph sizes and mark counts.

Finally, the precision counterexample is valid: an m^(-3/4) off-diagonal perturbation is o(m^(-1/2)) but dominates the original negative separation of order 1/m. It changes the limiting basis while preserving the claimed coarse approximation. It is correctly identified as a counterexample to an inference, not as an example sampled from the random-graph model.

## Scope and findings

No correction is required. The finite avoided crossing, cancellation, integer tuning and precision obstruction are accepted. The graph transfer remains conditional on the additional probability and isometry estimates. In particular, this review does not promote the finite negative 1/m coefficient to a graph theorem or resolve individual negative eigenvectors at exact finer resonance.
