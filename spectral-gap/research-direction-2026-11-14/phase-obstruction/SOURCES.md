# Source comparison and evidence limits

Date: November 14, 2026, America/Los_Angeles.

## Local input

The model is exactly the one-phase K4 permutation-lift proposal in [the revised guide](../../explanation/round1/04-spectral-gap-v2.tex), especially its pages 5 through 8. That guide already records gauge invariance of the universal-cover edge, the old/new-sector split, the candidate finite-size tail problem, and a twice-around-triangle calculation. The present candidate uses an unphased K4 minus one edge as a rare localized obstruction.

The [scope audit](../../../../spectral-reconciliation-2026-11-14/SCOPE_AUDIT.md) explains why the accepted moment manuscript does not already prove this graph-level claim. No accepted statement or frozen manuscript is changed here.

## Primary sources inspected in this pass

1. Bordenave and Collins, [Eigenvalues of random lifts and polynomials of random permutation matrices](https://annals.math.princeton.edu/2019/190-3/p03), 2019. The public abstract and the corresponding primary preprint establish the existing matrix-coefficient strong-convergence setting. Complex edge coefficients and the leading random-lift spectral edge are established background.

2. Chen, Garza-Vargas, Tropp and van Handel, [A new approach to strong convergence, version 3](https://arxiv.org/html/2405.16026v3#S3.SS3). Theorem 3.9 and Remarks 3.10 and 3.11 were read directly. For fixed self-adjoint matrix polynomials, Theorem 3.9 gives a fixed-excess O(1/n) tail, with explicit dependence on coefficient dimension, polynomial degree and excess. The remarks discuss random lifts, unavoidable tangle effects and conditioning away tangles. Applying the theorem to the 4 by 4 linear polynomial representing this lift gives the upper bound cited in the proof. The lower-bound proof does not need their theorem.

3. Chen, Garza-Vargas and van Handel, [A new approach to strong convergence II, version 3](https://arxiv.org/html/2412.00593v3#S9.SS2), June 2026. Theorem 9.4 improves the general polynomial convergence scale to O_P((log n/n)^(1/6)). This is the newer rate baseline. The proof here does not improve that scale.

4. Friedman and Kohler, [On the Relativized Alon Second Eigenvalue Conjecture I](https://arxiv.org/abs/1911.05688) and [VI](https://arxiv.org/abs/1911.05775). Abstract-level inspection confirms the established connection between rare tangles and sharp polynomial tail powers for regular Ramanujan bases. This pass did not reconstruct their full theorem chain or check whether an exact single-phase K4 example already appears there.

5. Bordenave and Collins, [Norm of matrix-valued polynomials in random unitaries and permutations](https://arxiv.org/abs/2304.05714). Abstract-level inspection confirms existing quantitative work with general matrix coefficients and universal lower bounds. The present note makes no general matrix-coefficient novelty claim.

## Evidence and status

- The proof is an explicit local-state calculation, exact first and second factorial moments, finite permutation exposure, and the variational principle after projection.
- The cubic root and eigenvalue decimals were checked numerically. Only their exact algebraic definitions enter the proof.
- No archived program, queue or research harness was launched.
- No simulation or finite sample establishes the probability claim. Its support is the symbolic argument in proof-v1.md.
- Separate proof review, a formalization, and a targeted priority comparison remain outstanding at freezing.
- This is a useful obstruction for the selected model, not evidence for a new general tangle theory or a transformation of spectral graph theory.
