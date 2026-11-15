# Independent review of the critical graph subspace proof

Date: November 15, 2026, America/Los_Angeles.

Decision: accepted at the exact frozen revision. No unsupported inference remains in the finite isometry lemma, first-order level-subspace theorem, mass operators or union concentration statement. The finer pair approximation needed for a resonance theorem is correctly excluded from this proof.

## Exact input and exposure

The entire file `root/subspaces-v1.md` was read at SHA256

`f13fbd47ba04bd638f4bafe940c20d604bfa4a4653df553b4b737f2e3779e87a`.

The reviewer had previously reviewed the critical-law, pair-count and effective-operator inputs and the older marked resolvent and deterministic transfer arguments. The reviewer authored the separate finite resonance note, knew the proposed isometry target, and received the intended precision from the integrator. The reviewer did not write this graph subspace proof. Its finite identities and all application steps were reconstructed from the frozen text. No new refined probability attempt was read for this review.

The previously frozen derivative estimate and the algebra expressing F' through the marked resolvent were reread to verify their quantitative use at criticality. This is a paper proof review, not a formal replay or an independent historical-priority determination.

## 1. Exact finite identities and the isometry

With R the host-complement inverse, (A-dI)RB=-QB. Multiplying the actual augmented block matrix by J therefore gives host coordinate u b^T v/sqrt(D) and added coordinate a b-F(d)v/sqrt(D). These are exactly the two coordinates of sVT. The sign of F and the factor sqrt(D) are correct.

Since F'(d)=I+B^T R squared B and RB takes values perpendicular to u, the remaining identities are

\[
 J^T J=\operatorname{diag}(1,F'(d)/D),
 \qquad J^T V=I,
 \qquad J^T HJ=sT.
\]

The inverse of H on the complementary spectral space gives the stated beta bound on (I-P)J. Subtracting its Gram matrix from J^T J yields ||J^T P J-I|| at most epsilon+beta squared. Thus the inverse square root exists under the stated hypothesis. Equality of ranks makes U an isometry onto the complete cluster, rather than only into it.

The normalized compression estimate follows by subtracting the complementary term J^T(I-P)H(I-P)J before applying the inverse square roots. Its norm is bounded by the product of the leakage norm and the residual norm. After division by s this is the stated order s times ||T|| squared over the fixed gap. No sum over eigenvectors and no factor of the cluster dimension occur. The constants and the dependence on D through v_D are consistent.

## 2. Critical precision

The prior derivative estimate at j=1 is valid before imposing the old subcritical growth condition. It gives the two terms m log^4(n)/n and m squared log^2(n)/n. Differentiating the exact F identity also introduces the value error O_P(s) and the stationary term m/n. At criticality, these are covered by the stated a_n, and O_P(s) is absorbed even into the displayed logarithmic upper order for sufficiently large n.

Since ||T|| is tight, the finite lemma gives both ||U-J||=O_P(a_n) and the normalized compression error O_P(a_n). At m asymptotic to c n^(1/3), a_n=O(n^(-1/3)log^2(n))=o(m^(-1/2)). The preceding host gap and interlacing inputs supply the required complementary spectral separation with probability tending to one.

This establishes the claimed finer graph-to-T precision. It does not imply a finer T-to-pair-block approximation, and the proof expressly preserves that distinction.

## 3. Whole level projectors and multiplicity

The reference levels form a locally discrete set away from zero. The selected interval can therefore isolate a complete level, including a pair-collective collision. For a fixed cutoff, the matching comparison is an actual direct sum. Its pair vectors have the correct signs, and its collective vector uses the finite number of free marked coordinates.

Replacing that free collective vector by the full constant marked vector changes its span by O_P(sqrt(p/m)). At a positive collision its overlaps with the p pair vectors are 1/sqrt(m). Their Gram matrix remains nonsingular when p is tight and m tends to infinity. At a negative collision the antisymmetric vectors are exactly orthogonal to the retained collective vector.

The resolvent contour bound is dimension independent and applies to the whole level. Reference eigenvalues on the target level converge to the contour centre, while all other levels stay a fixed distance outside it. The complementary graph spectrum is also excluded by the fixed host gap. The effective theorem's fixed-cutoff error probability is sufficient because the argument first takes n to infinity and then sends the cutoff to infinity. Its target subspace does not change with that cutoff.

Projection distance below one gives equality of ranks, including the zero-pair-count event. The pair-count limit is the stated Poisson law. Uniform closeness of J to U also transfers the statement to the actual image JV by the lower singular-value bound on J restricted to any subspace. Repeated levels never require selecting individual eigenvectors.

## 4. Basis-independent physical mass operators

The retained host coordinate maps to the actual constant host vector, while the added coordinates are divided by sqrt(D). The uniform near-isometry therefore gives the stated quadratic forms and their operator version on the complete cluster. Perpendicular host mass is the remaining mass and equals (D-1)||v|| squared divided by D, up to a uniform vanishing error.

A pair-only level has zero retained host coordinate, so every unit vector in its physical subspace has masses (0,1/8,7/8) asymptotically. A noncolliding collective level has masses (1/2,1/16,7/16).

For the collision calculation, subtract the p pair components from the positive collective vector. Its squared norm becomes 1-p/m, while its host coordinate remains 1/sqrt(2). The squared host projection onto the span is therefore (1/2)/(1-p/m), exactly as stated. On the negative side it is exactly 1/2. Since the physical host projection has rank one, convergence of its sole possible nonzero eigenvalue also justifies the basis-independent total mass without any dimension-dependent trace estimate. No equal allocation among an arbitrary basis is asserted.

## 5. Concentration near the union of endpoints

The two-sided host gap gives an operator-norm convergent Neumann series

\[
 RB=\sum_{j\ge1}(A/3)^j QE.
\]

For v supported on t selected endpoints, the unprojected finite sum is supported inside their radius-L host balls. Its constant-mode subtraction has norm at most L sqrt(t/n)||v||. The remaining operator tail is bounded uniformly by rho_0^(L+1)/(1-rho_0). The added coordinates already lie among the specified associated vertices.

These estimates hold for every vector in the retained pair subspace, independently of its chosen basis. Tightness of the endpoint count, the subspace projection theorem and the near-isometry transfer them uniformly to every unit vector of the actual physical level subspace. Taking n to infinity before L proves the stated concentration. The empty-subspace convention is supplied. No event asserting that all marked balls are trees is used, and no conditioning on a rare selected-pair event is hidden in the argument.

## Scope of acceptance

The accepted theorem covers fixed nonzero levels in the critical cubic H=0 model and predetermined marks. It gives the actual graph subspaces, uniform physical mass forms and concentration near the union of the relevant endpoint neighbourhoods. It does not choose a basis within repeated levels, prove one-pair localization for every eigenvector, identify a finer resonant splitting, or describe the accumulation point zero. It makes no normalized-Laplacian or solver claim and no end-to-end formalization claim.
