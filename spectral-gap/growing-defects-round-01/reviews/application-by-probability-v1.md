# Application audit of the growing defect theorem

Date: November 15, 2026, America/Los_Angeles.

Disposition: accepted for the application scope audited below. No unsupported inference was found in the deterministic transfer or its stated weighted random-graph application, conditional on the separately tracked probability premise. This is not an independent review of the probability proof.

## Exact revisions and exposure

| File | SHA256 |
| --- | --- |
| root/graph-theorem-v1.md | b4a00f7b6490590a51e112c99be336e895723f29df4819c68d00dec526a4d2e3 |
| root/transfer-v1.md | deb05e53631ad4d273f48b2d6253014352c1263010d3990ebcc4e0b616351b99 |
| probability/proof-v1.md, used as the application premise | 56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b |

Both requested root-file hashes were checked before review. Both files were read in full. The reviewer authored the probability premise and had previously discussed the general-degree calibration with the integrator. That exposure is declared. The proof steps connecting the actual weighted matrix to the transfer statement were reconstructed here, but this review must not be represented as a blind or independent review of the entire theorem chain.

No canonical ledger, proof or source file was edited. Priority, formalization and the separate full-chain review remain outside this review's scope.

## 1. Actual matrix and exact projected identity

The matrix in graph theorem equation (6) is the stated object:

\[
 \mathcal A_n(H)=
 \begin{pmatrix}A_n&\sqrt{d-2}\,A_nE\\
 \sqrt{d-2}\,E^\top A_n& s_nH\end{pmatrix}.
\]

For d=3 and H=0 it is exactly the original simple-graph augmentation, with each new vertex joined to the original neighbours of its predetermined marked label. The theorem explicitly identifies the weights and possible diagonal potentials in the general case. It does not portray arbitrary H as a simple graph adjacency matrix.

On the projected host subspace, the identity

\[
 A_nR_Q(z)A_n=z^2R_Q(z)-zQ-A_nQ
\]

is correct. Compressing it by E gives

\[
 E^\top A_nR_Q(z)A_nE
 =z^2G_E(z)-zI_m-E^\top A_nE+(z+d)J_m/n.
\]

Subtracting this expression, with factor d-2, from zI_m-s_nH verifies graph equation (16). In particular, the stationary correction has a negative sign in F_H and includes both z and d. No full inverse at the Perron pole is used.

## 2. Calibration, signs and constants

Substitution of the tree constants gives

\[
 (d-1)d-(d-2)d^2\frac{d-1}{d(d-2)}=0.
\]

The proposed coupling therefore cancels the constant regular part at the host eigenvalue. The derivative calculation gives exactly

\[
 D_d=(d-1)-(d-2)(2dg+d^2g')
 =\frac{2(d-1)^2}{(d-2)^2}>0.
\]

The Perron coupling is

\[
 b=\frac{d\sqrt{d-2}}{\sqrt n}\mathbf1_m.
\]

After the reference-derivative congruence, its normalized coefficient is

\[
 \frac{d\sqrt{d-2}}{\sqrt{D_d}}
 =\frac{d(d-2)^{3/2}}{\sqrt2(d-1)}=\kappa_d.
\]

The reference value is Z_H=-s_nH. Since the transfer matrix has lower-right block -D^(-1/2)Z_HD^(-1/2), that block is positive s_nH/D_d. This verifies the sign and all constants in the effective matrix.

The value and derivative error bounds (18), (20) follow from the frozen probability premise. The remaining stationary norm is proportional to m/n=s_n squared and is therefore o(s_n). Dropping E^\top A_nE is justified only on its separately controlled high-probability zero event, as the proof states.

## 3. Dimension-free deterministic transfer

The transfer proof's elimination of the host complement is an actual invertible triangular congruence. For z>d-gamma, the eliminated block is positive definite. Sylvester inertia therefore yields precisely

\[
 \#\{j:\mu_j(\mathcal A)>z\}=n_-(K(z)).
\]

The signs of F' and F'' are correct. The second derivative has norm at most 2||B|| squared divided by (gamma-h) cubed. The integral Taylor remainder supplies the factor one half, so the quadratic remainder in equation (4) has the correct coefficient.

The reference-derivative congruence changes only the lower-right error block. Its norm costs at most 1/lambda_min(D), with no factor depending on m. The increasingly ordered eigenvalues of tI-T are t-theta_j when theta_j is decreasingly ordered. Thus the Weyl comparisons and the two inertia tests in Section 4 have the correct ordering.

The strict endpoint inequalities exclude endpoint roots. They count exactly m+1 eigenvalues in the interval and none above it. The additional test points prove the maximum ordered error bound without differentiating eigenvalue branches or assuming simple roots. Repeated effective eigenvalues and growing multiplicities are covered.

The interlacing index is also correct. Deleting the m new coordinates gives mu_(m+2)<=lambda_2(A), whenever the index exists.

## 4. Uniformity over interactions

The event controlling the marked resolvent, its derivative and E^\top A_nE is independent of the particular matrix H chosen within the norm ball. Both displayed application errors are uniform over H because the term -s_nH is retained exactly in Z_H and has zero derivative in z.

The attachment norm is at most d sqrt(d-2), independent of m. The host gap is fixed. Choosing L larger than kappa_d+H_0/D_d+1 gives a deterministic margin. Equation (23) tends to zero on the common event, so the transfer applies simultaneously to all symmetric H with norm at most H_0. This justifies choosing H after seeing the host. It does not justify choosing the marked labels after seeing the host, and the statement explicitly distinguishes those operations.

Continuity on the compact finite-dimensional norm ball makes the supremum measurable. The finite host sample space also removes any measurability concern. Uniformity over H introduces no hidden union bound over that ball.

## 5. Worked and boundary cases

- At d=3, H=0, the constants reduce to D_3=8 and kappa_3=3/sqrt(8). The effective spectrum consists of two opposite nonzero values and m-1 zeros, exactly as claimed.
- For m=2, multiplying kappa_3 by s_n=sqrt(2/n) gives 3/(2 sqrt(n)). The top and third eigenvalue coefficients are correct, and the middle mode has only an o_P(n^(-1/2)) assertion.
- For H=hI_m, the orthogonal modes have value h/D_d. The remaining two values are the eigenvalues of the two by two matrix with diagonal 0 and h/D_d and off-diagonal kappa_d. This gives equation (24).
- For symmetric H with He_m=h e_m, the orthogonal complement of e_m is invariant. The decomposition in Section 7 is valid. It does not assert that the two collective values must bracket every orthogonal-sector eigenvalue in this more general case.
- The adjacent cubic tree Green matrix in Section 8 has off-diagonal value 1/3. Substitution together with its actual marked adjacency gives off-diagonal regular part -2. This is a correct algebraic illustration of why that geometry is outside the scalar approximation. It is not used as an additional conditional random-graph theorem.

Condition m cubed times log(n) squared divided by n tending to zero contains the original requested power range, allows m=1, and implies s_n tends to zero and m squared divided by n tends to zero. The theorem does not silently replace the original cubic model or require m to diverge.

## 6. Corroborating checks and limits

An exact rational calculation checked the calibration and derivative identities at degrees 3 through 50. Floating-point checks covered 96 deterministic transfer instances with n in {3,5,9} and m in {1,2,4,7}, including cases where the defect dimension exceeds the host dimension. All satisfied the asserted cluster count, ordered error bound and interlacing inequality. Another 27 finite effective-matrix checks verified the H=hI spectrum at three degrees, three defect counts and three values of h.

These checks are corroboration only. The acceptance above rests on the displayed identities, norm bounds, inertia and ordered spectral comparison, not on finite numerical tests.

No corrective finding is required in the audited revisions. The final status still depends on the separate review of the probability premise. This review establishes neither historical firstness, optimality of the growth range, proof-assistant coverage, a bulk-edge result, nor any consequence for normalized-Laplacian mixing or spontaneous-tangle occurrence probabilities.
