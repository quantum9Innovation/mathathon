# Separate review of the finite-error resonant-cluster transfer

November 15, 2026, America/Los_Angeles.

Reviewed source: [root/transfer-v1.md](../root/transfer-v1.md).

Exact SHA256: deb05e53631ad4d273f48b2d6253014352c1263010d3990ebcc4e0b616351b99.

Verdict: accepted in its stated deterministic scope. No unsupported mathematical inference was found. The asymptotic consequence is understood with a positive scale s_n, as required by h_n=L s_n and the small-o notation. This review does not certify the random-graph input, novelty, formalization, or any later application.

## Independence and prior exposure

The reviewer had previously read NEXT_PROBLEM.md, SG-17, and the mathematical description of the proposed weighted fixed-d application. The reviewer had also read primary-source growing-rank transfer methods for the priority audit. The reviewer had not read the new probability or transfer attempts before this frozen source was assigned. The present review reconstructs the deterministic argument directly from the named revision. This is a separate reconstruction with disclosed shared target exposure, not access isolation.

## Finite-error reconstruction

1. The host-gap hypothesis places the entire spectrum of A_Q below d-gamma. For every z in [d-h,d+h], the eliminated block L=zI-A_Q is therefore positive definite, with inverse norm at most 1/(gamma-h). A lower spectral bound for A_Q is unnecessary.

2. Reordering the host complement, the distinguished vector u and the defect space gives the exact Schur matrix K in equation (8). The displayed triangular congruence is correct. Since L is positive definite, its negative inertia vanishes, so the number of augmented eigenvalues strictly above z equals the negative inertia of K. Multiplicities and zeros are treated correctly.

3. Differentiating the restricted resolvent gives F'=I+B^T Q(z-A_Q)^(-2)QB and F''=-2B^T Q(z-A_Q)^(-3)QB. Thus the second-derivative bound is 2||B||^2/(gamma-h)^3. Integrating the Taylor remainder contributes exactly ||B||^2 h^2/(gamma-h)^3, with no missing factor two.

4. The congruence by diag(1,D^(-1/2)) converts the linear part into tI-T. Only the lower-right error block remains. Its norm costs at most 1/a, because lambda_min(D)>=a. No upper bound on D and no commutation of D with the reference Z are needed.

5. The strict condition ||T||+eta_h<h makes the transformed pencil negative definite at -h and positive definite at h. The host block is positive definite at both endpoints. Therefore neither endpoint is an augmented eigenvalue, there are m+1 eigenvalues above d-h and none above d+h, and exactly the largest m+1 lie inside the interval.

6. With theta_j descending, the eigenvalues t-theta_j are ascending. The source correctly orders the perturbed pencil eigenvalues ascending as kappa_j. At t=theta_j+eta_h+xi, kappa_j>0, giving at most j-1 eigenvalues above the tested z. At t=theta_j-eta_h-xi, kappa_j<0, giving at least j eigenvalues above z. Taking xi down to zero proves the ordered error bound. Individual eigenvalue derivatives, simple roots and separation of the theta_j are unnecessary.

7. Removing the m defect coordinates gives A as a principal submatrix. Standard interlacing gives mu_(m+2)<=lambda_2(A). When the index m+2 exists, n>=2 and lambda_2(A) is defined. This confirms the claimed ordering relative to the rest of the host spectrum.

The argument works without tracking determinant zeros. Inertia already counts multiplicity and determines the ordering. Although monotonicity is a natural classical route, the proof's pointwise inertia and Weyl comparison is sufficient.

## Growing-dimension and probabilistic consequence

For positive s_n tending to zero, h_n=L s_n is eventually below gamma. Under the stated uniform lower bounds on gamma and a and upper bound on ||B||, the Taylor remainder divided by s_n is O(s_n). The other two terms divided by s_n tend to zero by the assumed errors. Hence eta_h=o(s_n), and the strict endpoint condition eventually holds when L>C+1.

The same deterministic conclusion applies on high-probability events. Intersecting those events with the error event eta_h/s_n<L-C is enough. No union over the m+1 roots is needed. Thus growing dimension causes no hidden factor in the approximation. The result does not infer these events from entrywise convergence.

## Exact boundary checks

- If B=0, D=I and Z=F(d), eta_h=0. The effective shifts are zero together with the eigenvalues of C-dI, exactly matching the decoupled matrix.
- For a one-dimensional host A=[d], C=dI_m and arbitrary B=b^T, D=I and Z=0 give eta_h=0. The full shifts are plus ||b||, minus ||b|| and m-1 zeros. This confirms the off-diagonal signs, ordering and repeated effective eigenvalues.
- For Z=0 and general positive D, T has the two nonzero eigenvalues plus and minus ||D^(-1/2)b||, and an (m-1)-dimensional zero subspace when b is nonzero. The source does not confuse these effective zeros with exact finite-system eigenvalues at d.

These are symbolic checks, not numerical evidence for the general theorem.

## Review boundary and next action

No source edits were made and the frozen hash was rechecked. No new mathematical finding requires repair. The remaining obligation is the probability estimate at the actual graph scale and its application to the exact block matrix. Priority remains governed by the separate audit, which credits existing growing-rank compressed-resolvent and inertia methods.
