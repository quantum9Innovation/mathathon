# Uniform cluster width and the scale beyond the transition

November 15, 2026. Owner: root. Revision 1, frozen for separate review.

## 1. Statement

Use the fixed-degree notation and model of SG-20. Let d>=3 be fixed, let m>=1 satisfy m=o(sqrt(n)), and put

    s=sqrt(m/n),  a=m^2/n,  w=max(s,a).

The marks are distinct and predetermined. Let B=sqrt(d-2) A E and let the new-vertex block be sH, where H is any symmetric matrix with ||H||<=H_0. With probability tending to one the original host has its fixed two-sided gap. On this event define its centered marked resolvent as before.

Then

    ||G_E(d)-g_d(d) I||=O_P(w),                           (1.1)

and, uniformly over this norm ball of H, the top m+1 augmented eigenvalues obey

    max_(1<=j<=m+1) |mu_j-d|=O_P(w).                      (1.2)

The next eigenvalue stays below the host's second eigenvalue. At a critical mark count m/n^(1/3)->c in (0,infinity), this proves tightness of the normalized entire cluster at scale s. In the supercritical dilute range n^(1/3)<<m<<sqrt(n), it gives the upper displacement scale a=m^2/n. Combined with the separately reviewed pair lower bound, that scale is also bounded away from zero in probability for the top eigenvalue.

Here O_P(w) means that for every epsilon>0 there is C_epsilon independent of n and H with limiting upper failure probability at most epsilon. No critical limiting distribution is asserted.

## 2. The variable-cutoff resolvent estimate

This uses Sections 2 through 5 of [nonbacktracking-upper-v1.md](nonbacktracking-upper-v1.md), SHA256 d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896. Its estimates are finite-n bounds, before the final substitution of the subcritical growth condition.

Fix K>=1 and set x=K w and R=floor(log_q(1/x)), with q=d-1. Since w->0 and w>=s>=n^(-1/2), for each fixed K this gives 1<=R<=L for sufficiently large n. The probability of two marked vertices within distance R is at most

    C m^2 q^R/n <= C a/x <= C/K.                         (2.1)

The squared Frobenius norm of the marked off-diagonal tail has expectation at most

    C m^2/n^2 [n q^(-R)+L^4]
      <= C[a x+m^2 L^4/n^2].                            (2.2)

After division by x^2, the second term is at most C m L^4/(K^2 n), which tends to zero for m=o(sqrt(n)). Markov's inequality bounds the probability that this tail exceeds x by C/K+o(1).

The deterministic stationary correction m(1+L)/n is o(s), and the expected nonnegative diagonal error O(m L^3/n) is o(s). Indeed, division by s yields respectively O(s L) and O(s L^3), both tending to zero when m=o(sqrt(n)). The spectral tail is o(s) as well. Add the vanishing host-gap failure probability. There is a constant C_d,rho such that

    limsup_n Pr(||G_E(d)-g I||>C_d,rho K w) <= C_d,rho/K. (2.3)

This proves (1.1). The precise numerical constant is not claimed sharp.

## 3. A deterministic monotonicity comparison

Let a real symmetric host have a simple top eigenvalue d, unit eigenvector u and remaining eigenvalues at most d-gamma. Let B and C be arbitrary real matrices of the compatible block sizes, with C symmetric. Put

    b=B^T u,
    F(z)=zI-C-B^T Q(zI-A|_(u perpendicular))^(-1)Q B.

For |z-d|<gamma,

    F'(z)=I+B^T Q(zI-A|_(u perpendicular))^(-2)Q B >= I.

Set T=||b||+||F(d)||. If T<gamma, then all the largest m+1 augmented eigenvalues lie in [d-T,d+T]. The next eigenvalue is at most lambda_2(A).

To prove the first assertion, take any T<t<gamma. Integrating F'>=I gives

    F(d+t)>=F(d)+tI,  F(d-t)<=F(d)-tI.

After eliminating the host complement, the exact retained Schur matrix is

    K(z)=[[z-d,-b^T],[-b,F(z)]].

For a vector (x,y), the cross term satisfies

    2|x| |b^T y| <= ||b||(x^2+||y||^2).

Thus K(d+t) is positive definite and K(d-t) is negative definite, because t>T. In both cases the eliminated block zI-A|_(u perpendicular) is positive definite. Congruence and inertia therefore give no augmented eigenvalue above d+t, and exactly m+1 above d-t. Let t decrease to T. The next-eigenvalue assertion is ordinary interlacing because A is a principal submatrix. This proves the claim, including T=0 by taking positive t.

This comparison does not require derivative convergence, scalar linearization, root simplicity, or a minimum spacing between augmented eigenvalues.

## 4. Application to the critical attachment

Write c=d-2 to avoid confusing this coupling constant with a=m^2/n. The exact SG-20 identity gives

    b=d sqrt(c) s e,
    F(d)=-sH-c d^2[G_E(d)-g I]+c A_C-2cd J_m/n,          (4.1)

where e is the unit constant marked vector and A_C=E^T A E. The probability A_C is nonzero is at most d m(m-1)/(2(n-1))=O(a), tending to zero in the present range. On its complement,

    T<=d sqrt(c)s+sH_0+c d^2||G_E(d)-g I||+2cd m/n.

By (1.1), this is O_P(w), uniformly over H. Since w->0, the event T<gamma has probability tending to one. Section 3 proves (1.2).

The lower pair obstruction supplies the matching supercritical top scale for H=0. Its bounded-H version follows also from the deterministic perturbation bound |lambda_max(Aug_H)-lambda_max(Aug_0)|<=sH_0, since s/a->0 in the supercritical range. Uniformity in H is simultaneous on one graph event. The labels themselves still cannot be chosen after sampling the graph.

## 5. Limits

The upper theorem stops at m=o(sqrt(n)). In that range the scale a tends to zero and direct marked edges disappear with high probability. The separate lower divergence theorem holds throughout m=o(n), but this upper argument does not identify a matching scale when m is comparable to or larger than sqrt(n).

The assertion concerns adjacency eigenvalues near the isolated host Perron mode. It does not imply eigenvector localization, bulk-edge universality, a normalized-Laplacian gap, a mixing-time bound or a solver guarantee. The new deterministic monotonicity comparison is classical Schur-complement reasoning, not a claimed new general method.
