# Review of the filtered-port structural theorem

Date: November 15, 2026. Reviewer: structural workstream. Revision 1.

Target: `../root/port-interaction-v1.md`, SHA256 `5e41e11cccc76df15cb61f4fffa59a2f8e0a5b3d6ad92554298b294df2d10d17`.

Verdict: accepted as a paper theorem conditional on the frozen prior probability and finite-isometry premises stated by the target. No open mathematical finding was identified. Historical priority and formalization are not certified by this review.

## Exposure and independence

The reviewer read and reviewed several preceding rounds. The reviewer independently froze `route-v1.md`, SHA256 `ccb92c8b0db5f0ebf2ecd95deb59acf90d85c65920c2df8dd704636459750ce0`, before reading the target. The integrator had reported the existence of an independently derived filtered-port theorem without supplying its derivation. The formulations were then compared in full. Their agreement was not treated as a substitute for checking the target.

The review reconstructs the local energy decomposition, inertia, polynomial stationary term, growing-dimensional gap, physical lift, matching truncation, mass fractions, example constants and cancellation example. The accepted random-host results are premises. This review does not reprove the entire historical probability chain.

## 1. Local resonance and exact inertia

Write R_C(z)=(zI-C)^(-1). Positivity of R_C follows from the assumed motif gap. For f=b^TR_Cb, one has f>0 and (f^(-1))'=||R_Cb|| squared divided by f squared, which is strictly positive. The tree derivative k_p' is strictly negative because a nonzero polynomial cannot vanish on the support of the tree measure. Thus a>0 and 0<eta<1. Scaling b can enforce the calibration.

For t=b^Ty, the decomposition y=R_Cb t/f+y_perp has vanishing cross energy since b^Ty_perp=0. Its energy is t squared divided by f plus a strictly positive transverse form. It is an invertible coordinate decomposition. Eliminating the transverse blocks and then the positive host complement proves the exact inertia identity (12), including at z=d. No division by z-d occurs.

F' is uniformly positive and F'' uniformly bounded because the motif and host gaps are fixed and ||p(A)E|| is bounded by the maximum of |p| on [-d,d]. These are operator bounds with no sum over marks.

At d, F(d)=o_P(1). At d plus a small fixed gamma, F has a fixed positive lower bound. At d minus gamma it has a fixed negative upper bound. The host-to-port vector has norm |p(d)|s=o(1). The endpoint Schur matrices therefore have zero and m+1 negative eigenvalues respectively. All eliminated blocks are positive. This proves that exactly the largest m+1 eigenvalues form the near-d cluster, despite the km added coordinates.

## 2. Polynomial identity and random precision

The scalar polynomial division identity on the host complement gives

\[
 p(A)R_Q(z)p(A)=p(z)^2R_Q(z)-D_z(A)+D_z(d)uu^T.
\]

The plus sign is correct. On the constant vector, the final two terms cancel. On its complement they reduce to polynomial division.

Fixed-radius tree neighborhoods determine the finitely many diagonal moments, and separated marks kill the off-diagonal polynomial entries. The failure bound O(m/n+m squared/n) suffices in both stated regimes. The event concerns finitely many powers of A, so the resulting identity holds simultaneously in z and can be differentiated. The stationary correction has norm O(m/n)=O(s squared). Its value at d is 2p(d)p'(d), giving the negative sign in F(d).

The subcritical resolvent estimate without logarithmic loss is a frozen close-pair result. The critical value, derivative and full marked-space tail estimates are also frozen premises. Fixed polynomial substitution preserves these estimates. No rare-event conditioning or entrywise-to-operator dimension factor is introduced. The o_P(1) derivative error needed by (23) follows directly. The stronger prior finite derivative bound also supplies the quantitative critical isometry rate in the separate route proof.

## 3. Full-cluster transfer and phase law

Congruence by diag(1,a^(-1/2)I) gives the displayed retained pencil. Its Taylor remainder tends to zero uniformly on each fixed bounded scaled interval. The effective matrix is tight in operator norm. On its bounded-norm event, ordered eigenvalue comparison and the exact inertia identity bracket every root. First taking n large and then increasing the bounding interval proves (24), including repeated roots.

The full marked-space tail estimate is applied with K fixed before n tends to infinity. The stationary correction divided by s vanishes. The short marked graph is a matching with a tight number of endpoints. Deleting their star entries costs |p(d)|sqrt(2p/(am)), tending to zero. The remaining star eigenvalues differ from plus and minus kappa by O_P(1/m). This proves (8), after splitting the error tolerance and enlarging the constant if necessary.

Prior shortest-distance tightness and finite-window Poisson counts give the lower truncation, while (8) gives the upper truncation. These yield the signed measure and its stated order statistics. Each pair supplies both signs, so the full process is correctly not called Poisson. Its intensity is the unchanged host-pair intensity. Distinct phases yield distinct positive lattice atoms above kappa, hence the phase dependence survives the spectral map. Endpoint phases zero and one agree by index shift.

## 4. Physical identities and masses

For M=R_C(d)b/f(d), b^TM=1 and ||M|| squared=(f^(-1))'(d). Multiplication gives the constant-host component of HJ as p(d)1^Tv/sqrt(an). Its motif component is b tensor

\[
 \alpha p(d)1/\sqrt n-F(d)v/\sqrt a.
\]

These are exactly sVT. Also J^TV=I. The host-complement Gram term is -K'(d)/a, while the motif Gram term is (f^(-1))'(d)I/a. Thus J^TJ=diag(1,F'(d)/a), with the required derivative signs.

The fixed complementary gap, bounded ||V||, tight ||T|| and these identities meet the finite-isometry lemma with no factor depending on m. Leakage is O_P(s). Orthogonal compression and inverse-square-root normalization give (28)-(29). The displayed mass fractions follow from the Gram components uniformly on retained unit vectors. The level statement uses a fixed spectral contour separated from other nonzero limiting levels and retains the entire level at collisions. It does not choose a basis in a repeated eigenspace.

## 5. Example and cancellation checks

For weighted duplication p(x)=x, C=0 and b=sqrt(d-2), tree polynomial division gives k_p(d)=d/(d-2)=f(d)^(-1). Differentiating gives a=2q squared/(d-2) cubed and eta=(d-2) squared/(2q squared). The stated kappa and h follow, including cubic eta=1/8.

For the star motif, eliminating seven leaves gives f(z)=z/(z squared-7). Its inverse derivative at 3 is 16/9. Since g'(3)=-10/9, a=26/9 and eta=8/13. Thus kappa=3/sqrt(26), h=3/13, and both mass triples are correct. Its internal top eigenvalue is sqrt(7)<3. The single host-to-center edge and seven leaf edges are ordinary unweighted edges. This is a distinct simple graph attachment.

For p(x)=d-x, direct multiplication gives Bcal(Et,t)=d(Et,t) when E^TAE=0. The independent constant-host vector is also exact. These compact modes belong to a signed weighted example, as the target explicitly says. The independent-mark event has failure probability O(m squared/n). No unweighted nonnegative counterexample is claimed.

## 6. Comparison of the independent formulations

The formulations cover the same fixed-data class. In the route notation, K_0=dI-C-k_p(d)bb^T has a simple unit kernel vector v with beta=b^Tv nonzero. Therefore

\[
 M=v/\beta,\qquad a=D/\beta^2,\qquad\eta=1/D.
\]

The retained matrices and physical lifts agree up to a harmless host-coordinate sign. The root proof uses exact scalar port energy decomposition. The route proof retains the finite motif kernel and controls the other channels by a fixed gap. Their agreement is not an additional independent phenomenon.

The root proof adds the subcritical regime and a zero-coupling boundary example. The route proof adds a quantitative critical physical-isometry error, an unweighted triangle example and the degree-corrected Bethe-Hessian identity. These differences are compatible. Neither proof supplies a direct nonnormal Hashimoto resolvent estimate, a multiple-port law, a nonregular-host law or a finer general-motif retuned crossing.

No revision is requested for mathematical validity at this hash. Growing motif size, growing polynomial degree or several independent ports would require new uniform hypotheses and estimates.
