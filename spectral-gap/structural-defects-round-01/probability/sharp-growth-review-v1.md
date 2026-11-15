# Review of the sharp growth theorem for polynomial ports

November 15, 2026. Review revision 1.

Decision: accepted for the paper theorem stated in the reviewed revision. No mathematical correction is required by this review. This is an application audit using the frozen host estimates, not a new independent proof of those estimates or a formal verification.

## Exact inputs and exposure

The target is root/sharp-growth-v1.md, SHA256 db71f673c134ffd6b58cf2fa3d47e8dd0532f12793321742672affa97093e88b.

The local attachment model and its physical cluster argument are structural/vector-port-v1.md, SHA256 ff889b703f36bdf1bea9854c20c41b97578abdd92a474fc5e7c6bcc03472cde8. The variable-cutoff host bound is close-pair-transition-round-01/root/cluster-width-v1.md, SHA256 e40164dcf711cca13d945b666645c26aa8095b835e1e727d2d6d7159a78e7b8f. All three hashes were checked against the files read.

The reviewer authored earlier marked-resolvent and marked-pair probability premises and the current round's collective probability chain. The reviewer had also read earlier pair lower arguments. Those premises are exposed dependencies, not independently reviewed results here. The present compression, signed polynomial reduction, annulus application, growth ranges and nonresonant-channel inertia argument were reconstructed from the target and the exact frozen model. No live draft was read for this audit.

## 1. Actual compression and signed filters

Compress every motif copy isometrically to its unit vector v while keeping every host coordinate. The resulting host-to-motif map is p(A)E with p(x)=b(x)^T v. Its internal scalar is c_v=v^T Cv. From K_0v=0,

    c_v=d-k(d).

Consequently equation (6) is an actual isometric compression of the specified augmented matrix. The variational inequality for its largest eigenvalue has the asserted direction. No positivity of the entries of C, b or p is used.

For z>d, the full finite-host resolvent has the convergent nonnegative walk expansion. A walk in the universal regular cover with prescribed starting lift has a unique projected walk and can be recovered from that projection by path lifting. Thus the set of tree walks ending at any fixed endpoint lift injects into the finite-host walks with the prescribed endpoints. The chosen endpoint lift can be at the distance of a shortest host path. This proves both lower bounds in (7), including the diagonal bound. It does not require connectivity, a host spectral gap or an approximation to the projected resolvent.

Polynomial division gives the exact identity

    p(A)(zI-A)^(-1)p(A)
      =p(z)^2(zI-A)^(-1)-D_z(A).

The degree of D_z is at most 2 deg(p)-1. The fixed-radius tree condition therefore fixes its marked diagonal entries to the tree values. If the selected endpoints have distance greater than ell_0, its off-diagonal entry between them vanishes. These conclusions remain valid when the coefficients of p have both signs.

For the normalized positive pair vector, the two filtered diagonal entries are at least k(z). The filtered off-diagonal entry is at least p(z)^2 g(z) rho(z)^ell and hence at least its version with ell replaced by R. This proves (8). Other marked vertices do not enter that quadratic form, so the lower argument does not require every pair of marks to be separated.

Near d, a(d)=0 and a'(d)=D>0. Also p(z)^2g(z) tends to beta^2g(d)>0. With the stated B_0, the two continuous factors can each be bounded below by half their limit, while q^(-R)>=delta/B_0. Their product is then at least 2D delta. The upper bound a(d+delta)<=3D delta/2 gives the strict negative margin required in (10).

The full host block zI-A is positive definite for z>d. A negative vector for its exact Schur complement gives an augmented eigenvalue strictly above z. This establishes the strict inequality in (11), with its sign and normalization intact.

## 2. Annulus sampling and the range m=o(n)

For delta=Ts and theta bounded below, m tends to infinity. The chosen radius satisfies

    q^(2R)/n=O(1/m),
    q^R>=B_0/(qTs).

A radius-R ball at a specified host root fails to be a tree with probability at most a constant times q^(2R)/n in the configuration model. Conditioning on simplicity changes the constant only. Hence the fraction of roots with a nonmaximal ball tends to zero in probability.

Every root with a tree ball has exactly Delta_R annulus neighbors. Summing degrees gives the lower bound M_R>=(1-o(1))n Delta_R/2 on a host event of probability tending to one. The maximum-degree bound applies to every host, including roots with cycles.

The replacement of predetermined labels by an independent uniform m-subset is justified for the joint invariant events used here by label exchangeability. It is not a simultaneous assertion for every subset of one realized graph.

For a uniform fixed-size subset, write p_j=(m)_j/(n)_j. Expanding the square of the induced annulus edge count gives:

- Equal edges contribute mu.
- Ordered pairs of distinct edges sharing a vertex number at most n Delta_R squared and have inclusion probability p_3.
- Disjoint ordered edge pairs have inclusion probability p_4<=p_2 squared.

This proves (14). Using M_R comparable to n Delta_R and m tending to infinity,

    p_3 n Delta_R squared / mu squared = O(1/m).

No independence of overlapping edge indicators is assumed. The resulting second-moment lower bound is exactly (15). Finally,

    Delta_R=(1+o(1))d q^R/(q-1)

because R tends to infinity. Substitution gives the constant A_0 in (16), including its factor q from the integer radius.

The event that all marked fixed-radius neighborhoods are trees has failure probability O(m/n). It is subtracted after the sampling estimate, not imposed as an unjustified conditional host law. Thus the witness and probability calculation remain valid throughout m=o(n). In particular, no O(m squared/n) separation condition has entered this lower bound.

The claimed consequences follow. A subsequence with theta bounded below and any fixed T>kappa prevents convergence in probability to kappa. If theta tends to infinity, (15) tends to one for every fixed T. Neither implication requires a limiting value of theta or a limiting distance phase.

## 3. Subcritical cluster transfer

When m cubed/n tends to zero, the polynomial locality failure probability O((m+m squared)/n) tends to zero. The exact matrix polynomial identity converts the log-free host estimate into Delta_n(d)=o_P(s), since the stationary term has norm O(s squared).

The previously frozen derivative bound gives the required o_P(1) Gram error in this regime, also when m is bounded. The retained star coefficient is beta/sqrt(D), with D from the resonant scalar channel, rather than a derivative from an arbitrary motif direction.

The exact identity HJ=sVT+W has bounded V, W=O(s squared) and J^T W=0. With a fixed complementary gap, leakage is O_P(s), the compressed-energy leakage error is O_P(s squared), and normalization changes the matrix divided by s by o_P(1). This proves the asserted complete top m+1 comparison, rather than only a largest-root comparison. No critical relation between m and n is used at this step.

## 4. Upper width and the nonresonant channels

For m=o(sqrt(n)), w=max(s,m squared/n) tends to zero and the fixed-radius mark separation event has probability tending to one. The variable-cutoff host estimate therefore gives F_n(d)=I tensor K_0+O_P(w).

The derivative bound is independent of m. Indeed the polynomial host-to-motif map has a norm bounded by the fixed sum of polynomial norms times coefficient-vector norms. The fixed host gap then bounds the relevant resolvent and its derivatives. In particular F_n'(z)>=I.

On the event with deviation at most Mw, integration of this derivative inequality gives the stated positive bound at d+h. At d-h, the m-dimensional kernel restriction has Rayleigh quotient at most -(C_M-M)w. Min-max therefore places m eigenvalues below this negative threshold. The remaining eigenvalues stay positive by the fixed positive spectrum of K_0 and the norm continuity bound on the interval of length h. This gives exactly m negative eigenvalues with the needed distance from zero.

The retained host diagonal is also negative at d-h. The star perturbation has norm at most ||b(d)||w. The chosen C_M leaves sufficient margin on all negative directions, while the positive directions have a fixed margin. The lower endpoint consequently has exactly m+1 negative eigenvalues. At the upper endpoint every retained direction is positive. Exact inertia gives the width of the largest m+1 cluster.

The same argument at fixed endpoints separates every remaining eigenvalue from d. This avoids an incorrect use of the m-row interlacing index when each mark adds k coordinates. The cluster count remains m+1 because there is one local kernel direction per mark and one retained constant host direction.

## 5. Postcritical scale and limits

For n^(1/3)<<m<<sqrt(n), t=m squared/n tends to zero and t/s=theta tends to infinity. Taking delta=at gives

    q^(2R)/n=O(n/m^4)=o(1).

The same annulus proof gives mean at least (1-o(1))A_0/a and overlap ratio O(1/m). It yields (19). Sending a to zero is the required bounded-away-from-zero-in-probability statement. The upper width supplies tightness at scale t. A deterministic coefficient is neither needed nor established.

The separation of ranges is correct:

| Conclusion | Growth assumption | Reason for the boundary |
| --- | --- | --- |
| Failure of the star limit and lower divergence | m=o(n) | All marked fixed-radius tree neighborhoods suffice |
| Whole-cluster upper width | m=o(sqrt(n)) | The full matrix locality identity needs fixed-radius mark separation |
| Matching postcritical scale | n^(1/3)<<m<<sqrt(n) | The lower displacement tends to zero and the upper locality estimate applies |
| Star limit | m cubed/n tends to zero | Log-free marked-resolvent error is o_P(s) |

This review accepts the adjacency or specified symmetric weighted-operator statements. It does not supply a normalized-Laplacian result, an arbitrary marked-set result, a multiple-local-kernel theorem, a formal encoding or a new priority claim. The triangle and star example identifications remain inherited claims of the separately reviewed scalar-port packet, rather than a new example audit here.
