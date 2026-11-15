# Independent review of the sharp growth criterion

Date: November 15, 2026. Revision 1, frozen after reconstruction.

Verdict: accepted at the complete stated scope, conditional on the explicitly identified frozen host estimates. No unsupported inference was found. This is a mathematical review, not a formal proof certificate or a priority determination.

## Exact target and exposure

The target is `../root/sharp-growth-v1.md`, SHA256 `db71f673c134ffd6b58cf2fa3d47e8dd0532f12793321742672affa97093e88b`.

The reviewer authored this round's finite formal packets, including scalar attachment reconstruction, the signed compact cancellation example, and the finite arrow Schur calculation. The reviewer previously reviewed the earlier negative logarithmic probability argument and integration record. Those tasks did not establish the present general lower obstruction or upper cluster count. The present review independently reconstructed every section of the target. The target's acceptance labels were not used as proof premises.

The following dependencies were read at the displayed revisions:

| File | SHA256 | Use in this review |
| --- | --- | --- |
| `../structural/vector-port-v1.md` | `ff889b703f36bdf1bea9854c20c41b97578abdd92a474fc5e7c6bcc03472cde8` | Entire definition, hypotheses, exact polynomial identity, retained inertia, lift action and Gram identities |
| `../../close-pair-transition-round-01/root/cluster-width-v1.md` | `e40164dcf711cca13d945b666645c26aa8095b835e1e727d2d6d7159a78e7b8f` | Entire variable-cutoff bound and its growth range |
| `../../close-pair-transition-round-01/root/nonbacktracking-upper-v1.md` | `d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896` | Statement, finite two-walk estimate, coordinate sampling, log-free compression and derivative bridge |
| `../../growing-defects-round-01/probability/proof-v1.md` | `56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b` | Model and fixed-gap conventions, compared with the derivative bridge above |

The frozen host estimate proofs are accepted dependencies. This review checks their use here and does not represent a new independent review of every earlier host theorem.

## 1. Actual local compression and the pair witness

The map that retains the host and sends the scalar coordinate at each mark to its unit motif vector v is an isometry. Its compression is exactly the matrix in target (6), with coupling polynomial p(x)=b(x)^T v and internal diagonal c_v=v^T C v. The kernel calibration gives c_v=d-k(d). Thus its largest eigenvalue is a genuine variational lower bound for the augmented operator, including signed polynomial ports.

For z>d the full resolvent has its convergent nonnegative walk expansion. Lifting from a fixed initial point on the universal cover is unique. Walks ending at one selected lift of the target therefore inject into host walks ending at that target. This proves both full Green lower bounds in (7), without a host gap or connectedness assumption.

Polynomial division gives p(A)(zI-A)^(-1)p(A)=p(z)^2(zI-A)^(-1)-D_z(A). The chosen fixed tree radius makes the diagonal of D_z(A) equal its tree moment. Its off-diagonal vanishes when the marked distance exceeds ell_0. For the unit positive pair vector, the averaged diagonal self-energy is at least k(z), and the cross term is at least p(z)^2 g(z) rho(z)^ell. Since rho(z)<1 and ell<=R, target (8) follows with the stated sign. No positivity assumption on the coefficients of p has entered this calculation.

Here a'(d)=D=1-k'(d)>0. With B_0=beta^2 g(d)/(8D), the two factors p(d+delta)^2 g(d+delta) and q^R rho(d+delta)^R can each be bounded below by half their limiting values. Since q^(-R)>=delta/B_0, their product is at least 2D delta. The upper expansion a(d+delta)<=3D delta/2 therefore leaves a strict negative margin. Exact Schur inertia yields a strict eigenvalue above d+delta. All constants and strict inequalities in (9)-(11) check.

## 2. Pair count and the broad lower range

For delta=T sqrt(m/n), q^(2R)/n=O(1/m). A fixed lower bound on theta=sqrt(m^3/n) forces m to infinity. The standard configuration exposure and positive simplicity probability therefore make the fraction of roots without full radius-R tree balls tend to zero in probability. A full tree ball gives exactly Delta_R annulus neighbors, while every root has at most that many. Hence M_R>=(1-o(1))n Delta_R/2 on a host event of probability tending to one.

The conditional uniform-subset calculation in (14) is exact in its equal-edge term and an upper bound for the other terms. Ordered adjacent edge pairs number at most n Delta_R^2. For disjoint edges, the without-replacement probability satisfies p_4<=p_2^2. Since M_R is asymptotic to n Delta_R/2, the overlap term divided by mu^2 is O(1/m), independently of whether mu stays bounded or diverges. Cauchy-Schwarz gives (15).

The floor in R gives q^R>=B_0/(q T s). Combining it with Delta_R asymptotic to d q^R/(q-1) yields exactly A_0=dB_0/[2q(q-1)] in (16). The invariant event for predetermined marks has the same law as independent uniform marks sampled after the host. The fixed-radius locality failures are subtracted unconditionally with probability O(m/n), rather than incorrectly conditioned away. Thus the entire lower argument applies to m=o(n), and gives the probability bound (4), divergence when theta tends to infinity, and necessity in (3) by a subsequence with theta bounded below and a fixed T>kappa.

## 3. Subcritical sufficiency and bounded m

If m^3/n tends to zero, the fixed polynomial locality failure is O((m+m^2)/n)=o(1). The accepted log-free bound makes the full self-energy deviation o_P(s). Its stationary term has norm O(s^2). The fixed derivative estimate is o_P(1) throughout this range, including bounded m.

The vector-port identities are consistent under this substitution. In particular HJ=sVT+W, the residual has norm O(s^2), and J^T W=0. The scalar resonant compression has lower block o_P(1), while J^T J=I+o_P(1). The fixed complementary spectral gap gives leakage O_P(s), and the resulting energy error after division by s is o_P(1). This comparison does not require a growing mark count. It transfers the entire star multiset, with multiplicities, to the actual top m+1 cluster.

## 4. Positive channels and the dilute upper width

The cited variable-cutoff estimate applies exactly for m=o(sqrt(n)). Its cutoff bound controls the full marked resolvent norm at w_n=max(s,m^2/n), not merely an individual entry. Polynomial locality then gives F_n(d)=I tensor K_0+O_P(w_n). The host gap bounds the derivative uniformly, while F_n'>=I.

At d+C_M w_n, the motif block is positive with a margin greater than the norm of the host coupling, and the host diagonal has the same margin. At d-C_M w_n, restriction to the m-dimensional local kernel is at most -(C_M-M)w_n. Min-max produces at least m negative eigenvalues with that magnitude. Weyl comparison with I tensor K_0 leaves the other m(k-1) eigenvalues positive and uniformly separated. Hence there are exactly m negative motif eigenvalues. The host coordinate contributes one more negative direction. The coupling norm ||b(d)||s is smaller than the displayed margins, so it cannot alter this inertia.

The eliminated host complement is positive on the whole fixed interval. Congruence therefore counts exactly the top m+1 augmented eigenvalues in the shrinking interval. The separate fixed-endpoint comparison leaves every remaining eigenvalue a fixed distance below d. This establishes the stated count for km added coordinates and does not use an invalid interlacing argument with only m added coordinates.

## 5. Matching postcritical scale and limits

For n^(1/3)<<m<<sqrt(n), t=m^2/n tends to zero and t/s tends to infinity. With delta=a t, the needed ball estimate is q^(2R)/n=O(n/m^4)=o(1). The expected annulus count is at least (1-o(1))A_0/a, with the same O(1/m) relative overlap correction. Target (19) follows. Letting a decrease to zero shows boundedness away from zero in probability. The upper width provides tightness after division by t. This is exactly the declared meaning of Theta_P(t), with no deterministic coefficient asserted.

The accepted result concerns fixed local data with one simple resonant channel and nonzero stationary coupling, predetermined marks, and a symmetric adjacency or weighted operator. The necessity and divergence range m=o(n) is broader than the m=o(sqrt(n)) upper width range. The argument does not prove simultaneous bounds over all selected mark sets, multiple critical channels, growing motif dimension, a normalized-Laplacian statement, a mixing theorem, or formal verification of the random-graph result.

No revision request is needed for this target.
