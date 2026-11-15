# A compensated lattice-Poisson collective quadratic limit

November 15, 2026. Owner: probability workstream. Revision 1, frozen for separate review.

Status: complete paper argument for the statement below. It is not a canonical promotion, a historical-priority claim or an end-to-end formalization.

## 1. Exact model and declared exposure

Let A_n be the adjacency matrix of a uniform simple labelled cubic graph on even n vertices. Choose m=m(n) distinct vertex labels before sampling the graph, with

\[
 m/n^{1/3}\longrightarrow c\in(0,\infty).
\]

Let E be their coordinate inclusion, let u be the unit constant host vector, let Q=I-uu^top, and let e be the unit constant marked vector. Fix

\[
 2\sqrt2/3<\rho<1,\qquad
 \mathcal H_n=\{\|A_n-3uu^\top\|\le3\rho\}.
\]

On H_n define

\[
 G=E^\top R_Q(3)E,\qquad
 R_Q(3)=Q(3I-A_n|_{u^\perp})^{-1}Q.
\]

Extend G by zero off H_n. The fixed-gap input gives Pr(H_n^c)->0. This extension is used only for distributional statements, not for identities requiring an inverse.

Put

\[
 g=2/3,\qquad s=\sqrt{m/n},\qquad
 \theta_n=ms\longrightarrow\theta=c^{3/2},
\]

\[
 r=\lfloor\log_2(1/s)\rfloor,\qquad
 \phi_n=\log_2(1/s)-r.
\tag{1}
\]

Work along any subsequence on which phi_n tends to phi in [0,1]. The endpoint one is allowed. Let Z_(n,k) count unordered marked pairs at distance r+k. It is zero when r+k<1.

This workstream authored the earlier marked-resolvent, pair-count, refined-resolvent and logarithmic probability proofs. It also read and reviewed earlier deterministic graph applications and finite transfer proofs. The compensated-limit candidate and the need to retain its stationary centering were discussed before this round. No live structural or root attempt from this round was read before freezing this proof.

Frozen inputs, with checked hashes:

- growing-defects-round-01/probability/proof-v1.md, SHA256 56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b.
- close-pair-transition-round-01/root/nonbacktracking-upper-v1.md, SHA256 d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896.
- critical-law-round-01/probability/pair-counts-v1.md, SHA256 702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29.
- critical-subspaces-round-01/probability/refined-resolvent-v1.md, SHA256 bd00db6c2f69813d480f5a86d5d22c8b6fe4922d9cc3d233f72840dddb29f8df.
- critical-subspaces-round-01/probability/negative-log-scale-v1.md, SHA256 faced6a02d91d451e4ef0e0989d3d46811da66d809d40e9344e9444012901409.

These provide the fixed host gap, the nonbacktracking identity and second moment, the single-walk diagonal bound, the finite-window Poisson law, and short-path uniqueness. The finite sampling variance argument needed at the new scale is written out below. Every conclusion is for each predetermined label sequence, uniformly in that choice, not simultaneously over all marked sets in one graph.

## 2. Limit object and theorem

For every integer k define

\[
 \lambda_k=\frac34\theta\,2^{k-\phi},\qquad
 b_k=\frac4{3\theta}\,2^{\phi-k}.
\tag{2}
\]

In particular b_k lambda_k=1. Let the P_k be independent Poisson variables with means lambda_k. Define

\[
 C_\phi=-\frac23+
       \sum_{k\le0}b_kP_k+
       \sum_{k\ge1}b_k(P_k-\lambda_k).
\tag{3}
\]

The negative-offset sum has finitely many nonzero summands almost surely, since sum_(k<=0)lambda_k is finite. Its terms can have infinite total expectation, which does not prevent this almost-sure finiteness. The positive-offset centered series converges in L2 and almost surely because

\[
 \sum_{k\ge1}b_k^2\lambda_k=\sum_{k\ge1}b_k<\infty.
\tag{4}
\]

For example, its partial sums form an L2-bounded martingale, so the usual martingale convergence theorem proves both assertions. Formula (3) is therefore a well-defined finite random variable.

**Theorem 1.** Along the stated phase subsequence,

\[
 C_n:=\frac{e^\top(G-gI)e+s^2r}{s^2}
 \xrightarrow{\mathrm d} C_\phi.
\tag{5}
\]

Jointly, for every fixed finite integer set J,

\[
 (C_n,(Z_{n,k})_{k\in J})
 \xrightarrow{\mathrm d}(C_\phi,(P_k)_{k\in J}).
\tag{6}
\]

Thus conditioning on Z_(n,0)=p for any fixed nonnegative integer p gives the limit in (3) with P_0=p, all other P_k retaining their independent Poisson laws. The conditioning probability tends to the positive number exp(-lambda_0)lambda_0^p/p!.

At the resonant phase phi=1/2 the parameters are

\[
 \lambda_k=\frac{3\theta}{4\sqrt2}\,2^k,
 \qquad b_k=\frac{4\sqrt2}{3\theta}\,2^{-k}.
\tag{7}
\]

In particular the case p=1 is a graph-specific collective fluctuation law on the positive-probability event of exactly one resonant pair.

The theorem concerns a projected-resolvent quadratic form. It does not identify the next effective graph eigenvalue or the signed mixing coefficient at the retuned crossing. Those require the normalization and complementary-space correction at their actual order.

## 3. Nonbacktracking truncation and exact stationary coefficient

Let N_j count length-j nonbacktracking incidence walks. Its row sum is 3*2^(j-1). Choose L=ceil(C_0 log n) with C_0 large enough that the projected series has operator tail at most n^(-4) on H_n. The exact identity is

\[
 R_Q(3)=g\left[Q+
  \sum_{j=1}^L\left(2^{-j}N_j-\tfrac32 uu^\top\right)\right]
  +\mathcal E_L,\qquad \|\mathcal E_L\|\le n^{-4}.
\tag{8}
\]

Fix an integer K>=0 and put R=r+K. For large n, 1<=R<=L. Define

\[
 U_R=\sum_{j=R+1}^L2^{-j}N_j,\qquad
 T_R=\operatorname{offdiag}(E^\top U_R E).
\tag{9}
\]

The matrix U_R is symmetric and nonnegative. Its row sum is exactly

\[
 v_R=\frac32(L-R).
\tag{10}
\]

The earlier two-walk estimate gives, under the unconditional simple-host law,

\[
 \mathbb E\|U_R\|_F^2\le C(n2^{-R}+L^4).
\tag{11}
\]

With probability tending to one, every marked pair has at most one nonbacktracking incidence walk of length at most R. On this event the off-diagonal short sum is exactly W_R, where

\[
 (W_R)_{ab}=2^{-\operatorname{dist}(a,b)}
     \mathbf1_{\{\operatorname{dist}(a,b)\le R\}},\quad a\ne b,
 \qquad (W_R)_{aa}=0.
\tag{12}
\]

Let D_0=diag(G-gI). Deleting the diagonal in (8) and then restoring the actual diagonal gives, on H_n and the uniqueness event,

\[
 G-gI=gW_R+gT_R+D_0
       -\frac{g(1+3L/2)}n(J_m-I_m)+E_L,
 \qquad\|E_L\|\le2n^{-4}.
\tag{13}
\]

The coefficient includes the contribution from Q at j=0. It must not be omitted at the new scale.

The averaged single-walk diagonal estimate is

\[
 |e^\top D_0e|
 \le \frac1m\sum_{a=1}^m|G_{aa}-g|
 =O_{\mathbb P}(L^3/n+L/n+n^{-4}).
\tag{14}
\]

After division by s squared, this tends to zero, since n s squared=m and L cubed/m tends to zero. This use of an average is stronger than the maximum-diagonal estimate and is essential here.

## 4. Exact finite-subset sampling and tail variance

Relabelling invariance permits sampling a uniform independent m-subset S after the host. This gives exactly the same law as the predetermined labels for the statistics considered here. For v distinct fixed vertices, the inclusion probability is

\[
 p_v=(m)_v/(n)_v.
\tag{15}
\]

No calculation below conditions on H_n, short-path uniqueness or a marked-pair event.

Let H be any deterministic symmetric nonnegative n by n matrix with zero diagonal and row sums at most CL. Put

\[
 Y_H=\frac1m\sum_{a\ne b\in S}H_{ab}.
\]

Its exact conditional expectation is

\[
 \mathbb E(Y_H\mid H)=\frac{p_2}{m}\sum_{a\ne b}H_{ab}.
\tag{16}
\]

Its conditional variance satisfies

\[
 \operatorname{Var}(Y_H\mid H)
 \le C\left(\frac{\|H\|_F^2}{n^2}
              +\frac{mL^2}{n^2}\right).
\tag{17}
\]

For completeness, write the sum over unordered pairs and multiply by 2/m. Equal-pair terms in the variance have coefficient at most p_2. Distinct pairs sharing one endpoint have coefficient at most p_3. Their weighted sum is bounded by a constant times the sum of squared row sums, at most C nL squared. Disjoint pairs have covariance p_4-p_2 squared<=0, so their nonnegative weighted contributions may be discarded. The last inequality follows from

\[
 p_4/p_2=\frac{(m-2)(m-3)}{(n-2)(n-3)}
 \le\frac{m(m-1)}{n(n-1)}=p_2
\]

for sufficiently large m. Using p_2<=C m squared/n squared and p_3<=C m cubed/n cubed proves (17). This proof uses the actual fixed-size subset law, not independent marking.

Apply (16)-(17) to the off-diagonal part of U_R. Write

\[
 Y_R=e^\top T_R e,\qquad
 \overline Y_R=\mathbb E(Y_R\mid U_R).
\]

Its conditional mean is exactly

\[
 \overline Y_R
 =\frac{m-1}{n(n-1)}
      (n v_R-\operatorname{tr}U_R).
\tag{18}
\]

The first term divided by s squared differs from v_R by O(L/m). The remaining trace term is negligible in probability after that division. Indeed, nonnegativity and Cauchy-Schwarz give

\[
 \frac1n\mathbb E\operatorname{tr}U_R
 \le\frac1n\sqrt{n\,\mathbb E\|U_R\|_F^2}
 \le C\left(2^{-R/2}+L^2/\sqrt n\right)
 \longrightarrow0
\tag{19}
\]

for each fixed K. Its coefficient in overline Y_R/s squared is at most a constant times 1/n. Therefore

\[
 \overline Y_R/s^2=v_R+o_{\mathbb P}(1).
\tag{20}
\]

Taking expectations in (17) and using (11),

\[
 \frac{\mathbb E\operatorname{Var}(Y_R\mid U_R)}{s^4}
 \le C\left(\frac{n2^{-R}}{m^2}
             +\frac{L^4}{m^2}+\frac{L^2}{m}\right).
\tag{21}
\]

Since 2^(-R)=s 2^(phi_n-K) and n s/m squared=1/theta_n,

\[
 \limsup_{n\to\infty}
 \frac{\mathbb E\operatorname{Var}(Y_R\mid U_R)}{s^4}
 \le C_c2^{-K}.
\tag{22}
\]

This is an unconditional second-moment bound for the centered sampled tail. It is not an L2 estimate for a resolvent conditioned on the spectral-gap event.

## 5. The finite-cutoff comparison at order s squared

Define

\[
 b_{n,k}=\frac4{3\theta_n}2^{\phi_n-k},\qquad
 A_{n,K}=-\frac23-K+\sum_{k\le K}b_{n,k}Z_{n,k}.
\tag{23}
\]

The sum is finite because Z_(n,k)=0 for k<1-r. The exact short quadratic identity is

\[
 \frac{g e^\top W_R e}{s^2}
 =\frac{2g}{m s}\sum_{k\le K}2^{\phi_n-k}Z_{n,k}
 =\sum_{k\le K}b_{n,k}Z_{n,k}.
\tag{24}
\]

Evaluate (13) on e and divide by s squared. The stationary term becomes

\[
 -g(1+3L/2)(1-1/m).
\tag{25}
\]

Replacing 1-1/m by one costs O(L/m)=o(1). Equations (14), (20), (24), and the operator tail now give, on an event of probability tending to one,

\[
 C_n-A_{n,K}
 =g\frac{Y_R-\overline Y_R}{s^2}+o_{\mathbb P}(1).
\tag{26}
\]

The cancellation producing the constant in (23) is exact at its main order:

\[
 r+g v_R-g(1+3L/2)
 =r+g\tfrac32(L-R)-g(1+3L/2)
 =-K-g.
\tag{27}
\]

The host-gap and path-uniqueness exceptional probabilities tend to zero for every fixed K. Applying Chebyshev to the unconditional centered variable in (26), using (22), proves the key comparison: for every eta>0,

\[
 \limsup_{n\to\infty}
 \mathbb P(|C_n-A_{n,K}|>\eta)
 \le C_c\eta^{-2}2^{-K}.
\tag{28}
\]

A fixed numerical factor from splitting eta between the centered term and the vanishing error is included in C_c. All other terms in (26) have been shown to vanish after division by s squared. In particular the j=0 stationary correction leaves the nonzero constant -g=-2/3.

## 6. Finite-window limits and both tails

The frozen pair-count theorem gives joint convergence of the Z_(n,k) to independent P_k for each fixed finite set of offsets. It also gives the elementary uniform left-tail bound

\[
 \limsup_n\mathbb P\{Z_{n,k}>0\text{ for some }k<-J\}
 \le C_c2^{-J}.
\tag{29}
\]

This bound can alternatively be obtained from the deterministic cubic ball size and label symmetry. It does not control the mean amplitude of those rare stronger pairs, and no such mean bound is needed.

The same Poisson left-tail event has probability at most

\[
 \sum_{k<-J}\lambda_k\le C_{c,\phi}2^{-J}.
\tag{30}
\]

For fixed K, first retain only -J<=k<=K in (23). Finite-window convergence and b_(n,k)->b_k give convergence of this truncated sum, jointly with any fixed finite set of counts. Sending J to infinity using (29)-(30) proves

\[
 A_{n,K}\xrightarrow{\mathrm d}
 A_K:=-\frac23-K+\sum_{k\le K}b_kP_k.
\tag{31}
\]

For K>=0, the identity b_k lambda_k=1 gives

\[
 A_K=-\frac23+\sum_{k\le0}b_kP_k
                +\sum_{k=1}^K b_k(P_k-\lambda_k).
\tag{32}
\]

Its difference from C_phi has finite second moment even though the two variables separately need not have finite second moments. In fact,

\[
 \mathbb E|A_K-C_\phi|^2
 =\sum_{k>K}b_k^2\lambda_k
 =b_0\,2^{-K}.
\tag{33}
\]

Thus A_K tends to C_phi in probability. Combine (28), (31) and (33) by the converging-together argument for bounded Lipschitz functions. Explicitly, for a bounded Lipschitz f, first restrict both comparison errors to be at most eta. Its expectation difference is then bounded by its Lipschitz constant times eta and its bound times the corresponding exceptional probabilities. Send n to infinity with K fixed, then K to infinity, then eta to zero. This proves (5).

For joint convergence, retain a fixed finite count vector throughout the same argument. Choose the cutoffs to contain its offsets, and use the finite-window joint theorem. Neither comparison changes the count coordinates. This proves (6).

For conditioning, the coordinate Z_(n,0) is integer valued. Joint convergence implies convergence of expectations of bounded continuous functions of C_n multiplied by the indicator Z_(n,0)=p, since that indicator is continuous in the discrete count coordinate. Divide by its probability, which tends to the positive Poisson mass. This proves the conditional conclusion without applying any intermediate path estimate under rare-event conditioning.

## 7. Characteristic function and centering convention

The characteristic function is explicitly

\[
 \mathbb E e^{itC_\phi}
 =\exp\left[-\tfrac23it
 +\sum_{k\le0}\lambda_k(e^{itb_k}-1)
 +\sum_{k\ge1}\lambda_k(e^{itb_k}-1-itb_k)\right].
\tag{34}
\]

The first series is absolutely convergent because sum_(k<=0)lambda_k is finite. The second is absolutely convergent by |exp(ix)-1-ix|<=x squared/2 and (4). Formula (34) follows first for finite truncations and then from convergence in probability. Conditional on P_0=p, replace the k=0 Poisson term by it b_0 p.

The centering convention matters at the endpoint phase. Couple the families at phi=1 and phi=0 by P_k(1)=P_(k-1)(0). Their coefficients have the same relation. Reindexing (3) then gives

\[
 C_1\ \stackrel{\mathrm d}=\ C_0-1.
\tag{35}
\]

There is no contradiction with the endpoint identification in the earlier spectral law. The present variable includes the discontinuous integer center r. If instead one centers by the full logarithm, then

\[
 \frac{e^\top(G-gI)e+s^2\log_2(1/s)}{s^2}
 =C_n+\phi_n
 \xrightarrow{\mathrm d}C_\phi+\phi,
\tag{36}
\]

and its endpoint laws agree. At the retuned resonance phi=1/2 the choice is unambiguous, but it must still be recorded.

The left part of (3) has infinite expectation, since sum_(k<=0)b_k lambda_k is infinite. The theorem therefore asserts weak convergence, not convergence of moments. Its tail and compensation structure are separate from any unproved eigenvalue interpretation.

## 8. Limits of the result and next obligation

This proof supplies the complete order-s-squared fluctuation of one actual marked-resolvent quadratic form, jointly with the critical pair process. It retains the exact stationary center and all exceptional-event boundaries. It applies in particular on the positive-probability event of one resonant pair.

The effective collective graph eigenvalue at the retuned negative crossing also receives a complementary-space correction and an order-s normalization term in retained coordinates. Those terms can depend on the other pair levels and need not equal the linear statistic in (3). Consequently (5) is not presented as the final eigenvalue law.

The residual signed collective-to-antisymmetric coefficient must be determined from the actual graph reduction. A generic random avoided-crossing matrix is not assumed. Subsequent work will address that coefficient and the remaining order-s terms in separate frozen files.

Requested review: check the exact coefficient -2/3-K, the variance inequality for sampling without replacement, the trace error after division by s squared, both truncation limits, joint conditioning, and the endpoint translation in (35). No live structural or root attempt was read, and no earlier frozen file was edited.
