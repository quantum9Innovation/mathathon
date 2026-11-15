# A logarithm-free marked-resolvent bound by polynomial locality

Date: November 15, 2026, America/Los_Angeles.

Status: complete paper proof, frozen as revision 1 for separate review. No canonical claim is promoted by this file. Historical firstness and proof-assistant coverage are separate questions.

Owner: probability workstream. The argument below was developed before receiving the coordinator's alternative nonbacktracking route. That route was subsequently disclosed in a message but its proof file was not read before this revision was frozen. This argument uses a stronger quantitative host-spectrum input in exchange for avoiding a two-walk collision estimate.

## 1. Statement and precise additional input

Fix an integer d>=3 and put q=d-1. Let A_n be the adjacency matrix of a uniform simple labelled d-regular graph on n vertices, with nd even and n>=d+1. Let

\[
 \Pi_n=\mathbf1\mathbf1^\top/n,\qquad Q_n=I-\Pi_n.
\]

For each n fix m=m(n) distinct labels before sampling the graph. Let E_n be their coordinate-selection matrix and let s_n=sqrt(m/n). On a fixed two-sided host-gap event, define the full-space centered resolvent

\[
 R_n=Q_n(dI-A_n|_{\mathbf1^\perp})^{-1}Q_n,
 \qquad G_{E_n}(d)=E_n^\top R_nE_n.
\]

As in the accepted probability proof, extend the resolvent and its derivatives by zero off that event. No inverse is used on the exceptional event.

**Theorem 1.** If m cubed divided by n tends to zero, then

\[
 \left\|G_{E_n}(d)-\frac{d-1}{d(d-2)}I_m\right\|
 =o_{\mathbb P}(s_n),                                      \tag{1}
\]

and

\[
 \left\|G_{E_n}'(d)
 +\frac{(d-1)((d-1)^2+1)}{d^2(d-2)^3}I_m\right\|
 \xrightarrow{\mathbb P}0.                                \tag{2}
\]

These statements hold for every predetermined label sequence satisfying the displayed range. They are not a simultaneous maximum over all label sets in a sampled graph and do not cover graph-dependent mark selection.

The new input beyond the earlier elementary fixed-gap proof is the published quantitative host bound. Fix any 0<xi<1. Bordenave's published equation (2) gives a constant c_(d,xi)>0 such that

\[
 \mathbb P\!\left(\|A_n-d\Pi_n\|>
 2\sqrt q+c_{d,\xi}\left(\frac{\log\log n}{\log n}\right)^2\right)
 \le n^{-\xi}                                              \tag{3}
\]

for all sufficiently large admissible n. The source uses a non-strict exceptional inequality, which also implies (3). This exact published statement was inspected in the retained journal text, lines 135 through 160. Its proof is not reconstructed here.

Write

\[
 \epsilon_n=c_{d,\xi}\left(\frac{\log\log n}{\log n}\right)^2,
 \quad \Lambda_n=2\sqrt q+\epsilon_n,
 \quad \mathcal N_n=\{\|A_n-d\Pi_n\|\le\Lambda_n\}.
\]

Then epsilon_n log(n) tends to zero. In particular, for any fixed rho with 2 sqrt(q)/d<rho<1, the event N_n is contained, for all sufficiently large n, in the fixed host-gap event with norm at most d rho.

There is a useful quantitative version of (1). For every fixed eta>0, uniformly over 1<=m<=n^(1/3), for all sufficiently large n depending on d, xi and eta,

\[
 \begin{split}
 \mathbb P\bigl(\|G_{E_n}(d)-g_d(d)I_m\|>2\eta s_n\bigr)
 \le n^{-\xi}+C_{d,\xi}\bigg[&
 (1+\eta^{-2})\sqrt{\frac{m^3}{n}}\\
 &+\eta^{-2}\frac{m(\log n)^2}{n}
 +\eta^{-1}\sqrt{\frac mn}(\log n)^3\bigg],
 \end{split}                                               \tag{4}
\]

where g_d(d)=(d-1)/(d(d-2)). The constant does not depend on m or on the chosen labels. The proof below establishes (4), then (1) and (2).

## 2. An explicit polynomial approximation

Let 2 sqrt(q)<=Lambda<d and put

\[
 \Delta=\sqrt{d^2-\Lambda^2},\qquad
 \tau=\frac{d-\Delta}{\Lambda}
      =\frac{\Lambda}{d+\Delta}\in(0,1).
\]

Let T_k be the Chebyshev polynomial defined by T_0=1, T_1=x, and T_(k+1)=2xT_k-T_(k-1). On [-1,1], its absolute value is at most one. Summing the recurrence as an absolutely convergent series gives

\[
 1+2\sum_{k\ge1}\tau^kT_k(t)
 =\frac{1-\tau^2}{1-2\tau t+\tau^2}.
\]

Since d=Lambda(1+tau squared)/(2tau) and Delta=Lambda(1-tau squared)/(2tau),

\[
 \frac1{d-x}
 =\frac1\Delta\left(1+2\sum_{k\ge1}\tau^kT_k(x/\Lambda)\right)
 \quad (|x|\le\Lambda).                                   \tag{5}
\]

For an integer r>=0 define the degree-r polynomial

\[
 p_r(x)=\frac1\Delta\left(1+2\sum_{k=1}^r\tau^kT_k(x/\Lambda)\right).
\]

Truncating (5) gives

\[
 \sup_{|x|\le\Lambda}\left|\frac1{d-x}-p_r(x)\right|
 \le\frac{2\tau^{r+1}}{\Delta(1-\tau)}.                    \tag{6}
\]

The value at the omitted Perron eigenvalue has only linear growth in r. Indeed, the same recurrence gives

\[
 T_k(d/\Lambda)=\frac{\tau^k+\tau^{-k}}2,
\]

and therefore the exact formula is

\[
 p_r(d)=\frac1\Delta\left(r+1+\sum_{k=1}^r\tau^{2k}\right).
                                                                    \tag{7}
\]

Fix Lambda_*=(d+2 sqrt(q))/2<d. For Lambda in [2 sqrt(q),Lambda_*], both Delta and 1-tau are bounded below by positive constants depending only on d. Thus

\[
 |p_r(d)|\le C_d(r+1).                                    \tag{8}
\]

To control the approximation error at Lambda_n, observe

\[
 \frac{d}{d\Lambda}\log\tau(\Lambda)
 =\frac{d}{\Lambda\sqrt{d^2-\Lambda^2}}.
\]

This derivative is bounded on the displayed compact interval, and tau(2 sqrt(q))=q^(-1/2). Consequently

\[
 \tau(\Lambda_n)^{2(r+1)}
 \le q^{-(r+1)}\exp(C_d\epsilon_n(r+1)).                   \tag{9}
\]

Since epsilon_n log(n) tends to zero, for every integer

\[
 0\le r\le\frac{\log n}{2\log q},                         \tag{10}
\]

equations (6) and (9) yield, for sufficiently large n,

\[
 \sup_{|x|\le\Lambda_n}\left|\frac1{d-x}-p_r(x)\right|^2
 \le C_d q^{-r}.                                         \tag{11}
\]

The polynomial here depends on n through Lambda_n, which is deterministic. All constants in (8), (11) are uniform over r satisfying (10).

## 3. Deterministic far-row squared-mass bound

Consider any simple d-regular graph satisfying N_n. Use the polynomial from Section 2 with Lambda=Lambda_n and define

\[
 W_r=R_n-p_r(A_n)+p_r(d)\Pi_n.
\]

On the constant vector, W_r is zero. On its orthogonal complement, it is the polynomial approximation error for 1/(d-x). The spectral theorem and (11) imply

\[
 \|W_r\|^2\le C_dq^{-r}.                                  \tag{12}
\]

If graph distance between c and x exceeds r, every walk of length at most r from c to x is absent. Since p_r has degree at most r,

\[
 p_r(A_n)_{cx}=0.
\]

This includes disconnected vertices if their distance is defined as infinity. The actual identity at every such x is therefore

\[
 (R_n)_{cx}=(W_r)_{cx}-p_r(d)/n.
\]

Using the real inequality (a-b) squared <=2a squared+2b squared, summing over the far vertices, and using the norm of one row of W_r,

\[
 \begin{split}
 \sum_{x:\operatorname{dist}(c,x)>r}|(R_n)_{cx}|^2
 &\le2\sum_x|(W_r)_{cx}|^2+2p_r(d)^2/n\\
 &\le C_d\left(q^{-r}+\frac{(r+1)^2}{n}\right).
 \end{split}                                               \tag{13}
\]

The stationary term is retained exactly. A sum of its absolute entries would cost order r, while its squared row mass costs only order r squared divided by n. Equation (13) is pointwise on N_n and uniform over all root vertices c in that one graph.

## 4. Sampling predetermined labels by exchangeability

The law of the host is invariant under every permutation of its labels. The event N_n, graph distance and the full centered resolvent transform covariantly under the same permutation.

For any two distinct predetermined labels c,b, permutations fixing c show that

\[
 \begin{split}
 &\mathbb E\left[
 \mathbf1_{\mathcal N_n}\mathbf1_{\{\operatorname{dist}(c,b)>r\}}
 |(R_n)_{cb}|^2\right]\\
 &\quad=\frac1{n-1}\mathbb E\left[
 \mathbf1_{\mathcal N_n}
 \sum_{x\ne c}\mathbf1_{\{\operatorname{dist}(c,x)>r\}}
 |(R_n)_{cx}|^2\right]\\
 &\quad\le\frac{C_d}{n-1}
 \left(q^{-r}+\frac{(r+1)^2}{n}\right).
 \end{split}                                               \tag{14}
\]

No independence of entries is used. This is an unconditional expectation with a label-invariant event included in the integrand, not an unsupported symmetry assumption after selecting marks from the graph.

Let F_(E,r) be the m by m matrix whose off-diagonal entry i,j is

\[
 \mathbf1_{\mathcal N_n}
 \mathbf1_{\{\operatorname{dist}(c_i,c_j)>r\}}
 (R_n)_{c_ic_j},
\]

and whose diagonal entries are zero. Summing (14) over the ordered distinct pairs gives

\[
 \mathbb E\|F_{E,r}\|_{\mathrm F}^2
 \le\frac{C_dm(m-1)}{n-1}
 \left(q^{-r}+\frac{(r+1)^2}{n}\right).                    \tag{15}
\]

The operator norm is bounded by the Frobenius norm.

There is also a direct bound for close pairs. A graph of maximum degree d has at most

\[
 1+d\frac{q^r-1}{q-1}
\]

vertices within distance r of any root. Label symmetry and a union bound therefore give

\[
 \begin{split}
 \mathbb P(\mathcal C_{E,r})
 &\le\frac{m(m-1)}2\frac{d(q^r-1)}{(q-1)(n-1)}\\
 &\le C_d\frac{m^2q^r}{n},
 \end{split}                                               \tag{16}
\]

where C_(E,r) is the event that at least one distinct marked pair is at distance at most r. This estimate requires no spectral input and no conditioning on N_n.

On N_n outside C_(E,r), the off-diagonal part of G_(E_n)(d) equals F_(E,r). By Markov's inequality applied to its squared Frobenius norm, (15), (16) imply

\[
 \begin{split}
 &\mathbb P\bigl(\|\operatorname{offdiag}(G_{E_n}(d))\|>
 \eta s_n,\ \mathcal N_n\bigr)\\
 &\quad\le C_d\frac{m^2q^r}{n}
 +C_d\eta^{-2}m\left(q^{-r}+\frac{(r+1)^2}{n}\right),
 \end{split}                                               \tag{17}
\]

for all sufficiently large n. The factor n/(n-1) is absorbed into the constant.

Choose the integer

\[
 r=\left\lfloor\log_q\sqrt{n/m}\right\rfloor.
                                                                    \tag{18}
\]

For 1<=m<=n^(1/3) and all sufficiently large n, it satisfies (10) and is nonnegative. Moreover,

\[
 q^r\le1/s_n,\qquad q^{-r}\le q s_n.
\]

Thus (17) becomes

\[
 \begin{split}
 &\mathbb P\bigl(\|\operatorname{offdiag}(G_{E_n}(d))\|>
 \eta s_n,\ \mathcal N_n\bigr)\\
 &\quad\le C_d\left[
 (1+\eta^{-2})\sqrt{m^3/n}
 +\eta^{-2}\frac{m(\log n)^2}{n}\right].
 \end{split}                                               \tag{19}
\]

This is the step that removes the logarithm from the growth condition. It discards rare close marked pairs and measures all remaining interactions by squared mass rather than their total absolute sum.

## 5. Diagonal control and completion of the value estimate

Use the fixed rho selected in Section 1. Let rho_0=2 sqrt(q)/d and choose L=C log(n), rounded up, with a fixed C large enough that both rho^(L+1) and rho_0^(L+1) are O(n^(-4)). For sufficiently large n, L<=nd/4.

For a fixed labelled vertex c, let p_k(c,c) be the simple random-walk return probability and let p_k^T be its infinite-tree counterpart. The accepted single-walk estimate gives nonnegative excess D_k(c)=p_k(c,c)-p_k^T and

\[
 \mathbb E_{\rm simp}D_k(c)
 \le\frac{2k(k+1)}{\alpha_{n,d}n},                          \tag{20}
\]

where alpha_(n,d) is the simplicity probability and is bounded below by a positive constant for fixed d. Equation (20) is the previously reviewed configuration exposure and conditioning estimate. It is used here only for diagonal entries.

The projected random-walk series, including its k=0 stationary subtraction, gives on the fixed host-gap event

\[
 |(R_n)_{cc}-g_d(d)|
 \le\frac1d\sum_{k=0}^LD_k(c)+\frac{L+1}{dn}+C_dn^{-4}.
                                                                    \tag{21}
\]

Let Delta_E denote the diagonal matrix with entries (R_n)_(c_i c_i)-g_d(d). Sum (21) over all m marks and use the diagonal operator norm bound by that absolute sum. The random nonnegative sum has expectation at most C_d mL cubed divided by n, by (20). The remaining deterministic contribution is at most C_d(mL/n+mn^(-4)). Consequently, for every fixed eta>0, uniformly for 1<=m<=n^(1/3) and all sufficiently large n,

\[
 \mathbb P(\|\Delta_E\|>\eta s_n,\ \mathcal N_n)
 \le C_d\eta^{-1}\sqrt{m/n}(\log n)^3.                     \tag{22}
\]

To justify the threshold explicitly, divide the deterministic contribution by s_n. It is at most C_d(n^(-1/3)log(n)+n^(-10/3)), uniformly in that m range, and therefore is eventually less than eta/2. Markov's inequality then applies with the remaining eta s_n/2 budget. The precise negative power in the negligible last term is not needed.

The operator G_(E_n)(d)-g_d(d)I_m is the sum of Delta_E and its off-diagonal part. Combining (19), (22), and P(N_n complement)<=n^(-xi) proves (4).

If m cubed divided by n tends to zero, then m<=n^(1/3) eventually. Every term on the right of (4) tends to zero. Indeed, m(log n) squared/n<=n^(-2/3)(log n) squared, and sqrt(m/n)(log n) cubed<=n^(-1/3)(log n) cubed. This proves (1).

## 6. Derivative estimate

The derivative estimate does not need the new polynomial argument. The earlier finite-n marked-resolvent theorem, applied with derivative order one and a logarithmic random-walk cutoff, already gives

\[
 \|G_{E_n}'(d)-g_d'(d)I_m\|
 =O_{\mathbb P}\left(
 \frac{m(\log n)^4+m(m-1)(\log n)^2}{n}
 +(\log n)n^{-4}\right).                                  \tag{23}
\]

This is equation (25) of the frozen probability proof, whose finite-n theorem holds for every deterministic marked set. It was not restricted to the older collective-scale range.

Under m cubed divided by n tending to zero, each term in (23) tends to zero. The tree derivative is

\[
 g_d'(d)=-\frac{(d-1)((d-1)^2+1)}{d^2(d-2)^3}.
\]

This proves (2). The same reasoning gives convergence of every fixed derivative order under the new range. The existing dimension-free local Taylor bounds and the marked-edge estimate d m(m-1)/(2(n-1)) continue to hold. No new application of the deterministic eigenvalue transfer is asserted by this probability proof alone.

## 7. Limits, dependencies and handoff

The proof does not show that m cubed divided by n tending to zero is necessary. It does not prove an actual graph eigenvalue obstruction at the boundary. The close-pair event is only removed in the upper argument, not analyzed as a sufficient spectral witness.

The stronger host-spectrum input is substantive. A merely fixed spectral interval strictly below d gives an approximation decay rate that need not match q^(-r/2). It would not justify equation (11) at the required scale. This proof uses the published bound (3) to close exactly that issue. The coordinator's separate nonbacktracking approach seeks to avoid this additional quantitative input and is not a premise here.

The previous frozen probability proof has SHA256

`56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b`.

Its single-walk estimate, simplicity input, derivative estimate and local Taylor bound are the only earlier project results used. The new external input is equation (2) of Charles Bordenave, A new proof of Friedman's second eigenvalue theorem and its extension to random lifts, Annales scientifiques de l'Ecole Normale Superieure, volume 53, 2020, pages 1393 to 1439. The retained published PDF and extracted text are in mathathon/spectral-gap/manuscript-round-01/presubmission-01/sources.

Requested review: reconstruct the Chebyshev normalization and p_r(d), the stationary correction in the far-row squared bound, the exchangeability identity with N_n included, and the two uses of the radius (18). The main application output is (1), (2) under m cubed divided by n tending to zero. Any correction should create a new frozen revision.
