# Growing marked sets at the Perron resolvent

Date: November 15, 2026, America/Los_Angeles.

Status: complete paper proof, frozen as revision 1 for separate review. This file does not promote a canonical claim and does not claim formal verification or historical firstness.

Owner: probability workstream. Integrator: root coordinator. This attempt read the frozen SG-17 replacement and the current problem packet. It did not read another new proof attempt before freezing. The deterministic transfer and priority comparison are separate workstreams.

## 1. Exact objects and inputs

Fix an integer d>=3. Let n tend through integers with nd even and n>=d+1. Let A=A_n be the adjacency matrix of a uniformly sampled simple labelled d-regular graph on [n]. Write

\[
 P=A/d,\qquad u=n^{-1/2}\mathbf1,\qquad
 \Pi=uu^\top,\qquad Q=I-\Pi.
\]

For each n, choose m=m(n) distinct labels c_1,...,c_m deterministically before sampling the graph, with 1<=m<=n, and put

\[
 E=(e_{c_1},\ldots,e_{c_m}),\qquad J_m=\mathbf1_m\mathbf1_m^\top.
\]

All norms below are Euclidean operator norms. The bounds are independent of the particular deterministic labels. They are not simultaneous assertions over all subsets of a sampled graph.

Let alpha_(n,d) be the probability that the d-regular configuration model is simple. For all sufficiently large admissible n,

\[
 \alpha_{n,d}\ge a_d>0.                                      \tag{1}
\]

Conditioning that model on simplicity gives exactly the uniform simple labelled graph law. The retained counting source, Corollary 1.2 and equations (1.15), (1.16), supplies (1). Every simple labelled d-regular graph corresponds to exactly (d!)^n labelled half-edge pairings.

Choose a fixed rho with

\[
 \rho_0:=\frac{2\sqrt{d-1}}d<\rho<1,
 \qquad \mathcal H_n=\{\|A-d\Pi\|\le d\rho\}.
\]

The published two-sided random regular graph spectral-gap theorem supplies

\[
 \mathbb P(\mathcal H_n^c)\longrightarrow0.                  \tag{2}
\]

No quantitative rate for (2) is used or claimed. The finite-n bound below is also valid for any fixed 0<rho<1 if its actual exceptional probability is retained.

On the event H_n, define the marked projected resolvent

\[
 G_E(z)=E^\top Q(zI-A|_{u^\perp})^{-1}QE.                    \tag{3}
\]

Its derivatives are derivatives in z. Define these quantities as zero off H_n for statements about probability. Inverses and deterministic identities are used only on H_n. That event forces connectedness and keeps the spectrum of A restricted to u-perpendicular inside [-d rho,d rho].

Let T_d be the infinite d-regular tree and let

\[
 p_k^{\mathcal T}=\mathbb P_o(X_k=o),\qquad
 g_d(z)=\langle\delta_o,(zI-A_{\mathcal T_d})^{-1}\delta_o\rangle.
\]

The tree adjacency norm is at most 2 sqrt(d-1). One direct upper bound orients every edge towards a fixed end. Each vertex then has one parent and d-1 children. The operator that sums values over children has norm sqrt(d-1), and adjacency is this operator plus its adjoint. In particular,

\[
 0\le p_k^{\mathcal T}\le\rho_0^k.                          \tag{4}
\]

The scalar quantities needed for the application are

\[
 g_d(d)=\frac{d-1}{d(d-2)},\qquad
 g_d'(d)=-\frac{(d-1)((d-1)^2+1)}{d^2(d-2)^3}.              \tag{5}
\]

The proof of (5) is included in Section 6.

## 2. Finite-n marked-resolvent theorem

For an integer j>=0, write

\[
 w_j(k)=\binom{k+j}{j},\qquad a_j=\frac{j!}{d^{j+1}}.
\]

For an integer 0<=L<=nd/4, define

\[
 B_{j,L}=\sum_{k=0}^Lw_j(k)=\binom{L+j+1}{j+1},             \tag{6}
\]

\[
 S_{j,L}=\sum_{k=0}^Lw_j(k)k(k+1)
 =(j+1)(j+2)\binom{L+j+1}{j+3}
   +2(j+1)\binom{L+j+1}{j+2},                              \tag{7}
\]

where a binomial coefficient is zero when its lower index exceeds its nonnegative upper index. Put

\[
 M_{j,L}=\frac{2m}{\alpha_{n,d}n}S_{j,L}
       +\frac{m(m-1)}{n-1}(B_{j,L}-1),                     \tag{8}
\]

\[
 T_{j,L}=\sum_{k>L}w_j(k)(\rho^k+\rho_0^k).                 \tag{9}
\]

**Theorem 1.** For every t>0,

\[
 \begin{split}
 &\mathbb P\!\left(
 \|G_E^{(j)}(d)-g_d^{(j)}(d)I_m\|
 >a_j\left(t+\frac{mB_{j,L}}n+T_{j,L}\right)\right)\\
 &\hspace{25mm}\le
 \mathbb P(\mathcal H_n^c)+\frac{M_{j,L}}t.
 \end{split}                                               \tag{10}
\]

The right side may be replaced by its minimum with one. The bound needs no independence between marked entries and no conditional expectation given H_n.

The proof occupies Sections 3 through 5.

## 3. Diagonal excess returns

First use the configuration multigraph with its labelled half-edges. A loop contributes two to the adjacency diagonal. Thus choosing an incident half-edge uniformly gives transition matrix A/d even with loops and parallel edges.

For every fixed configuration multigraph and every vertex c,

\[
 D_k(c)=p_k(c,c)-p_k^{\mathcal T}\ge0.                       \tag{11}
\]

Indeed, lift the walk to the universal covering tree rooted above c. Every return to the lifted root projects to a graph return, and graph paths have unique lifts. The uniform incident half-edge choice induces simple random walk on T_d. Distinct loop incidences and parallel edges remain distinct choices. This proves (11) before any averaging.

Expose a uniform pairing only when a walk requests a previously unpaired half-edge. In k steps at most k pairs and k+1 vertices are exposed. Before the first collision, the discovered graph is a tree and its lift is injective. A graph return whose lift does not return to the lifted root therefore requires a collision.

A fresh partner is uniform among all remaining permissible half-edges. At any exposure before step k, at most d(k+1) half-edges lie at discovered vertices and at least nd-2k+1 partners remain. Hence, for k<=nd/4,

\[
 \begin{split}
 0\le\mathbb E_{\rm conf}D_k(c)
 &\le\mathbb P_{\rm conf,walk}(\hbox{a collision by time }k)\\
 &\le\frac{kd(k+1)}{nd-2k+1}
 \le\frac{2k(k+1)}n.                                      \tag{12}
 \end{split}
\]

Previously exposed edges need no fresh pair. Loops and second edges to discovered vertices count as collisions. At k=0 the excess is exactly zero. The expectation in (12) first averages the walk into its return probability, then averages the pairing.

Nonnegativity permits conditioning on simplicity without a signed-error estimate:

\[
 \mathbb E_{\rm simp}D_k(c)
 \le\frac{2k(k+1)}{\alpha_{n,d}n}.                          \tag{13}
\]

This is the single-walk mechanism of the accepted SG-17 replacement. It does not require a radius-k graph ball to be a tree.

## 4. Off-diagonal symmetry and a nonnegative matrix

For distinct deterministic labels c and b, invariance of the uniform simple graph law under every label permutation fixing c shows that E_simp p_k(c,b) has the same value for all b different from c. Row sums of P^k equal one. Therefore the exact identity is

\[
 \mathbb E_{\rm simp}p_k(c,b)
 =\frac{1-\mathbb E_{\rm simp}p_k(c,c)}{n-1}
 \le\frac1{n-1}.                                         \tag{14}
\]

No simplicity factor is needed in (14), since it is proved directly under the simple graph law. At k=0 every off-diagonal entry is zero.

Define the m by m symmetric matrix

\[
 X_{j,L}=\sum_{k=0}^L w_j(k)
       \left(E^\top P^k E-p_k^{\mathcal T}I_m\right).        \tag{15}
\]

Its diagonal entries are weighted excess returns, hence nonnegative by (11). Its off-diagonal entries are sums of nonnegative transition probabilities. Thus X_(j,L) is entrywise nonnegative. Positive semidefiniteness is not asserted or needed.

Let Z_(j,L) be the sum of all entries of X_(j,L). The Frobenius norm is at most this sum, so

\[
 \|X_{j,L}\|\le Z_{j,L},\qquad Z_{j,L}\ge0.                 \tag{16}
\]

Summing (13) over the m diagonal entries and (14) over the m(m-1) ordered off-diagonal pairs gives

\[
 \mathbb E_{\rm simp}Z_{j,L}\le M_{j,L}.                    \tag{17}
\]

The term B_(j,L)-1 in (8) drops the zero off-diagonal contribution at k=0. Equation (7) follows from

\[
 k\binom{k+j}j=(j+1)\binom{k+j}{j+1},
\]

\[
 k(k-1)\binom{k+j}j=(j+1)(j+2)\binom{k+j}{j+2},
\]

the identity k(k+1)=k(k-1)+2k, and the finite binomial summation identity. This also verifies (6).

## 5. Projected series and proof of Theorem 1

On H_n the projected Neumann series and all its fixed-order derivatives converge in operator norm in an open interval around d. They give

\[
 G_E^{(j)}(d)
 =(-1)^j a_j\sum_{k\ge0}w_j(k)
             \left(E^\top P^kE-\frac1nJ_m\right).           \tag{18}
\]

At k=0, the bracket is I_m-J_m/n. The stationary subtraction applies to every k, including zero. Differentiating z^(-k-1) produces the coefficient j! binom(k+j,j), which establishes the sign and normalization in (18).

Similarly, by (4),

\[
 g_d^{(j)}(d)=(-1)^j a_j\sum_{k\ge0}w_j(k)p_k^{\mathcal T}.  \tag{19}
\]

For the truncated difference, equations (15), (18), and (19) give the exact expression

\[
 (-1)^j a_j\left(X_{j,L}-\frac{B_{j,L}}nJ_m\right).          \tag{20}
\]

The stationary matrix has norm mB_(j,L)/n. The host tail is bounded directly as an operator:

\[
 \left\|E^\top(P^k-\Pi)E\right\|
 =\left\|E^\top Q(P|_{u^\perp})^kQE\right\|
 \le\rho^k.                                               \tag{21}
\]

Here E is an isometry, so no factor m appears. Equation (4) bounds the tree tail. Consequently, on H_n,

\[
 \|G_E^{(j)}(d)-g_d^{(j)}(d)I_m\|
 \le a_j\left(Z_{j,L}+\frac{mB_{j,L}}n+T_{j,L}\right).       \tag{22}
\]

Markov's inequality applied to the unconditional nonnegative variable Z_(j,L), using (17), proves (10) after adding P(H_n^c). In particular, the proof never applies the symmetry identity or the pairing estimate under conditioning on H_n. This proves Theorem 1.

## 6. Tree constants and local analytic control

Put q=d-1 and let

\[
 r(z)=\frac{z-\sqrt{z^2-4q}}{2q}
\]

on the real interval z>2 sqrt(q). Decomposing the rooted tree into its d branches gives g_d(z)=1/(z-d r(z)). The relation q r(z)^2-zr(z)+1=0 also gives

\[
 g_d(z)=\frac{r(z)}{1-r(z)^2}.
\]

At z=d one has r(d)=1/(d-1). Differentiating the quadratic relation gives

\[
 r'(d)=-\frac1{(d-1)(d-2)}.
\]

Substitution into g_d and into

\[
 g_d'(z)=r'(z)\frac{1+r(z)^2}{(1-r(z)^2)^2}
\]

proves (5). In particular, g_3(3)=2/3 and g_3'(3)=-10/9.

There is also dimension-free local control. Put delta=d(1-rho)/2. On H_n and |z-d|<=delta,

\[
 \|G_E^{(j)}(z)\|\le\frac{j!}{\delta^{j+1}}.                \tag{23}
\]

This follows from the spectral theorem, the derivative formula for a resolvent and ||QE||<=1. It holds for real z and supplies uniform Taylor remainders on a fixed neighbourhood. For the attachment expression with A_nE on both sides, the corresponding derivative bound gains at most a factor d^2 because ||A_nE||<=d. No entrywise summation is needed for these bounds.

## 7. Consequences for growing marked sets

Fix j. Let ell=log n, let q_*=max(rho,rho_0)<1, and choose

\[
 L=\left\lceil\frac{4\log n}{\log(1/q_*)}\right\rceil.
\]

For all sufficiently large n, L<=nd/4. Equations (6), (7), and (9) imply

\[
 B_{j,L}=O_j(L^{j+1}),\quad S_{j,L}=O_j(L^{j+3}),\quad
 T_{j,L}=O_{j,q_*}(L^j q_*^L)
        =O_{j,q_*}(\ell^j n^{-4}).                          \tag{24}
\]

For the tail bound, write k=L+1+h and bound the degree-j polynomial w_j(k) by a constant times (L+1)^j(h+1)^j, then sum the geometric series with its fixed polynomial weight.

Theorem 1, (1), and (2) now yield

\[
 \|G_E^{(j)}(d)-g_d^{(j)}(d)I_m\|
 =O_{\mathbb P}\!\left(
 \frac{m\ell^{j+3}+m(m-1)\ell^{j+1}}n
 +\ell^j n^{-4}\right).                                   \tag{25}
\]

The m ell^(j+1)/n stationary term is absorbed by the first term. To justify the O_P notation, apply (10) with t a large constant times the deterministic order of M_(j,L). The exceptional probability tends to zero independently of that order. Zero extension off H_n therefore does not require a rate for (2).

More generally, for any positive scale b_n, (10) proves an o_P(b_n) statement whenever the deterministic quantity M_(j,L)+mB_(j,L)/n+T_(j,L) is o(b_n) and (2) holds. This form allows other truncations and scales without changing the argument.

**Corollary 2, collective scale.** Suppose

\[
 \frac{m^3(\log n)^2}{n}\longrightarrow0,
 \qquad s_n=\sqrt{m/n}.                                   \tag{26}
\]

Then for every fixed d>=3,

\[
 \left\|G_E(d)-\frac{d-1}{d(d-2)}I_m\right\|
 =o_{\mathbb P}(s_n),                                     \tag{27}
\]

and for every fixed integer j>=1,

\[
 \|G_E^{(j)}(d)-g_d^{(j)}(d)I_m\|
 \xrightarrow{\mathbb P}0.                                \tag{28}
\]

For (27), divide (25) at j=0 by s_n. The resulting terms are bounded by constants times

\[
 \sqrt{m/n}\,\ell^3,
 \quad\frac{m^{3/2}\ell}{\sqrt n},
 \quad\frac{n^{-4}}{s_n}.                                 \tag{29}
\]

The middle term tends to zero by (26). That hypothesis also implies m<=n^(1/3) eventually. The first term is then at most n^(-1/3) ell^3 and tends to zero. Since m>=1, the last term is at most n^(-7/2). For (28), use m<=n^(1/3) in (25). Every fixed logarithmic power is dominated by the remaining negative power of n. This proves the corollary.

Condition (26) is equivalent to

\[
 m=o\!\left(\left(\frac n{(\log n)^2}\right)^{1/3}\right).
\]

It contains every sequence 1<=m(n)<=n^(1/3-epsilon) for fixed 0<epsilon<1/3, without requiring m to tend to infinity. At d=3, equations (27) and (28) for j=1 are exactly R1 and R2 of the problem packet.

For reference, a separate consequence of (25) is convergence of the j-th derivative in operator norm whenever m=o(sqrt(n)/(log n)^((j+1)/2)). This weaker precision statement is not enough by itself for (27) or for critical spectral splitting.

## 8. Absence of marked host edges

Uniformity of the simple regular graph law gives

\[
 \mathbb P(\{c_i,c_h\}\in E(G_n))=\frac d{n-1}
 \quad(i\ne h).
\]

Hence

\[
 \mathbb P(E^\top A_nE\ne0)
 \le\frac{dm(m-1)}{2(n-1)}.                               \tag{30}
\]

Under (26), the right side tends to zero. This event is intersected with the good resolvent event after proving the unconditional estimates. Rare adjacency among predetermined labels is part of the original model, not a forbidden graph configuration. No graph-dependent choice of labels is covered.

## 9. Scope and handoff

Theorem 1 is a structural bound for every fixed degree, every deterministic marked set and every fixed derivative order. Its logarithmic corollaries concern a growing marked set, not a uniform maximum over all possible sets in one graph. The proof does not supply an optimal growth threshold, a limit distribution of residual errors, a bulk-edge local law, or occurrence probabilities for deliberately inserted defects.

The power 1/3 has a plausible geometric interpretation through the nearest marked pair, but that interpretation is not proved here and is not an input. The logarithmic loss in (26) may reflect the entry-sum bound. Neither its removal nor a converse is asserted.

For the integrator, the usable output is (27), (28) at j=1, the dimension-free Taylor bound (23), and the no-marked-edge probability (30). These hold jointly with H_n with probability tending to one. The deterministic reduction must still justify all roots, their multiplicities and their ordering. This proof alone makes no augmented-graph eigenvalue assertion.

The next action is a separate exact-revision review of (11) through (22), then integration with the deterministic transfer. In particular, review should check the tree-cover convention, conditioning on simplicity, off-diagonal symmetry, stationary subtraction and growing-dimension operator tail.

## 10. Evidence anchors

| Input | Exact identity |
| --- | --- |
| Current problem packet, mathathon/spectral-gap/research-direction-2026-11-14/NEXT_PROBLEM.md | SHA256 0575afeaf42b43693ffbff4e2f3f20afb9386b52f49404d8e2753434917a55f8 |
| Accepted SG-17 replacement, spectral-reconciliation-2026-11-14/remote-intake/CRITICAL_SCALE_AUDIT.md | SHA256 0ddd92d7a8871e0e4c5da6d6acb51964764f5ffbdf22b68f43204bd6f4ae8e0d |
| Separate SG-17 review, spectral-reconciliation-2026-11-14/remote-intake/CRITICAL_SCALE_REVIEW.md | SHA256 ea11d33adb67787b056680cf0b726e3619d3392c90213805866570e19d273992 |
| Host-gap input | Bordenave, published Theorem 1, retained text in mathathon/spectral-gap/manuscript-round-01/presubmission-01/sources/bordenave-published.txt, inspected lines 125 through 165 |
| Simplicity input | Angel, van der Hofstad and Holmgren, Corollary 1.2 and equations (1.15), (1.16), retained text in mathathon/spectral-gap/snapshot/.ultramath/smwgwbyn9/m6/papers/avhh.txt, inspected lines 180 through 235 |

The primary source passages were read locally in this round. Their full proofs were not re-audited. No numerical experiment is a premise of this proof.
