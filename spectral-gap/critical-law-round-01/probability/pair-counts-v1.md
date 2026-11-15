# The critical marked-pair point process

Date: November 15, 2026, America/Los_Angeles.

Status: complete paper proof, frozen as revision 1 for separate review. No canonical claim is promoted by this file. This is a geometric probability theorem, not a spectral theorem or a historical-priority claim.

Owner: probability workstream. The coordinator independently suggested the same conditional-host factorial-moment route while this argument was being developed. Prior exposure also includes the earlier two-walk upper proof. No effective-operator attempt or new obstruction proof was read before this revision was frozen. Shared development of the route is not independent-review evidence.

## 1. Exact model and theorem

Fix an integer d>=3 and put q=d-1. Let G_n be uniform among simple labelled d-regular graphs on n vertices, with nd even. Fix a deterministic set M_n of m=m(n) distinct labels before sampling G_n. Assume

\[
 m/n^{1/3}\longrightarrow c\in(0,\infty).
\]

Define

\[
 s_n=\sqrt{m/n},\qquad
 r_n=\lfloor\log_q(1/s_n)\rfloor,\qquad
 \phi_n=\log_q(1/s_n)-r_n.
\]

Work along a subsequence on which phi_n tends to phi in [0,1]. A fractional part can converge to one from below, so that endpoint is included. Changing between phase endpoints reindexes the integer offsets.

For each fixed integer k, let

\[
 Z_{n,k}=\#\bigl\{\{a,b\}\subset M_n:
              \operatorname{dist}_{G_n}(a,b)=r_n+k\bigr\}.
\]

Pairs are unordered and distinct. Disconnected vertices have distance infinity. For sufficiently large n, every distance in any prescribed finite offset set is positive.

**Theorem 1, joint geometric law.** For every finite set J of integer offsets, the vector (Z_(n,k))_(k in J) converges in distribution to independent Poisson variables with means

\[
 \lambda_k=\frac{d}{2q}\,c^{3/2}q^{k-\phi}.                \tag{1}
\]

For every fixed integer K, the count of marked pairs at distance at most R_n=r_n+K converges to Poisson with mean

\[
 \Lambda_K=\frac{d}{2(q-1)}\,c^{3/2}q^{K-\phi}
           =\sum_{k\le K}\lambda_k.                       \tag{2}
\]

Joint versions hold for disjoint distance bands with fixed integer offset endpoints. The lowest band may instead contain all positive distances up to r_n+K_0 for a fixed integer K_0. Their means are the corresponding sums of (1). In particular, the finite offset counts and their lower tail are consistent with a Poisson point process on the integer offsets.

**Theorem 2, geometry at each fixed cutoff.** Fix K and put R_n=r_n+K. With probability tending to one:

1. The graph on M_n that joins marks at distance at most R_n is a matching.
2. Every pair of distinct marks has at most one nonbacktracking incidence path of length between one and R_n.
3. Every path counted in the second assertion is simple and realizes the graph distance. The paths for different edges of the matching are vertex-disjoint and have no other marked vertices in their interiors.

For fixed d,c,K, matching failure has probability O(n^(-1/3)), while failure of the second assertion has probability O(n^(-2/3)(log n)^2). No host spectral theorem is used in either theorem. The only configuration-model input is a fixed positive lower bound for the simplicity probability, together with the elementary exploration arguments given below.

## 2. Predetermined labels and an independent uniform marked set

For every two deterministic m-element subsets M and M' of [n], a label permutation maps M to M'. The uniform simple regular graph law is invariant under that permutation. Therefore every statistic considered here has the same law for every predetermined set M.

It follows that its law also equals the law obtained by first sampling G_n and then independently choosing S_n uniformly among its m-element vertex subsets. This is an exact equality of distributions, not an assumption that the original marks were sampled from the observed graph. It permits conditional calculations on the host with a uniform marked subset.

Conditioning the regular configuration model on simplicity produces the uniform simple labelled graph law, since every such graph has exactly (d!)^n half-edge realizations. Write alpha_(n,d) for the simplicity probability. For fixed d,

\[
 \alpha_{n,d}\ge a_d>0                                    \tag{3}
\]

for all sufficiently large admissible n. This is the same previously inspected primary-source input used in the earlier marked-resolvent proof. The source is Angel, van der Hofstad and Holmgren, Corollary 1.2 and equations (1.15), (1.16), retained in the spectral topic's source archive.

## 3. Tree-sized distance spheres at almost every host vertex

Let R=R_n=r_n+K. Then R=O(log n), R tends to infinity, and

\[
 q^R=q^{K-\phi_n}/s_n=\Theta(n^{1/3}),\qquad
 q^{2R}/n=O(n^{-1/3}).                                    \tag{4}
\]

These bounds hold with constants depending on d,c,K.

Explore the configuration model breadth first from a fixed root, revealing all pairings needed to determine its vertices at distance at most R. Pairings need only be requested from vertices at distance less than R. At most C_d q^R vertices and half-edge pairs are involved. At any fresh pairing, the partner is uniform among the remaining half-edges. The probability that it belongs to an already discovered vertex is at most C_d q^R/n while the exploration remains within this deterministic size bound. The denominator is at least nd/2 for all sufficiently large n.

A union bound over the fresh pairings gives

\[
 \mathbb P_{\rm conf}(\text{a collision in this exploration})
 \le C_d q^{2R}/n.                                       \tag{5}
\]

Loops and parallel edges are collisions. If no collision occurs, the root has exactly

\[
 a_\ell=dq^{\ell-1}
\]

vertices at each distance 1<=ell<=R. This conclusion does not require exposing edges between two boundary vertices at distance R. Such an edge cannot shorten their distance to the root.

By conditioning the nonnegative collision indicator on simplicity, (3) and (5) give the same bound, with another d-dependent constant, in the simple graph. Let B_n be the number of roots whose breadth-first exploration has a collision. Then

\[
 \mathbb E(B_n/n)\le C_d q^{2R}/n\longrightarrow0.          \tag{6}
\]

For any graph of maximum degree d, every distance-ell sphere has at most a_ell vertices. Thus if e_(n,ell) denotes the number of unordered vertex pairs at distance exactly ell,

\[
 (n-B_n)a_\ell\le2e_{n,\ell}\le n a_\ell
 \quad(1\le\ell\le R).                                   \tag{7}
\]

In particular,

\[
 \sup_{1\le\ell\le R}
 \left|\frac{2e_{n,\ell}}{n d q^{\ell-1}}-1\right|
 \xrightarrow{\mathbb P}0.                               \tag{8}
\]

The same argument applied to whole balls gives, for the number e_(n,<=R) of unordered pairs at positive distance at most R,

\[
 e_{n,\le R}
 =(1+o_{\mathbb P}(1))\frac n2\frac{d(q^R-1)}{q-1}.        \tag{9}
\]

The auxiliary graph joining vertices at positive distance at most R has deterministic maximum degree at most

\[
 \Delta_n=\frac{d(q^R-1)}{q-1}=O(n^{1/3}).                 \tag{10}
\]

This is where simplicity conditioning is handled for the sphere counts. The eventual Poisson law is proved directly under the simple host law. It is not obtained by dividing an unconditioned Poisson probability by the simplicity probability.

## 4. A finite sampling lemma that proves Poisson independence

The next statement is deterministic in the host and applies to graphs other than distance graphs.

**Lemma 3.** For each n, let a simple graph on n vertices have edges partitioned into a fixed finite number of colours. Let Delta_n>=1 bound its maximum degree, let e_(n,j) be the number of edges of colour j, and independently choose a uniform m-element vertex subset. Suppose m tends to infinity, p=m/n, and

\[
 n\Delta_n p^2\le B_0<\infty.                             \tag{11}
\]

Let X_(n,j) count the edges of colour j with both endpoints selected. For every fixed tuple of nonnegative integers t_j, uniformly over all such coloured host graphs,

\[
 \mathbb E\prod_j(X_{n,j})_{t_j}
 =\prod_j(e_{n,j}p^2)^{t_j}+O_{B_0,(t_j)}(1/m).            \tag{12}
\]

Here (x)_t is the falling factorial. In particular, if e_(n,j)p squared tends to lambda_j for each j, then the colour counts converge jointly to independent Poisson variables with those means.

**Proof of the factorial-moment estimate.** Put h=sum_j t_j. The case h=0 is immediate. Expand the left side into ordered tuples of h edges, with their prescribed colours. Within each colour the edges are distinct because of the falling factorial. Different colours are disjoint edge sets, so all h edges in each tuple are distinct.

The union of one tuple is a finite simple graph with v vertices and b nontrivial connected components. There are no isolated vertices. For fixed h there are finitely many possible incidence patterns, including the edge order and colours. Each pattern has at most

\[
 C_h n^b\Delta_n^{v-b}                                    \tag{13}
\]

embeddings in the host. Choose one root per component in at most n ways, choose a spanning tree of each fixed pattern, and embed each remaining vertex along a host edge in at most Delta_n ways. Extra-edge, colour and injectivity constraints only reduce the count.

The probability that all v distinct endpoints are in the uniform marked set is exactly

\[
 p_v=\frac{(m)_v}{(n)_v}.                                 \tag{14}
\]

For fixed h and sufficiently large n, this is at most C_h p^v. Also

\[
 \Delta_n p=(n\Delta_np^2)/m\le B_0/m.                    \tag{15}
\]

If the edge tuple is not a matching, at least one component has three or more vertices, so v-2b>=1. Combining (13) through (15), its entire pattern contributes at most

\[
 C_h n^b\Delta_n^{v-b}p^v
 =C_h(n\Delta_np^2)^b(\Delta_np)^{v-2b}
 =O_{h,B_0}(1/m).                                        \tag{16}
\]

Summing over the finitely many patterns preserves this bound. This controls shared marked vertices, cycles among selected auxiliary edges and every higher overlap pattern. It does not assume their independence.

The number of all edge tuples, ignoring whether their endpoints overlap, is

\[
 N_{\rm all}=\prod_j(e_{n,j})_{t_j}.
\]

Every matching tuple has 2h distinct vertices and inclusion probability p_(2h). Since p_v>=p_(2h) for v<=2h, replacing the actual probability of every nonmatching tuple by p_(2h) changes the total expectation by at most the nonmatching contribution (16). Hence

\[
 \mathbb E\prod_j(X_{n,j})_{t_j}
 =N_{\rm all}p_{2h}+O_{h,B_0}(1/m).                       \tag{17}
\]

One has p_(2h)/p^(2h)=1+O_h(1/m), since m tends to infinity and n>=m. Also e_(n,j)p squared<=B_0/2 by (11). Expanding each fixed falling factorial as a polynomial shows

\[
 (e_{n,j})_{t_j}p^{2t_j}
 =(e_{n,j}p^2)^{t_j}+O_{h,B_0}(p^2).
\]

Condition (11), with Delta_n>=1, gives p squared<=B_0/n=O(1/m). Substitution in (17) proves (12).

**Why the moments determine the joint law.** The first moments give tightness. Formula (12) for every fixed order gives bounded moments of every fixed order for the total count. These bounds give uniform integrability of all mixed factorial moments, using a higher fixed moment to dominate each one. Every subsequential distributional limit therefore has mixed factorial moments equal to the products of the corresponding Poisson means.

For such a limit vector Y, Tonelli's theorem applied to the finite binomial expansion for each integer-valued coordinate gives

\[
 \mathbb E\prod_j(1+t_j)^{Y_j}
 =\sum_{(r_j)}\prod_j\frac{\lambda_j^{r_j}t_j^{r_j}}{r_j!}
 =\exp\!\left(\sum_j\lambda_jt_j\right)
 \quad(t_j\ge0).
\]

In particular, E 2^(sum_j Y_j) is finite. Thus the same expansion is absolutely integrable for -1<=t_j<=0. It yields the joint probability generating function exp(sum_j lambda_j(z_j-1)) for 0<=z_j<=1. This is exactly the generating function of independent Poisson variables. Every subsequential limit is the same, which proves the lemma.

## 5. Application to critical distance colours

Take a finite set J of integer offsets and K=max J. On each realized simple host, give colour k to the unordered vertex pairs at distance r_n+k. Distinct distance colours are disjoint edge sets. Their union is a subgraph of the auxiliary graph in (10).

For p=m/n, equations (4), (10) and the critical assumption give

\[
 n\Delta_np^2
 \le C_d\frac{m^2q^{r_n+K}}n
 =C_d\frac{m^{3/2}}{\sqrt n}q^{K-\phi_n}=O(1).             \tag{18}
\]

By (8), the colour-edge means satisfy

\[
 \begin{split}
 e_{n,r_n+k}p^2
 &=(1+o_{\mathbb P}(1))\frac{d}{2q}\frac{m^2}{n}q^{r_n+k}\\
 &=(1+o_{\mathbb P}(1))\frac{d}{2q}
       \frac{m^{3/2}}{\sqrt n}q^{k-\phi_n}
 \xrightarrow{\mathbb P}\lambda_k.
 \end{split}                                               \tag{19}
\]

All these means are deterministically bounded by (18). Conditional on the host, Lemma 3 gives its uniform mixed factorial-moment estimate. Taking the expectation over the host in (12), the bounded means in (19) converge in expectation as well as in probability. Therefore the unconditional mixed factorial moments tend to the required products. The joint-law argument from Lemma 3 proves Theorem 1 for finite offset sets.

For the cumulative count at cutoff K, use the single auxiliary colour consisting of every pair at positive distance at most r_n+K. Its edge count is given by (9). Its mean after marking tends to

\[
 \frac{d}{2(q-1)}\frac{m^{3/2}}{\sqrt n}q^{K-\phi_n}
 \longrightarrow\Lambda_K,
\]

because q^(r_n+K) tends to infinity. The same lemma proves (2). Giving different colours to disjoint bands with fixed offset endpoints proves the joint band version. For example, one colour may contain all distances from one to r_n+K_0, with separate colours for finitely many larger integer offsets.

For completeness, the expected number of pairs with offset at most -L is at most C_(d,c) q^(-L), uniformly for sufficiently large n. This follows directly from the deterministic ball-volume bound and label symmetry. It also follows by taking K=-L in the bounded first-moment calculation. Hence the lower offset tail can be removed uniformly before sending L to infinity.

The identities in (19) verify the constant d/(2q), the power c^(3/2), and the sign of the phase factor. The limit at phi=1 is the limit at phi=0 with the integer offsets shifted by one.

## 6. Shared marks and disjoint short geometry

Let H_R be the auxiliary graph joining host vertices at positive distance at most R=r_n+K. Conditional on the host, its number of ordered wedges is at most n Delta_n squared. A particular wedge uses three distinct vertices. Under a uniform m-subset, the probability that all three are marked is (m)_3/(n)_3. Therefore

\[
 \mathbb P(H_R[M_n]\text{ is not a matching})
 \le C\frac{m^3\Delta_n^2}{n^2}
 \le C_d\frac{m^3q^{2R}}{n^2}
 =O(n^{-1/3}).                                           \tag{20}
\]

This calculation is valid for every simple host and then for the original predetermined labels by Section 2. It needs neither an independent-edge approximation nor a tree event.

There is a deterministic geometric consequence of matching. Suppose two paths of length at most R, with four distinct marked endpoints, intersect at a vertex x. From each path choose an endpoint at path distance at most R/2 from x. Those two marks have graph distance at most R, producing a cross edge in H_R[M_n]. The original two short pair edges together with that cross edge cannot form a matching. Thus paths belonging to different edges of a matching cannot intersect.

Likewise, if another marked vertex lies inside a path of length at most R between marks, its distances to both endpoints are at most R. The resulting short-pair graph is not a matching. This proves the disjointness and absence of interior marks once existence and uniqueness of the short paths have been established.

## 7. Alternative paths and cycles

Let N_l(u,v) count nonbacktracking incidence paths of length l in a d-regular configuration multigraph. There are exactly a_l=dq^(l-1) such paths from each root for l>=1. Incidences distinguish loop orientations and parallel edges.

Fix positive r,t with r,t<=R. Independently sample a uniform nonbacktracking incidence path of length r and one of length t from the same root. Reveal their required pairings, first one path and then the other. At most r+t pairs and r+t+1 vertices are discovered. A fresh partner remains uniform among the unmatched half-edges conditional on all prior discoveries and path choices.

For all sufficiently large n, the probability of an accidental pairing to an already discovered vertex is at most

\[
 C_d(r+t)^2/n.                                           \tag{21}
\]

For example, the union bound uses denominator nd-2(r+t)-1 and at most d(r+t+1) discovered half-edges at each of r+t requests. Since R=O(log n), that denominator is at least nd/2 eventually. Previously exposed edges require no new pair. Loops and extra parallel edges are included in the accidental-collision event.

If no such collision occurs, the revealed graph is a tree. Two nonbacktracking paths from its root with the same endpoint must have the same length and identical incidence sequence. Therefore endpoint coincidence by two distinct paths is contained in the accidental-collision event, also when r and t differ.

For r=t, the probability that the second path follows the exact first incidence sequence is 1/a_r, conditional on the full configuration and first path. No conditioning on collision-freeness is used in this statement. It follows that

\[
 \mathbb E_{\rm conf}\sum_{u,v}
 \left(N_r(u,v)N_t(u,v)-\mathbf1_{\{r=t\}}N_r(u,v)\right)
 \le C_d(r+t)^2a_ra_t.                                   \tag{22}
\]

The left side counts ordered distinct paths with common endpoints. It is nonnegative. Conditioning on simplicity therefore costs only the fixed factor from (3). Summing (22) over r,t from one to R gives

\[
 \mathbb E_{\rm simp}\sum_{u,v}
 \sum_{r,t=1}^R
 \left(N_r(u,v)N_t(u,v)-\mathbf1_{\{r=t\}}N_r(u,v)\right)
 \le C_dR^2q^{2R}.                                       \tag{23}
\]

Exchangeability of ordered distinct endpoints now gives

\[
 \begin{split}
 &\mathbb P(\text{some distinct marked pair has two different
 nonbacktracking paths of lengths at most }R)\\
 &\quad\le C_d\frac{m(m-1)}{n(n-1)}R^2q^{2R}
 =O(n^{-2/3}(\log n)^2).                                 \tag{24}
 \end{split}
\]

Including diagonal endpoints in the upper sum (23) only increases it, while the sampling factor is applied to the distinct-endpoint part. No path independence is assumed after conditioning on the graph.

If a nonbacktracking path of length at most R between two distinct marks repeated a vertex, erasing its loops would yield a different simple path between the same endpoints, of length at most R. A simple path is nonbacktracking. Hence the no-multiplicity event in (24) forces every such path to be simple. A shorter graph-distance path would also be a second nonbacktracking path, so the unique path is a geodesic.

Every pair at graph distance at most R has at least one geodesic. Thus, on the event complementary to (24), for all distinct marks and all 1<=ell<=R,

\[
 N_\ell(a,b)=\mathbf1_{\{\ell=\operatorname{dist}(a,b)\}}.
                                                                    \tag{25}
\]

Combining this with (20) and the deterministic observations in Section 6 proves Theorem 2. This handles alternative paths, repeated vertices, shared marks and intersections of the realized short paths.

## 8. Scope, source use and requested review

The theorem proves Poisson independence for counts of unordered geometric pairs. It does not claim that a whole signed eigenvalue process is Poisson. A single pair may produce dependent positive and negative spectral effects, and any such spectral correspondence requires its own operator theorem.

The constants and limit law are derived from the exact fixed-degree tree sphere sizes and finite subset probabilities. Simplicity conditioning is used only on nonnegative exploration or path-count bounds. No independence of the simplicity event and a rare pair event is assumed.

The proof uses no current edge universality or quantitative spectral-edge result. The earlier configuration-model simplicity input and the deferred-pairing convention are the same as those in the frozen probability proof with SHA256

`56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b`.

The unequal-length two-walk extension in Section 7 is proved here, rather than imported as a new assumption. The prior equal-length argument is in the frozen nonbacktracking proof with SHA256

`d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896`.

Requested review: inspect the uniform error in Lemma 3, the passage from conditional host moments to the unconditional law, the phase normalization including the endpoint one, and the use of distinct paths in (22) through (25). Review should separately confirm that no final spectral conclusion has been inferred from pair-count convergence alone.
