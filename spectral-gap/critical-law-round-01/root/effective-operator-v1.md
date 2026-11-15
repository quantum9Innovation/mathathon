# Critical reduction to a collective mode and disjoint pair blocks

November 15, 2026. Owner: root. Revision 1, frozen for separate review.

## 1. Model and precise approximation

Fix d>=3, q=d-1 and c>0. Let A_n be a uniform simple labelled d-regular adjacency matrix, with nd even. Choose m predetermined distinct marks, with m/n^(1/3)->c. Let E select them, and set

\[
s=\sqrt{m/n},\quad \theta=ms\longrightarrow c^{3/2},\quad
r_n=\lfloor\log_q(1/s)\rfloor,\quad
\phi_n=\log_q(1/s)-r_n\in[0,1).
\]

The critically weighted augmented adjacency is

\[
\mathcal A=\begin{pmatrix}A_n&\sqrt{d-2}A_nE\\
\sqrt{d-2}E^\top A_n&0\end{pmatrix}.
\]

The cubic case is the unweighted duplication model. Write its eigenvalues in descending order as mu_j. Define

\[
D=\frac{2q^2}{(d-2)^2},\qquad
\kappa=\frac{d(d-2)^{3/2}}{\sqrt2 q},\qquad
h=\frac{d(d-2)^2}{2q}=\frac{dq}{D}.
\]

Fix an integer K>=0 and write R=r_n+K. Define a graph on the marked coordinates by joining a and b if their host distance ell_ab is at most R. Let p_(n,K) be its number of edges. On the event that this graph is a matching and 2p_(n,K)<m, form the multiset

\[
\mathcal Z_{n,K}=
\left\{+\kappa,-\kappa\right\}
\cup\bigcup_{\{a,b\}:\ell_{ab}\le R}
\left\{+h q^{-\ell_{ab}}/s,-h q^{-\ell_{ab}}/s\right\}
\cup\left\{0\text{ with multiplicity }m-2p_{n,K}-1\right\}.
\tag{1}
\]

It has m+1 entries. Outside this event define the ordered vector z_(n,K) to be any deterministic m+1 vector, for example the zero vector. On the event, z_(n,K) is the decreasing ordering of (1).

**Theorem.** For every fixed K the event defining (1) has probability tending to one. For every eta>0,

\[
\limsup_{n\to\infty}
\mathbb P\left\{\max_{1\le j\le m+1}
\left|\frac{\mu_j-d}{s}-z_{n,K,j}\right|>\eta\right\}
\le C_{d,c}\eta^{-2}q^{-K}.
\tag{2}
\]

Constants can additionally depend on a fixed host-gap choice. The exact factor on the right is not optimized. In particular, taking n to infinity first and K to infinity second makes the entire ordered-cluster approximation error vanish in probability.

This theorem is an effective spectral reduction. It does not assume or prove the limiting distribution of the distances. That probability law is supplied separately.

## 2. Earlier inputs and their validity at criticality

Use the [nonbacktracking upper proof](../../close-pair-transition-round-01/root/nonbacktracking-upper-v1.md), SHA256 d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896. Its finite estimates hold before substitution of the subcritical range.

On a fixed two-sided gap event H_n of probability tending to one, let R_Q(d) be the inverse on the host constant vector's orthogonal complement and set G=E^T R_Q(d)E. The tree value is g=q/[d(d-2)]. The earlier diagonal argument gives

\[
\|\operatorname{diag}(G-gI)\|=o_{\mathbb P}(s),            \tag{3}
\]

because the mean bound divided by s is O(s log^3 n). The earlier every-fixed-derivative bound gives

\[
\|G'(d)-g_d'(d)I\|=o_{\mathbb P}(1),                     \tag{4}
\]

since m=O(n^(1/3)). The [cluster-width proof](../../close-pair-transition-round-01/root/cluster-width-v1.md), SHA256 e40164dcf711cca13d945b666645c26aa8095b835e1e727d2d6d7159a78e7b8f, gives

\[
\|G-gI\|=O_{\mathbb P}(s).                               \tag{5}
\]

These are statements under the original simple-graph law, with arbitrary extensions off H_n. No expectation is conditioned on H_n when using the two-walk estimates.

Let N_r count nonbacktracking incidence walks of length r and M_r=q^(-r)N_r. With L=C_0 log n rounded up and C_0 sufficiently large, the exact series and tail bound give

\[
R_Q(d)=g\left[Q+\sum_{r=1}^{L}\left(M_r-\frac dq\Pi\right)\right]
+\mathcal E_L,\qquad \|\mathcal E_L\|\le n^{-4}             \tag{6}
\]

on H_n. For U_(R,L)=sum_(r=R+1)^L M_r, the unconditioned simple-graph estimate is

\[
\mathbb E\|U_{R,L}\|_F^2\le C(nq^{-R}+L^4).              \tag{7}
\]

For fixed K, R<=L for large n.

## 3. Unique short paths between marked vertices

The following minor extension of the two-walk estimate will be used. For lengths r,t>=1 with r+t=O(log n), let a_r=dq^(r-1). In the pairing model,

\[
\mathbb E\sum_{u,v}\left[N_r(u,v)N_t(u,v)
-\mathbf1_{\{r=t\}}N_r(u,v)\right]
\le C_d(r+t)^2a_ra_t.                                    \tag{8}
\]

The expression inside the sum is the number of ordered distinct path pairs with a common start and end, hence is nonnegative. For r=t, identical directed incidence sequences are the subtracted term.

To prove (8), choose independent uniform nonbacktracking walks of lengths r,t from a fixed root and expose their required pairings. There are at most r+t discoveries and r+t+1 discovered vertices. A fresh pairing hits a previously discovered vertex with total probability at most C_d(r+t)^2/n. Without such a collision the revealed graph is a tree. Distinct nonbacktracking paths in a tree starting at the same root cannot have the same endpoint, including when their lengths differ. The probability of endpoint equality with distinct sequences is thus at most this collision probability. Multiply by a_ra_t and sum over n roots. Conditioning on simplicity only changes the constant, since the counted quantity is nonnegative and the simplicity probability is bounded below.

Put S_R(u,v)=sum_(r=1)^R N_r(u,v). Summing (8) and using the geometric growth of a_r yields

\[
\mathbb E\sum_{u,v}S_R(u,v)(S_R(u,v)-1)
\le C_d R^2q^{2R}.                                      \tag{9}
\]

Label symmetry and Markov's inequality imply

\[
\mathbb P\{S_R(c_a,c_b)\ge2\text{ for some distinct marks }a,b\}
\le C_d\frac{m^2R^2q^{2R}}{n^2}=o(1)                    \tag{10}
\]

for each fixed K, since m and q^R are of order n^(1/3). Therefore, with probability tending to one, every marked pair has at most one nonbacktracking incidence walk of length at most R.

If the host distance ell_ab is at most R, a shortest path is one such walk. Under the uniqueness event it is the only one. If the distance is greater than R, there is no such walk. Thus exactly, on this event,

\[
\sum_{r=1}^R q^{-r}N_r(c_a,c_b)
=q^{-\ell_{ab}}\mathbf1_{\{\ell_{ab}\le R\}}
\quad(a\ne b).                                         \tag{11}
\]

No tree ball around every mark is assumed. Such a simultaneous tree-ball assertion would be too strong at this scale.

## 4. The short marked graph is a tight matching

By label symmetry, probabilities of invariant events for fixed marks equal those obtained by sampling a uniform independent m-subset after the host. In every fixed host the distance-at-most-R graph has maximum degree at most C_d q^R. The expected number of its edges whose endpoints are marked is therefore at most

\[
C_d m^2q^R/n=O_{d,c,K}(1).                               \tag{12}
\]

Hence p_(n,K) is tight for fixed K. The number of host triples forming a wedge in this distance graph is at most C_d n q^(2R). Each triple is marked with probability (m)_3/(n)_3. The expected number of marked wedges is at most

\[
C_d m^3q^{2R}/n^2=O_{d,c,K}(n^{-1/3})=o(1).              \tag{13}
\]

Thus the induced marked graph is a matching with probability tending to one. Tightness of p and m tending to infinity also gives 2p<m with probability tending to one. Direct marked edges disappear with probability tending to one because their expected count is O(m^2/n)=o(1).

## 5. Operator error after retaining short interactions

Let W_(n,K) be the m by m matrix with zero diagonal and entries

\[
W_{ab}=q^{-\ell_{ab}}\mathbf1_{\{\ell_{ab}\le R\}}
\quad(a\ne b).
\]

On the uniqueness event, (11) identifies W with the off-diagonal short nonbacktracking sum. The stationary correction in (6), after compression and division by s, has norm O(mL/(ns))=O(sL)=o(1). The operator tail is o(s), including after diagonal deletion. By (3), the diagonal error is o_P(s).

For the remaining tail, exact label symmetry and (7) give

\[
\mathbb E\|\operatorname{offdiag}(E^TU_{R,L}E)\|_F^2
\le C\frac{m^2}{n^2}(nq^{-R}+L^4).
\]

Divide by s^2=m/n. Since q^(-R)=s q^(phi_n-K), the right side becomes

\[
C\left(mq^{-R}+mL^4/n\right)
=C\left(\theta q^{\phi_n-K}+mL^4/n\right)
\le C_{d,c}q^{-K}+o(1).                                 \tag{14}
\]

Markov's inequality, (3), (6), (10) and the stationary estimate prove

\[
\limsup_n\mathbb P\left\{
\left\|(G-gI)/s-gW_{n,K}/s\right\|>\eta\right\}
\le C_{d,c}\eta^{-2}q^{-K}.                              \tag{15}
\]

Unlike the previous subcritical argument, short pairs are retained rather than discarded. This is an operator-norm statement over the whole marked subspace.

## 6. Actual eigenvalue transfer at criticality

Let F be the pole-free retained Schur block, with B=sqrt(d-2)AE and C=0, and let b=B^T u. The exact earlier identity is

\[
F(d)=-(d-2)d^2(G-gI)+(d-2)A_C-2d(d-2)J_m/n,
\qquad b=d\sqrt{d-2}\,s e.
\tag{16}
\]

Here e is the unit constant marked vector and A_C=E^TAE. We have A_C=0 with probability tending to one. Equations (4), (5) and the exact derivative identity give

\[
\|F(d)\|=O_P(s),\qquad \|F'(d)-DI\|=o_P(1).             \tag{17}
\]

The local second derivative is bounded independently of m on a fixed interval about d, using the host gap and bounded ||B||.

Apply the reviewed [finite transfer theorem](../../growing-defects-round-01/root/transfer-v1.md), SHA256 deb05e53631ad4d273f48b2d6253014352c1263010d3990ebcc4e0b616351b99, with its Z=F(d) and D matrix equal to D I. Its retained comparison matrix divided by s is

\[
T_n=\begin{pmatrix}0&\kappa e^\top\\
\kappa e&-F(d)/(Ds)\end{pmatrix}.
\tag{18}
\]

By (17), ||T_n||=O_P(1). For any fixed sufficiently large B_0, take the transfer radius B_0s. Its error divided by s is o_P(1), since the constant-term error is exactly zero, the derivative error is o_P(1) and the quadratic remainder is O(B_0^2s). On the event ||T_n||<B_0/2 the finite transfer condition holds with probability tending to one. Let B_0 tend to infinity after n. This proves

\[
\max_{1\le j\le m+1}\left|
(\mu_j-d)/s-\lambda_j(T_n)\right|=o_P(1).                 \tag{19}
\]

Repeated eigenvalues cause no problem because the transfer theorem is ordered and uses inertia, not individual simple roots.

By (15), (16) and (d-2)d^2g/D=h, T_n is approximated in operator norm by

\[
S_{n,K}=\begin{pmatrix}0&\kappa e^\top\\
\kappa e&hW_{n,K}/s\end{pmatrix}                         \tag{20}
\]

with the error probability of (2), up to a constant. The stationary term in (16) divided by s has norm O(s), and the marked-adjacency term is zero with probability tending to one.

## 7. Decoupling the finite pair sector

On the matching event let V be the 2p marked coordinates belonging to short pairs. Set the host-to-marked entries of (20) to zero only on V. The resulting matrix differs from S_(n,K) by a symmetric star supported on V, whose operator norm is exactly

\[
\kappa\sqrt{2p/m}=o_P(1)                                \tag{21}
\]

for fixed K. This follows by restricting e to V: the removed coupling vector has squared norm kappa^2 times 2p/m, and the associated two-block star has eigenvalues plus and minus its Euclidean norm.

After permutation of marked coordinates, the resulting matrix is a direct sum of p two-by-two blocks

\[
\begin{pmatrix}0&h q^{-\ell}/s\\h q^{-\ell}/s&0\end{pmatrix}
\]

and a star on the host coordinate and the m-2p free marked coordinates. The pair blocks have eigenvalues plus and minus h q^(-ell)/s. The remaining star has eigenvalues

\[
+\kappa\sqrt{1-2p/m},\quad-\kappa\sqrt{1-2p/m},
\]

and m-2p-1 zeros when 2p<m. The finite normalization correction is retained here, not silently replaced by kappa. Its difference from the two values plus and minus kappa is at most 2kappa p/m=o_P(1).

Weyl's ordered eigenvalue bound, (19), (20), (21) and this final scalar correction establish (2). This proves the theorem.

## 8. Scope and next bridge

The proof uses the previously reviewed spectral gap, nonbacktracking tail and diagonal estimates. It proves new short-path uniqueness and matching estimates explicitly. It covers the critically weighted H=0 model, including the unweighted cubic case. An arbitrary bounded H can couple the remaining coordinates and is not included in the claimed limiting reduction.

The finite formal component verifies the separately recorded matrix identities and eigenvectors. The random graph, analytic transfer and limiting probability are not formalized here. A limiting-law statement additionally requires the independently proved joint law of the integer distances and a justified two-sided truncation argument. Neither is assumed by this effective-operator theorem.
