# Collective complementary correction at the retuned crossing

November 15, 2026. Owner: probability workstream. Revision 1, frozen for separate review.

## 1. Model, dependencies and theorem

Use the actual cubic graph pencil, retuning, reference vectors and exact two-dimensional Schur matrix of signed-coupling-v1.md, SHA256 68660a0914a02b0a6bf53f2ccef75a2b844859e9dafc7f8a9e106db3921d5fba. Thus

\[
 \beta_n=\frac{w-\kappa+(\kappa^2/2)sr}{s}\longrightarrow\beta,
 \qquad x_n^0=-\kappa-\frac{\kappa^2}{2}sr,
 \qquad \theta= c^{3/2},
\]

and the final conclusions are conditional on exactly one marked pair at distance r. Its probability tends to a positive constant. The two reference vectors are c_- and a_-, and Q_- projects onto their orthogonal complement in retained coordinates.

Write

\[
 A_n=\mathcal T_n(x_n^0),\qquad
 \Sigma_n=
 c_-^\top A_n Q_-
 (x_n^0 I-Q_-A_nQ_-)^{-1}Q_- A_n c_-.
\tag{1}
\]

This is the collective entry of the exact complementary correction. The inverse exists with a fixed norm bound on an event whose conditional probability tends to one. Assign any value off that event.

Let independent Poisson variables P_k have means

\[
 \lambda_k=\frac{3\theta}{4\sqrt2}\,2^k,
 \qquad w_k=\kappa\,2^{-k}.
\tag{2}
\]

In all limit statements below condition their family on P_0=1. Define

\[
 D=\sum_{k\in\mathbb Z}\frac{w_k^2}{\kappa+w_k}P_k.
\tag{3}
\]

The part k<=0 contains only finitely many nonzero summands almost surely. The positive-offset part has finite expectation, since its expected summands are O(2^(-k)). Thus D is finite almost surely.

**Theorem 1.** Jointly with the collective quadratic and every fixed finite collection of pair counts,

\[
 (C_n,\Sigma_n/s,(Z_{n,k})_{k\in J})
 \xrightarrow{\mathrm d}
 (C_{1/2},-D/\theta,(P_k)_{k\in J})
 \quad\text{conditional on }Z_{n,0}=1.
\tag{4}
\]

The C variable on the right is the compensated collective limit from collective-limit-v1.md, SHA256 e492d3dfa506167ba28782e316129146e72f8046e96bbaf50b265e42d3fc307d. It is built from this same Poisson family, not from an independent copy.

Consequently the tight collective coefficient from signed-coupling-v1.md has limit

\[
 L=\frac{\kappa^2}{2}C_{1/2}+\frac{63}{32}-\frac D\theta.
\tag{5}
\]

Equivalently, put

\[
 J(w)=\frac{\kappa w}{\kappa+w}.
\]

Then

\[
 L=\frac{51}{32}
 +\frac1\theta\left[
    \sum_{k\le0}J(w_k)P_k+
    \sum_{k\ge1}\bigl(J(w_k)P_k-w_k\lambda_k\bigr)
   \right].
\tag{6}
\]

The second series has a finite deterministic drift plus a convergent centered L2 series. Equations (5) and (6) are the same random variable under the stated coupling. The cancellation of their large-jump parts must be retained.

This file identifies the collective correction. The actual graph eigenvalue and eigenvector synthesis, including noncoincidence of the two limiting diagonals, is a separate application.

Exposure: this workstream authored and froze the two preceding probability proofs. Before this freeze, the integrator communicated agreement with the proposed scalar correction and the equivalent formula (6). No live root or structural proof was read. The finite calculation and cutoff-resolvent comparison below were reconstructed directly. Earlier frozen inputs are those named in the preceding probability proofs.

## 2. A collective column estimate that retains the cutoff factor

Fix K>=0 and put R=r+K. Let S_K be the full-star short-pair matrix from the earlier effective theorem. Its host star is kappa e and its marked off-diagonal weights are

\[
 \frac34\,2^{-\operatorname{dist}(u,v)}/s
 \quad\text{for marked pairs at distance at most }R.
\]

For fixed K its short marked graph is a matching with probability tending to one. Its count and largest scaled weight are tight.

The nonnegative nonbacktracking tail is

\[
 U_R=\sum_{j=R+1}^{L_n}2^{-j}N_j,
 \qquad T_R=\operatorname{offdiag}(E^\top U_RE),
\]

where L_n is a sufficiently large fixed multiple of log n. To distinguish it from the limit variable L, the truncation length is written L_n throughout this proof. The earlier two-walk and exact subset-sampling estimates give

\[
 \mathbb E\|T_Re/s\|^2
 \le C\left(2^{-R}+\frac{L_n^4}{n}
                     +\frac{mL_n^2}{n}\right).
\tag{7}
\]

Divide by s. Since 2^(-R)=s 2^(phi_n-K), n s has order m squared, and m/(n s) has order 1/m,

\[
 \limsup_n\frac{\mathbb E\|T_Re/s\|^2}{s}
 \le C_c2^{-K}.
\tag{8}
\]

The diagonal and stationary auxiliary operator in the resolvent decomposition has norm O_P(L_n cubed/m). Its squared norm divided by s tends to zero. The analytic pencil correction A_n-T has norm O_P(s L_n squared), whose squared norm divided by s also tends to zero. Hence, for every eta>0,

\[
 \limsup_n\mathbb P\left\{
  \|(A_n-S_K)e\|>\eta\sqrt s
 \right\}\le C_c\eta^{-2}2^{-K}.
\tag{9}
\]

The vectors in (9) are embedded in the marked coordinates. The host row of the difference is zero.

This also holds with e replaced by the free vector f that excludes only the resonant pair. Indeed,

\[
 f-e=\left((1-2/m)^{-1/2}-1\right)e
        -\frac{m^{-1/2}}{\sqrt{1-2/m}}(e_a+e_b).
\tag{10}
\]

The first coefficient is O(1/m). The full difference A_n-S_K has norm O_P(1) for each fixed K. On the matching event its columns at the two selected endpoints differ from their isolated pair columns by o_P(sqrt(s)), by signed-coupling-v1.md, including the analytic correction. Thus the effect of (10), divided by sqrt(s), vanishes in probability. Since c_-=(h-f)/sqrt(2), we obtain

\[
 \limsup_n\mathbb P\left\{
  \|(A_n-S_K)c_-\|>\eta\sqrt s
 \right\}\le C_c\eta^{-2}2^{-K}.
\tag{11}
\]

Conditioning on Z_(n,0)=1 only multiplies the limiting upper bounds by a fixed constant. All bounds leading to (7) were unconditional.

The existing global comparison, and the vanishing analytic correction, also give

\[
 \limsup_n\mathbb P\{\|A_n-S_K\|>\eta\}
 \le C_c\eta^{-2}2^{-K}.
\tag{12}
\]

The actual collective coupling column satisfies

\[
 \|Q_-A_nc_-\|/\sqrt s=O_{\mathbb P}(1).
\tag{13}
\]

This follows from the earlier O_P(m^(-1/2)) column bound and ms tending to theta. It is a bound for the actual matrix, independent of K.

## 3. Cutoff-resolvent comparison

Define the finite-model correction

\[
 \Sigma_{n,K}^{S}=
 c_-^\top S_K Q_-
 (-\kappa I-Q_-S_KQ_-)^{-1}Q_-S_K c_-.
\tag{14}
\]

On the matching event and for fixed K, the complementary spectrum of S_K has a fixed gap about -kappa with probability tending to one. To see this, delete its finite host couplings to all short-pair endpoints. The resulting direct sum has only its one collective negative vector and the selected antisymmetric pair at the target level. All other negative lattice levels have a fixed separation, as do zero and the positive levels. Its collective vector differs from c_- by O_P(m^(-1/2)). Restoring the couplings and changing that reference projection changes the compressed complement by o_P(1), on events where the tight count and weights are bounded. This proves the assertion.

The actual inverse in (1) has the fixed gap established in signed-coupling-v1.md. On events where both inverse norms are bounded, let

\[
 v=Q_-A_nc_-,\qquad v_K=Q_-S_Kc_-.
\]

The resolvent identity gives the deterministic inequality

\[
 \begin{split}
 \frac{|\Sigma_n-\Sigma_{n,K}^{S}|}{s}
 \le C\Bigg[
 &\left(\frac{\|v\|}{\sqrt s}
       +\frac{\|v_K\|}{\sqrt s}\right)
       \frac{\|v-v_K\|}{\sqrt s}\\
 &+\frac{\|v_K\|^2}{s}
       \left(|x_n^0+\kappa|+\|A_n-S_K\|\right)
       \Bigg].
 \end{split}
\tag{15}
\]

No matrix dimension enters the bound. Equations (11)-(13), tightness of v/sqrt(s), and x_n^0+kappa tending to zero imply

\[
 \lim_{K\to\infty}\limsup_n
 \mathbb P\left\{
  |\Sigma_n/s-\Sigma_{n,K}^{S}/s|>\varepsilon
 \right\}=0
\tag{16}
\]

for every epsilon>0, also under the final conditioning.

More explicitly, first restrict ||v||/sqrt(s) to a fixed large bound. The first term in (15) is then small whenever the column difference is small. That event also bounds ||v_K||/sqrt(s). Use (11) and (12) with a fixed small tolerance, send n to infinity, then K to infinity, and finally remove the large bound. The actual complementary-gap failure probability tends to zero. The model gap failure probability tends to zero for each fixed K. This proves (16) without assuming a growing-cutoff theorem.

## 4. Finite arrow calculation

The next calculation identifies the leading coefficient of (14). Suppose the short model has one distinguished resonant pair of weight w_0 tending to kappa, and ell further pairs of weights v_1,...,v_ell. Work uniformly when ell and all weights are bounded, and when every v_j stays a fixed positive distance from kappa. These conditions hold after a fixed finite offset truncation and a count bound.

Let u be the unit constant vector on coordinates outside all ell+1 pairs. Let t_j be the unit symmetric vector of pair j, with j=0 denoting the resonant pair. The nontrivial symmetric sector has basis h,u,t_0,...,t_ell. Its exact matrix has host-to-u coefficient

\[
 \kappa\sqrt{1-2(\ell+1)/m},
\]

host-to-each-t_j coefficient kappa sqrt(2/m), and t_j diagonal weight w_0 or v_j. All antisymmetric pair coordinates are exact eigenvectors of weights -w_0 or -v_j, and the remaining free-coordinate directions have eigenvalue zero.

Put delta=m^(-1/2) and c_0=(h-u)/sqrt(2). The vector c_- defined by removing only the resonant pair has expansion

\[
 c_-=c_0-\delta\sum_{j=1}^{\ell}t_j+O(\delta^2).
\tag{17}
\]

The operator has expansion S_K=S_0+delta S_1+O(delta squared), where S_0 has the free-star levels plus and minus kappa and the displayed pair levels. The first-order host coupling gives

\[
 S_1c_0=\kappa\sum_{j=0}^{\ell}t_j.
\]

Project away c_- and the distinguished antisymmetric vector. Combining this with (17) yields

\[
 \delta^{-1}Q_-S_Kc_-
 =\kappa t_0-\sum_{j=1}^{\ell}v_j t_j+O(\delta).
\tag{18}
\]

Indeed, the j-th nonresonant contribution is
kappa t_j-(v_j+kappa)t_j=-v_j t_j. This sign and coefficient differ from those obtained by using a collective vector that excludes every pair.

In the limiting complementary operator, every t_j has positive eigenvalue w_0 or v_j. The collective positive vector, the other antisymmetric vectors and the free dark directions are orthogonal to the leading vector in (18). The complementary inverse has a fixed gap by assumption. Its leading quadratic form is therefore

\[
 m\Sigma_{n,K}^{S}
 =-\frac{\kappa^2}{\kappa+w_0}
    -\sum_{j=1}^{\ell}\frac{v_j^2}{\kappa+v_j}+o(1).
\tag{19}
\]

Because w_0 tends to kappa, the first term may be replaced by
-w_0 squared/(kappa+w_0), with an o(1) error. The error is uniform on the indicated bounded sets. This follows either by the resolvent identity in the fixed-dimensional symmetric sector or by an orthogonal identification of the complementary projections, whose difference is O(delta). All remaining free directions are exactly uncoupled.

A bounded numerical check of one, two and three pair models, with m=80,160,320, reproduced convergence to (19). That check is corroboration only. Equations (17)-(19) are the analytic proof.

## 5. The finite-cutoff distribution and both tails

For every retained pair at distance r+k, its weight is w_n 2^(-k), with w_n tending to kappa. Conditional on Z_(n,0)=1, apply the finite calculation after retaining offsets -J through K. The count vector converges to the corresponding independent Poisson family conditioned on P_0=1. On a fixed count bound, the weights and gaps meet the uniform assumptions in Section 4. Since ms tends to theta,

\[
 \Sigma_{n,K}^{S}/s
 \xrightarrow{\mathrm d}
 -\frac1\theta D_K,\qquad
 D_K=\sum_{k\le K}\frac{w_k^2}{\kappa+w_k}P_k.
\tag{20}
\]

To justify the unbounded left end in (20), first use the finite truncation -J<=k<=K. The probability of any omitted stronger marked pair is at most C2^(-J), and the same bound holds for the limiting family. On the event with no omitted pair the short model itself is unchanged. Sending J to infinity therefore proves (20), jointly with all finite pair counts and the finite-cutoff collective quadratic.

The weak tail satisfies

\[
 \mathbb E(D-D_K)
 =\sum_{k>K}\lambda_k\frac{w_k^2}{\kappa+w_k}
 \le C_\theta\,2^{-K},\qquad K\ge0.
\tag{21}
\]

Here lambda_k w_k is constant in k, while w_k/(kappa+w_k)<=2^(-k). Thus D_K tends to D almost surely and in probability. This statement about the difference does not assert that the full variable D has finite mean.

Combine (16), (20), and (21) by convergence together. For the joint limit with C_n, use the same cutoffs and the same count vector. The collective approximation error is controlled by collective-limit-v1.md, and its limiting weak tail is L2-small. The left rare-pair events are shared and have probability tending to zero as J increases. This proves the full joint statement (4).

## 6. Cancellation and the scalar collective law

The relation between the coefficients of the collective quadratic and the pair amplitudes is

\[
 \frac{\kappa^2}{2}b_k=\frac{w_k}{\theta},
\qquad
 \lambda_k w_k=\frac{\kappa^2\theta}{2}.
\tag{22}
\]

Insert the compensated formula for C_(1/2) and subtract D/theta in (5). Since

\[
 w-\frac{w^2}{\kappa+w}=J(w),
\]

the random part becomes exactly (6). The constant is

\[
 \frac{63}{32}-\frac{\kappa^2}{3}
 =\frac{51}{32}.
\tag{23}
\]

For the positive-offset series in (6), write

\[
 J(w_k)P_k-w_k\lambda_k
 =J(w_k)(P_k-\lambda_k)
       -\frac{w_k^2}{\kappa+w_k}\lambda_k.
\tag{24}
\]

Its deterministic series is summable by (21), and its centered variance series is summable because J(w)<=w for w>0 and sum_(k>=1)lambda_k w_k squared is finite. Its negative-offset sum is finite almost surely, and also has finite expectation because J(w)<=kappa and sum_(k<=0)lambda_k is finite.

Thus the cancellation in (6) removes the infinite-mean large-jump contribution present separately in the raw quadratic and in D. The resulting scalar has finite moments of at least order two. This fact is a property of their coupled difference, not a consequence of subtracting two expectations that do not exist.

The law remains conditional on P_0=1. The probability variables at every other offset are independent with their original intensities. Their effects have not been replaced by an independent copy of the collective fluctuation.

## 7. Scope and remaining application

This proves the order-s collective complementary correction for the actual graph pencil and its joint law with the compensated quadratic. It identifies the scalar L that appears in the diagonal leading two-dimensional reduction. The signed off-diagonal is already o_P(s) by the separately frozen coupling proof.

An eigenvector conclusion still requires noncoincidence of L with the deterministic pair coefficient 33/16-beta, followed by the exact nonlinear-root and graph reconstruction steps. Those are separate from (4). This proof does not assume that the scalar law has a density and does not claim a generic avoided crossing.

Requested review: check the cutoff factor in the collective column estimate, the resolvent comparison in (15), the nonresonant coefficient -v_j in (18), the common Poisson coupling in (4), the cancellation in (22)-(24), and the distinction between finite expectation of the combined law and infinite expectations of its separate components.
