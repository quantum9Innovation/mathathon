# Actual-source graph and transfer audit

**Verdict: PASS.** No mathematical gap was found in the graph construction,
fractional compression argument, generalized Ritz argument, or determinant
exhaustion argument in the actual source. This audit does not certify historical
priority, a finite-precision algorithm, or any bound on graph size or degree.

Audited source: `spectral-gap/unweighted-fractional-response.tex`.

- The first complete read had SHA256
  `005d2ef489ca2f96c4b7820dfa0f4d3d77da694ee39b65f5affe39ffa23d5f46`.
- During the audit the source's cell-sequence sentence changed from “For large
  integer s” to “As integers s tend to infinity.” That intermediate source had
  SHA256
  `f0d8cca6c32416267ec4136c842bd30fae7898d77cb79153b5c088179e8c3c5d`.
- A later update added the complete finite-target closure corollary and Koke
  credit. A fresh full source read had matching start/end SHA256
  `f6a706de604fbaf986189b18d2059cbb888eaf660096a2f3b7ce1dcfad2d39d4`.
  That version was also audited; its new corollary passes, as explained below.
  Line references in this report refer to this latest version. No source edits
  were made by this auditor.

The underlying rank-one matrix closure and weighted mass-path realization were
independently audited in this session before the present task. Their use here is
legitimate: choose one sufficiently accurate finite mass-path witness first,
then hold it fixed throughout the unweighted simulation.

## 1. Rational gadgets, simplicity, and bipartiteness: PASS

Source lines 217–236 and 362–385.

For a positive rational conductance p/q, use 2p internally disjoint unit-edge
paths of length 2q. Each path has conductance 1/(2q), so their total conductance
is p/q. The paths have even length, so the terminals have the same bipartite
color. Even q=1 gives length-two paths, not parallel physical edges: their
internal vertices are different. There are no loops or repeated physical edges.

Each macro cell is a simple unweighted K_{m,m}. A port is chosen from whichever
side is to have the required global color. Removing the distinguished edge
splits the macro path into two components. Assign one port color throughout each
component and the opposite color across the distinguished edge. This is
consistent with every nondistinguished even-chain gadget.

The replacement of the distinguished bridge by three internally disjoint paths
of length three has exactly six new internal vertices and nine unit edges. Its
terminals have opposite colors. Each chain has resistance three, so the three
parallel chains have resistance exactly one. They have no direct terminal edge;
inserting that previously absent unit edge preserves simplicity and
bipartiteness. Both graphs are connected.

The requirement that every external edge of a cell use its **same single port**
is essential and is explicitly present in the source. The entire complete
bipartite cell then hangs from that port electrically. More generally, every
network outside the distinguished three-chain connector is attached to only one
of its two terminals: the macro connection graph is a path. Under fixed terminal
potentials such a dangling network has constant harmonic potential and carries
no current. It cannot change the two-terminal resistance. Therefore the inserted
edge has effective resistance exactly one at every finite cell size, not just
asymptotically.

No claim that the insertion terminals remain a bridge is used. The old bridge
is replaced by the nonbridge three-chain gadget; its electrical resistance and
its Kron-reduced conductance are what preserve the budget.

## 2. Conductance and mass scaling: PASS

Source lines 204–215 and 223–301.

Write n_i(s)=2m_i(s). The cell has unit vertex masses, total mass n_i(s), and
n_i(s)/s -> M_i. The normalized cell indicator has port value n_i(s)^(-1/2).
Multiplying the full physical Laplacian by s gives the cell-constant scaling

    R_s = diag(sqrt(s/n_i(s))) -> M^(-1/2).

For the fixed external network with blocks K_PP, K_PZ, K_ZZ, the exact PP, PZ,
and ZZ blocks of sL_s+tI before eliminating cell fluctuations are

    R_s K_PP R_s+tI, sqrt(s) R_s K_PZ, sK_ZZ+tI.

In particular J_s^T(sL_s)J_s=R_s K_PP R_s is uniformly bounded. There is no
missing factor of s in the effective macro conductance. The physical conductance
stays fixed; the growing cell masses create the slow time scale, which the
common factor s removes. That factor cancels from the final relative matrix.

The mean-zero spectrum of K_{m,m} consists of m (multiplicity 2m-2) and 2m
(multiplicity one). On the cell mean-zero space F, s times its cell Laplacian
therefore dominates c s^2 I for large s. Since the external Laplacian is PSD, it
cannot reduce the FF lower bound. Only finitely many port incidences and gadget
vertices occur at this stage. Their Euclidean row norms are uniformly bounded,
even as the dimension of F grows. Thus the norm estimates

    PF=O(sqrt(s)), ZF=O(s), (FF)^(-1)=O(s^(-2))

are correct. Eliminating F changes PP by O(s^(-1)), PZ by O(s^(-1/2)), and ZZ
by O(1). The ZZ inverse after that elimination is

    s^(-1) K_ZZ^(-1) + O(s^(-2)),

because K_ZZ is a fixed positive-definite Dirichlet matrix. Eliminating Z then
gives

    R_s (K_PP-K_PZ K_ZZ^(-1) K_ZP) R_s+tI+o(1) -> H+tI.

Its inverse is exactly the compressed resolvent. This verifies the lemma in
operator norm. The same estimates apply after insertion because only fixed
external blocks change; all cell blocks are the same. The distinguished
three-chain gadget merely adds a fixed six-dimensional piece to Z. The argument
also correctly handles Z empty in the preliminary bridge construction.

The fixed-network qualification is important but satisfied. Rational
approximation and the choice of its p,q are performed before the cell-size
limit. The proof never requires uniformity over increasing gadget counts.

## 3. Compressed fractional powers with diverging fast eigenvalues: PASS

Source lines 161–199.

For J isometric, A>=0, and t>0, Schur-complement inversion gives

    J^T(A+tI)^(-1)J >= (J^T A J+tI)^(-1).

Writing B=J^T A J, the exact identity

    J^T A(A+tI)^(-1)J = I-t J^T(A+tI)^(-1)J

therefore yields

    0 <= J^T A(A+tI)^(-1)J <= B(B+tI)^(-1)
      <= min(1,M/t) I

when ||B||<=M. The majorant multiplied by t^(alpha-1) is integrable near zero
because alpha>0 and at infinity because alpha<1. Compressed resolvent
convergence supplies pointwise convergence to H(H+tI)^(-1). Since the compressed
dimension d is fixed, matrix-valued dominated convergence is straightforward.

This proves J_s^T A_s^alpha J_s -> H^alpha. It does not assert convergence of
the full powers, whose norms can diverge. It does not require convergence of
inverse powers or a uniform lower spectral gap of the full graphs. The possible
large fractional contribution of growing fast eigenvalues is controlled by the
bounded compressed first moment. This resolves the principal analytical risk in
the construction.

## 4. Generalized Ritz trial space: PASS

Source lines 303–337.

Let g_s have entries sqrt(n_i(s)). Then J_s^T 1=g_s exactly, including the fact
that the gadget vertices have zero entries in J_s. Consequently J_s V_s is an
isometry into physical 1-perp whenever the columns of V_s span g_s-perp. Such
V_s can be chosen to converge: the normalized vectors g_s/||g_s|| converge to
sqrt(M)/||sqrt(M)||, so a small orthogonal rotation transports any fixed
orthonormal basis of the limiting complement.

The macro kernel is span(sqrt(M)), common to H and H'. Restriction of H^alpha
and H'^alpha to its orthogonal complement is SPD. The compressed physical
positive pair thus converges to an SPD pair, and its generalized eigenvalues
mu_s,j converge to all d-1 macro generalized eigenvalues q_j.

Operator monotonicity of x^alpha on nonnegative matrices gives mu_s,j>=1.
The generalized Rayleigh quotient is the full physical quotient restricted to
range(J_s V_s), so ordered generalized min-max yields lambda_s,j>=mu_s,j for
each j<=d-1. No unproved identification of the compressed inverse with the
inverse compression is made.

## 5. Exact logarithmic budget and all growing-dimension extras: PASS

Source lines 338–359 and 372–385.

On the common physical support, insertion is the rank-one update bb^T with
b=e_u-e_v. Its exact host leverage is b^T L_s^dagger b=1. Therefore

    sum_j log(lambda_s,j) = alpha log(2)

exactly at each finite s. The analogous macro bridge update has conductance
one -> two, so its total log budget is exactly the same. Arbitrary vertex
masses introduce no discrepancy. For a mass-normalized tree Laplacian,

    pdet(M^(-1/2) K M^(-1/2))
      = (sum_i M_i)/(product_i M_i) * product_edges(w_e),

so doubling one edge doubles the pseudodeterminant even with unequal masses.
Equivalently, its bridge effective resistance gives leverage one.

Define

    delta_s = alpha log(2) - sum_{j=1}^{d-1} log(mu_s,j).

Then delta_s>=0 and delta_s->0. The source's exact decomposition is

    sum_{j=1}^{d-1} [log(lambda_s,j)-log(mu_s,j)]
       + sum_{j=d}^{N_s-1} log(lambda_s,j) = delta_s.

Every summand is nonnegative. In particular, for j<=d-1,

    0 <= log(lambda_s,j)-log(mu_s,j) <= delta_s,

and uniformly for every extra index j>=d,

    0 <= lambda_s,j-1 <= exp(delta_s)-1 -> 0.

These bounds explicitly show why increasing N_s is harmless. They prove both
individual convergence of the intended leading eigenvalues and uniform decay
of *all* additional corrections. There is no exchange of an uncontrolled
infinite sum and limit. The constant direction adds another exact zero
correction eigenvalue, as stated.

This argument uses positivity essentially. It would not follow from a signed
determinant identity alone, but the actual update is positive, so the source
has exactly the required nonnegative summands.

## 6. Sequential limits, strict counts, and input scope: PASS

Source lines 387–420.

For a prescribed tolerance, select a finite matrix witness, then a finite
weighted mass-path witness. Common conductance scaling leaves the relative
matrix unchanged and makes the distinguished base edge and increment both
one. Positive rational approximation of the other path conductances preserves
the distinguished bridge leverage, since its resistance depends only on its
own conductance. Fixed-dimensional positive-support functional calculus is
continuous under this approximation. Now choose a sufficiently large finite
cell size. Each step has its own finite error allowance. No simultaneous
uniform limit over these choices is assumed.

The strict-count formula follows from (1+epsilon)^m<2^alpha and the constructed
equal-eigenvalue targets strictly beyond the threshold. At an integral budget
ratio the strict inequality correctly gives ceil(R)-1, rather than floor(R).
The zero-count case is handled separately. No finite graph is claimed to
attain a repeated nontrivial relative spectrum exactly.

## 7. Added finite-target closure corollary: PASS

Source lines 88–129 and the final clause/proof of the arbitrary-bridge
corollary.

The current source correctly distinguishes the exact finite-stage determinant
identity from the closure in the metric of zero-padded ordered correction
lists. In that growing-dimension topology, the complete finite-target closure
is product(q_i)<=2^alpha, not necessarily equality.

Necessity follows by retaining the largest n nonnegative log eigenvalues before
taking the approximation limit. For sufficiency let the missing log budget be
S>0. Appending m eigenvalues exp(S/m) produces an equal-budget target; their
corrections tend uniformly to zero as m grows. Replacing those appended
corrections by zero changes the sorted diagonal spectrum by at most
exp(S/m)-1, by ordered eigenvalue continuity. Applying the equal-budget
construction and then the triangle inequality proves the claim. The same
argument applies for budget alpha log(1+tau) in the arbitrary-bridge class.

There is no contradiction with the fixed-macro transfer proof in Section 5.
For a fixed macro witness its Ritz budget is exhausted, so the total log budget
of its microscopic extra modes tends to zero. For a deficit target the number
of deliberately appended macro modes also tends to infinity; their individual
corrections vanish while their total log budget remains S. Thus determinant
continuity must not be asserted across growing padded dimensions. The added
corollary states the correct distinction.

## 8. Independent numerical diagnostic

`check_gadgets.py` builds the actual unweighted gadgets, without weighted-edge
shortcuts. It uses three cells of target masses (1,2,3), one nondistinguished
conductance 2/3 implemented by four length-six chains, and the distinguished
three length-three chains followed by the direct edge insertion. It checks:

- every physical edge is a new unordered pair, every edge crosses the assigned
  bipartition, and the inserted pair was previously absent;
- the insertion changes the Laplacian by exactly bb^T;
- host effective resistance equals one numerically at each size;
- compressed resolvents and compressed fractional powers approach the macro
  matrices;
- full generalized eigenvalues dominate their Ritz approximants;
- the full logarithmic budget is alpha log(2), within numerical precision;
- the largest extra log eigenvalue is bounded by the computed Ritz budget slack.

The run uses alpha=0.6 and s=4,...,256, reaching 1,562 graph vertices. The host
resistance errors stay below 1.2e-10. The compressed resolvent error decreases
from 0.5514 to 0.0290; the compressed fractional-power error decreases from
1.2771 to 0.4636; the leading relative spectrum error decreases from 0.0752 to
0.00559. Slow fractional convergence is expected, and no monotonicity of each
extra eigenvalue is asserted. Full output is in `diagnostics.txt`.

The numerical experiment supports the source construction. The proof audit,
particularly the uniform bound exp(delta_s)-1, establishes the asymptotic
claim beyond these finite sizes.

## Final determination

PASS for the actual graph theorem and its proof, subject to its explicitly
stated and independently checked matrix/mass-path inputs. The strongest
construction claim survives this audit: both endpoint graphs are simple,
unweighted, connected, and bipartite; exactly one absent unit edge is inserted;
its host effective resistance is exactly one; every determinant-admissible
positive rank-one fractional relative spectrum is approximable; all additional
relative correction eigenvalues tend uniformly to zero. No requested source or
root files were edited.
