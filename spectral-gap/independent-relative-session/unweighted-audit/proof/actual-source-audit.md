# Actual-source proof audit: PASS

Audited source: `spectral-gap/unweighted-fractional-response.tex`.

Frozen SHA-256:

`005d2ef489ca2f96c4b7820dfa0f4d3d77da694ee39b65f5affe39ffa23d5f46`

An exact copy with that hash is retained as `frozen-source-005d2ef4.tex` in this directory. The source was read in full. During the audit the root file changed to SHA-256 `f0d8cca6c32416267ec4136c842bd30fae7898d77cb79153b5c088179e8c3c5d`; the change replaces the sentence introducing the cell-size sequence and has no mathematical effect. No root files were edited.

**Verdict:** the frozen source's main universality theorem, fractional-compression lemma, fixed-macro spectral-transfer lemma, exact effective-resistance assertion, and strict-count formula pass this independent mathematical audit. No inverse-power or growing-dimensional functional-calculus error was found. The conclusion is the source's stated sufficiency/universality assertion. An exact-closure interpretation across unrestricted growing dimensions requires the distinction discussed at the end of this report.

## 1. Compressed fractional powers are controlled uniformly in the physical dimension

Write

\[
 X_s=J_s^TA_sJ_s,\qquad
 R_s(t)=J_s^T(A_s+tI)^{-1}J_s.
\]

The Schur-complement inverse formula gives

\[
 R_s(t)\succeq(X_s+tI)^{-1}.
\]

Consequently

\[
 \begin{aligned}
 0\preceq J_s^TA_s(A_s+tI)^{-1}J_s
 &=I-tR_s(t)\\
 &\preceq I-t(X_s+tI)^{-1}\\
 &=X_s(X_s+tI)^{-1}
 \preceq\min(1,M/t)I.
 \end{aligned}
\]

Here the same finite \(M\) bounds every \(\|X_s\|\), independently of \(N_s\). The dominating scalar function

\[
 t^{\alpha-1}\min(1,M/t)
\]

is integrable at zero because \(\alpha>0\) and at infinity because \(\alpha<1\). For each fixed \(t>0\), the assumed compressed-resolvent convergence gives convergence of the compressed integrand to \(H(H+tI)^{-1}\). All compressed matrices have the same fixed dimension \(d\), so dominated convergence applies in operator norm and proves

\[
 J_s^TA_s^\alpha J_s\longrightarrow H^\alpha.
\]

This argument correctly handles both the growing dimension and diverging fast eigenvalues. It needs no uniform bound on \(\|A_s\|\), no entrywise eigenvector limit in the growing physical space, and no interchange between a fractional power and Schur complementation.

The first-moment compression bound is a substantive hypothesis. Compressed-resolvent convergence alone would not suffice: in dimension two, take \(A_s=\operatorname{diag}(s^2,0)\) and an isometry \(J_s\) whose first coordinate is \(s^{-\alpha}\). Then the compressed resolvent tends to \(1/t\), while \(J_s^TA_s^\alpha J_s=1\). Its compressed first moment diverges as \(s^{2-2\alpha}\). The source includes exactly the hypothesis that excludes this failure.

## 2. The cell/gadget block estimates remain valid when the fast space grows

Fix the macro dimension, masses, rational conductances, and all finite resistor gadgets before taking \(s\to\infty\). Let \(n_i(s)=2m_i(s)\sim sM_i\). The normalized cell indicator has port value \(n_i(s)^{-1/2}=O(s^{-1/2})\).

In the decomposition \(P\oplus Z\oplus F\), where \(P\) consists of cell constants, \(Z\) consists of the fixed gadget-coordinate space, and \(F\) consists of cell mean-zero vectors, the following estimates are correct for \(A_s=sL_s\):

\[
 \begin{array}{lll}
 PP=R_sK_{PP}R_s+tI,&PZ=\sqrt{s}R_sK_{PZ},&ZZ=sK_{ZZ}+tI,\\
 PF=O(\sqrt{s}),&ZF=O(s),&FF\succeq cs^2I.
 \end{array}
\]

The constants may depend on the fixed macro network and its gadgets, but are independent of \(s\) and of \(\dim F\). This independence follows because the external network has only finitely many edges: the norm of a port coordinate projected onto \(F\) is at most one, and all its relevant indicator coordinates have the \(O(s^{-1/2})\) bound. The internal complete-bipartite cell has nonzero eigenvalues \(m_i(s)\) and \(2m_i(s)\). Thus its restriction to \(F\), after scaling by \(s\), has a lower bound \(cs^2\), which the positive external Laplacian cannot reduce.

The inverse of the \(FF\) block is \(O(s^{-2})\) in norm. Its Schur correction therefore has block norms

\[
 PP:O(s^{-1}),\qquad PZ:O(s^{-1/2}),\qquad ZZ:O(1).
\]

Because \(K_{ZZ}\succ0\) is fixed, the subsequently reduced \(ZZ\) block has inverse

\[
 (sK_{ZZ}+O(1))^{-1}=s^{-1}K_{ZZ}^{-1}+O(s^{-2}).
\]

The final \(P\)-Schur complement is consequently

\[
 R_s(K_{PP}-K_{PZ}K_{ZZ}^{-1}K_{ZP})R_s+tI+o(1)
 \longrightarrow H+tI.
\]

The matrix \(H+tI\) is positive definite for every fixed \(t>0\), so its inverse gives the asserted compressed-resolvent limit. The unreduced \(PP\) block also proves \(\sup_s\|J_s^TA_sJ_s\|<\infty\). The identical argument applies after updating. If \(Z\) is absent, the first elimination alone gives the same conclusion.

## 3. The generalized Ritz step uses the correct pair

Set \(W_s=J_sV_s\). The vector \(g_s=(\sqrt{n_i(s)})_i\) has normalized direction tending to the normalized direction of \((\sqrt{M_i})_i\). Therefore one can choose orthonormal bases \(V_s\) of \(g_s^\perp\) converging to a fixed orthonormal basis \(V\) of \((\sqrt{M_i})^\perp\).

Every column of \(W_s\) is exactly orthogonal to the full physical constant vector: its gadget coordinates are zero, and its physical cell sum is \(g_s^TV_s=0\). Thus \(W_s\) lies in the positive support of both physical Laplacians.

The compressed pair is

\[
 \bigl(W_s^T(sL_s')^\alpha W_s,
       W_s^T(sL_s)^\alpha W_s\bigr).
\]

The source correctly compresses the fractional powers themselves, rather than taking a fractional power of a compressed Laplacian. By the compression lemma this fixed-dimensional pair converges to

\[
 (V^TH'^\alpha V,V^TH^\alpha V),
\]

whose denominator is positive definite. Its generalized eigenvalues therefore converge to the macro relative eigenvalues \(q_j\).

For completeness, generalized Ritz interlacing follows by applying ordinary Ritz interlacing to the relative matrix and the isometry

\[
 Y_s=Q_s^{1/2}W_s(W_s^TQ_sW_s)^{-1/2},
 \qquad Q_s=(sL_s)^\alpha\big|_{\mathbf1^\perp}.
\]

This yields \(\lambda_{s,j}\geq\mu_{s,j}\). Operator monotonicity gives \(\mu_{s,j}\geq1\). No convergence statement involving physical inverse fractional powers is used. Inverting the fixed \((d-1)\)-dimensional compressed denominator is legitimate because its limit is strictly positive definite.

## 4. Log-determinant exhaustion controls every extra eigenvalue

Let \(\beta=\alpha\log(1+\tau)\). Exact physical and macro leverage give

\[
 \sum_{j=1}^{N_s-1}\log\lambda_{s,j}
 =\beta=\sum_{j=1}^{d-1}\log q_j.
\]

Define

\[
 \rho_s=\beta-\sum_{j=1}^{d-1}\log\mu_{s,j}.
\]

Then \(\rho_s\geq0\), \(\rho_s\to0\), and all the summands in

\[
 \sum_{j=1}^{d-1}(\log\lambda_{s,j}-\log\mu_{s,j})
 +\sum_{j=d}^{N_s-1}\log\lambda_{s,j}=\rho_s
\]

are nonnegative. In particular, the following explicit uniform bounds hold:

\[
 \mu_{s,j}\leq\lambda_{s,j}\leq e^{\rho_s}\mu_{s,j}
 \quad(j\leq d-1),
\]

\[
 1\leq\lambda_{s,j}\leq e^{\rho_s}
 \quad(j\geq d),\qquad
 \sum_{j=d}^{N_s-1}\log\lambda_{s,j}\leq\rho_s.
\]

Thus all leading relative eigenvalues converge to \(q_j\), while the supremum of all extra correction eigenvalues is at most \(e^{\rho_s}-1\to0\), irrespective of their increasing number. The proof actually gives vanishing **total logarithmic budget** in the extra spectrum, which is stronger than merely having the largest extra eigenvalue vanish.

The physical constant direction contributes a further zero correction eigenvalue. The common time scaling by \(s\) cancels exactly from the relative matrix, since the positive and negative fractional exponents sum to zero.

## 5. The physical edge insertion has the stated exact combinatorics and resistance

For a fixed rational conductance \(p/q\), \(2p\) new internally disjoint paths of length \(2q\) have total conductance \(p/q\). Their endpoints share a bipartite color, and all internal vertices are new. The construction is simple even for \(q=1\), because the two-edge paths have different internal vertices.

Across the distinguished macro edge the port colors are opposite. Three new internally disjoint paths of length three have total conductance one and leave the direct port-to-port edge absent. Inserting that direct edge creates no multiple edge or odd cycle and changes the effective macro conductance from one to two.

All connections into any cell use its one port. Each cell's interior and each of the two remaining macro-path components therefore attaches to the distinguished connector through just one terminal. Such a component carries zero current in the terminal-to-terminal electrical problem. The connector resistance is exactly the parallel resistance of three length-three paths, namely one. This conclusion is exact at every finite \(s\); it is unaffected by cell sizes or rational approximations of other macro conductances.

Both graph endpoints are therefore finite, simple, unweighted, connected, and bipartite, and the inserted unit edge has leverage exactly one. Updated matrices differ by a positive rank-one physical incidence update, so the determinant budget is exactly \(\alpha\log2\).

## 6. The limiting quantifiers are sequential and sufficient

Fix \(\alpha\in(0,1)\), a finite target list, and \(\eta>0\). The source supports the following order, with no simultaneous uniformity claim:

1. Choose a finite SPD rank-one witness approximating the target as closely as required. The separated matrix scale is fixed after this choice. Unit target entries can be handled by a positive-log perturbation or inactive dimensions, as in the input theorem.
2. Choose the finite grounded mass-path parameter sufficiently large. This fixes a finite macro path, all its positive masses, and a one-edge increment ratio exactly equal to one. Commonly rescale both conductance matrices so that the distinguished base conductance and increment are each one. Relative spectra are unchanged by this common scaling.
3. Approximate only the other, still positive, macro conductances by positive rationals sufficiently closely. This is a fixed-dimensional, fixed-kernel, fixed-rank continuity step. It leaves the distinguished resistance/increment ratio unchanged because that macro edge is a bridge.
4. Fix the finitely many resistor gadgets representing those rational conductances and the distinguished insertion gadget. Only now let the integer cell-size parameter \(s\) tend to infinity, with \(2m_i(s)/s\to M_i\).
5. The fixed-macro transfer proof gives a finite threshold \(s_0\) beyond which the leading eigenvalue error and the entire extra spectral tail are within the remaining error allowance. Choose one finite integer \(s\geq s_0\).

For example, allocate errors less than \(\eta/4\) to the SPD, mass-path, rational, and final cell-size approximations. At each comparison, pad the shorter ordered correction spectrum with zeros to the final graph dimension. The triangle inequality then gives the stated coordinatewise tolerance. Constants in the final \(s\)-limit may depend on every earlier finite choice; the source does not need uniformity in those choices.

## 7. The strict-count formula follows without a hidden attainment assumption

At every finite stage,

\[
 \prod_j(1+\lambda_j(C_\alpha))=2^\alpha,
 \qquad \lambda_j(C_\alpha)\geq0.
\]

If \(m\) eigenvalues exceed \(\varepsilon\), then

\[
 m\log(1+\varepsilon)<\alpha\log2.
\]

The largest allowed nonnegative integer is the stated ceiling-minus-one formula. Conversely, use that many target entries equal to \(2^{\alpha/m}\). They lie strictly above the threshold, and the proved universality with a sufficiently small tolerance preserves the inequalities. Exact finite realization of the repeated target is unnecessary. The leading asymptotic constant follows from \(\log(1+\varepsilon)=\varepsilon+O(\varepsilon^2)\).

## Scope distinction: variable-dimensional closure need not preserve equality of determinant budgets

This is not an error in the actual theorem, which asserts realization of every equality-budget target and does not assert an exclusion of all other growing-dimensional limits. It matters if the result is described elsewhere as an **exact** closure characterization under only padded coordinatewise/supremum spectral convergence.

With unrestricted growing dimension, the fixed finite-stage determinant does not force a finite limiting list to have the same product. Choose length-\(m\) targets all equal to \(2^{\alpha/m}\), and approximate them with errors tending to zero. Then the supremum of every correction eigenvalue tends to zero, although every finite-stage relative determinant equals \(2^\alpha\). The all-ones finite target, whose product is one, is therefore also a padded-supremum limit.

More generally, in this finite-target padded-supremum topology the exact finite-target limit class has product **at most** \(2^\alpha\): necessity follows from each fixed finite prefix's logarithmic budget, and sufficiency follows by spreading any missing budget among a growing number of entries tending to one, then applying the proved theorem. Equality becomes necessary if the definition additionally requires the total logarithmic budget of all extra eigenvalues to tend to zero. The source's constructed equality-budget sequences satisfy this stronger exhaustion property by Section 4 above.

No historical-priority certification or computational-complexity claim is included in this audit.
