# Independent review of the logarithmic negative resonance argument

November 15, 2026. Revision 1, frozen review.

## Decision and exact scope

Accepted for the explicit retained matrices T, Gamma and widehat T defined in the target. I found no blocking unsupported inference in equations (6), (7), or the retained eigenvalue and separated-subspace conclusions in Section 8.

This decision does not establish the separate graph normalization bridge (47). It does not identify a basis in a repeated pair sector, resolve the retuned crossing a=-kappa squared/2, or prove physical localization. No probability statement is being treated as formally verified.

The review target is `probability/negative-log-scale-v1.md`, SHA256 `faced6a02d91d451e4ef0e0989d3d46811da66d809d40e9344e9444012901409`. Its direct dependency is `probability/refined-resolvent-v1.md`, SHA256 `bd00db6c2f69813d480f5a86d5d22c8b6fe4922d9cc3d233f72840dddb29f8df`.

Prior exposure: the reviewer authored the finite formal components for this and earlier rounds and received the finite equal-pair normal form. That work concerned actual finite matrix identities and did not prove the probability estimates reviewed here. The target probability proof and its direct dependency were read for this review. The shared workspace was available throughout, so this was neither blind nor access-isolated. No other review of this target was read before freezing this report.

## Dependencies reconstructed

I inspected the relevant single-walk, two-walk, pair-selection and effective-operator arguments in the following frozen files. Their current hashes match those cited by the direct dependency.

| Dependency | SHA256 |
| --- | --- |
| growing-defects-round-01/probability/proof-v1.md | 56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b |
| close-pair-transition-round-01/root/nonbacktracking-upper-v1.md | d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896 |
| critical-law-round-01/probability/pair-counts-v1.md | 702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29 |
| critical-law-round-01/root/effective-operator-v1.md | 13b559897d6ed9253a2fc6dd4dede5dd03914c078558d759542afc9c54d28864 |

The published positive simplicity probability and fixed two-sided host gap remain the stated external premises. Their published proofs were not re-audited here. The relevant nonnegative exploration bounds and finite subset-selection arguments were reconstructed from the local proofs.

Throughout the check, n is of order m cubed, s is of order 1/m, 2 to the power r is of order m, and L and r are of order log m. Therefore t=sr is of order log(m)/m. In particular, 1/m=o(t), while a first-order error of order 1/sqrt(m) is not o(t).

## Finite-sampling variance

Write pi_j=(m)_j/(n)_j, and index the off-diagonal entries of a deterministic symmetric nonnegative H by unordered edges. Then

\[
Y=\frac2m\sum_e H_e I_e.
\]

The variance terms with the same unordered edge have coefficient at most pi_2. Terms whose edges share exactly one endpoint have coefficient at most pi_3. Their weight sum is bounded by a constant times the sum of squared row sums. For disjoint edges the covariance is

\[
\pi_4-\pi_2^2\le0.
\]

For sufficiently large m this follows by comparing the two remaining inclusion factors after one edge has been selected with the corresponding original factors. Nonnegativity of H permits discarding these covariance terms in an upper bound. Thus

\[
\operatorname{Var}(Y\mid H)
\le\frac C{m^2}
\left(\pi_2\|H\|_F^2+
\pi_3\sum_u\left(\sum_vH_{uv}\right)^2\right)
\le C\left(\frac{\|H\|_F^2}{n^2}
+\frac{mL^2}{n^2}\right).
\]

This verifies (18) with fixed-size sampling. Independent marks are not substituted.

For H equal to the off-diagonal part of U_R, the conditional mean is exactly

\[
\frac{m-1}{n(n-1)}\left(nv_R-\operatorname{tr}U_R\right),
\qquad v_R=\frac32(L-R).
\]

The non-trace part differs from s squared times v_R by O(L/n). The trace estimate in (20), multiplied by its actual sampling coefficient, is negligible relative to s squared times r. The three normalized variance contributions in (21) have orders 1/r squared, L to the fourth divided by m squared r squared, and L squared divided by m r squared. All vanish. Thus (22) is justified, including the concentration at the scale needed for the logarithmic coefficient.

## Sharpened columns and selected diagonals

The improvement from the older L to the fourth over m column bound to (13) is valid. The sum of nonnegative own-partner tail entries is O_P(L cubed/n) by its first moment. Squaring this probability bound gives an own-partner squared Frobenius contribution O_P(L to the sixth/m to the fourth) after division by s squared. This step does not assume a second-moment bound for that sum.

For every remaining selected-row entry, three distinct marked vertices are required. The deterministic distance-degree bound and the unconditional tail Frobenius estimate give

\[
\pi_3 2^r H_R/s^2=O(1/m+L^4/m^3).
\]

The matching exception has probability tending to zero. These two estimates give (13), and the collective-column estimate gives (14) and (15). The diagonal and stationary auxiliary operator has squared norm O_P(L to the sixth/m squared), which is o(1/m).

For the selected diagonal, let X_j(u) be the nonnegative ordinary-walk excess-return sum. Pointwise,

\[
\mathbf1_{\{u\in V\}}X_j(u)
\le\sum_{v\ne u}\mathbf1_{\{u,v\in S\}}D_r(u,v)X_j(u).
\]

Averaging over the uniform subset first and then using the deterministic distance-degree bound gives

\[
\mathbb E\sum_{u\in V}X_j(u)
\le C\pi_2 2^r\mathbb E\sum_uX_j(u)
\le C\pi_2 2^r L^{j+3}=O(L^{j+3}/n).
\]

This proves the selected improvement (28) without conditioning on a rare pair event. The stationary diagonal and the operator tail have the stated smaller orders. The own-pair, four-distinct-endpoint and stationary estimates likewise give (30). Applying the previously derived three-endpoint row-sum estimate verifies (32).

## Stationary cancellation and collective drift

The averaged diagonal bound in (23) follows from the single-walk estimate with the sum divided by m. Its scale is smaller than s squared times r. On each fixed-cutoff matching event, the short contribution is O_P(s/m), hence O_P(s squared).

The exact off-diagonal stationary coefficient includes the initial Q term as well as all L nonbacktracking terms. The long-tail mean and stationary term therefore combine as

\[
 g s^2\frac32(L-R)
-g s^2\left(1+\frac32L\right)
=-s^2R-gs^2.
\]

Since g=2/3 and R=r+K with fixed K, this equals -s squared times r plus a lower-order term. The use of m rather than m-1 costs O(L/n), also negligible. This verifies the sign and coefficient in (25).

Multiplication by 9/(8s) gives -kappa squared times sr, since kappa squared is 9/8. The extra J term in (16) contributes only O(s). Replacing e by f costs O_P(1/m): use the strengthened bound for Ze in the linear cross term and the bounded norm of Z in the quadratic term. A coarse bound using only the norm of Z would not suffice at this point. This establishes (27).

The same distinction is handled correctly in (33). In Za_j=-w a_j+v_j, the leading vector is exactly orthogonal to f-e. Only the residual of order 1/sqrt(m) enters the replacement error, giving O_P(1/m)=o_P(sr).

## Derivative coefficient and corrected compression

The derivative of the tree recursion parameter satisfies rho'(3)/rho(3)=-1. Differentiating the nonbacktracking coefficient g_3(z)rho(z)^r therefore gives

\[
(g_3'-gr)2^{-r}.
\]

The weighted tail is bounded entrywise by O(L) times the same nonnegative unweighted tail. The selected diagonal estimate with j=1 and the stationary derivative coefficient O(L squared) give (35).

The exact identity for Gamma_M is consistent with differentiating

\[
F(z)=2zI+A_C-z^2G(z)-(z+3)J/n.
\]

The selected off-diagonal coefficient in Gamma_M is

\[
-\frac18\left(6g+9g_3'-9gr\right)2^{-r}
=\frac34(r+1)2^{-r}
=s(r+1)w.
\]

Thus Gamma acts on the selected antisymmetric sector with leading coefficient -kappa sr. The sign in (37) is correct.

The ordinary-walk quadratic calculation gives the collective derivative bound O_P(L to the fourth/n+mL squared/n). This is o_P(sr). The selected mixed derivative estimate is also o_P(sr), and the full operator estimate is O_P(sL squared). Replacing e by f then costs O_P(sL squared/sqrt(m))=o_P(sr), as required in (41).

Consequently, for the isometry U in the target,

\[
U^\top TU=-\kappa I+
 sr\operatorname{diag}(-\kappa^2/2,-aI_p)+o_P(sr),
\]

\[
U^\top\Gamma U=
 sr\operatorname{diag}(0,-\kappa I_p)+o_P(sr).
\]

Replacing the compressed product of Gamma and T by the product of their compressions costs at most O_P(sL squared/sqrt(m)), using the separately proved off-block T bound. The correction in widehat T is therefore plus kappa times the compressed Gamma to this precision. Its pair contribution is -kappa squared times sr, not the opposite sign. This proves (6).

Also, the full correction widehat T-T is O_P(sL squared), which is o_P(1/sqrt(m)). Hence its off-block coupling still has squared norm O_P(1/m), proving (7). Tightness of p is enough to pass between the displayed column estimates and the variable-dimensional operator estimates.

## Complementary gap and retained subspaces

For each fixed K, the decoupled short model has no nonresonant pair amplitude arbitrarily close to kappa. Its amplitudes are w times integer powers of two. After excluding offset zero, their distance from kappa is bounded below by a fixed positive constant for large n. The zeros and positive levels are separated as well.

The model's negative collective vector differs from the target b_- by O_P(1/sqrt(m)). The number of additional short-pair coordinates is tight for fixed K, and the model norm is tight. Aligning these two subspaces therefore changes the complementary compression by o_P(1). This justifies using the complement of the target U, rather than the exact short-model complement.

The global tail comparison at a fixed small tolerance has limiting failure probability at most C times 2 to the power -K. The metric correction is o_P(1). The actual complementary-gap event is independent of the auxiliary K, so taking the upper limit in n first and then sending K to infinity proves that this event has probability tending to one. This is a valid two-limit argument and does not assert a vanishing fixed-K global error.

On the gap event, write the actual block matrix relative to U as blocks A, B and C. For lambda in a fixed neighborhood of -kappa, the Schur correction satisfies

\[
\|B^\top(C-\lambda I)^{-1}B\|
\le C_\mathrm{gap}\|B\|^2
=O_P(1/m)=o_P(sr).
\]

The Schur derivative is negative definite, namely minus the identity minus B transpose times the squared complementary resolvent times B. Inertia at the two endpoints therefore counts exactly p+1 roots. The uniform correction bound and ordered eigenvalue bracketing give the shifts in (46).

When a is different from -kappa squared/2, the two displayed coefficient groups have a positive separation after division by sr. The complementary elimination error is o_P(sr), and the complementary component of each normalized retained eigenvector is O_P(1/sqrt(m)). Within U, ordinary finite-dimensional spectral perturbation then gives convergence of the simple collective projector and the p-dimensional pair projector. This reasoning uses the squared coupling through the fixed complementary gap. Applying a first-order perturbation estimate directly at the shrinking logarithmic gap would not justify the conclusion.

The case p=0 is included. When p>1, the conclusion concerns the pair subspace and does not select its individual basis vectors. At the retuned crossing the coefficient groups coincide, so the stated exclusion of that case is necessary and preserved.

## Accepted boundary

The target proves a logarithmic law and separated-subspace statement for its explicit graph-derived retained matrix widehat T. Its estimate O_P(norm(Gamma) squared+s)=o_P(sr) is arithmetically sufficient for the proposed normalization bridge, but existence of the corresponding actual graph-cluster isometry and that error estimate are separate obligations. They were neither assumed nor checked in this review.

No source proof was edited. No stronger individual-vector, smaller-scale, localization or novelty conclusion is accepted by this report.
