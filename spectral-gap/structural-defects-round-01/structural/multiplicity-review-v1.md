# Review of the finite-multiplicity extension

Date: November 15, 2026. Reviewer: structural workstream. Revision 1.

Target: `../probability/multiplicity-extension-v1.md`, SHA256 `2649c74230d20b7411cdf1a92276c63b8181e0674e53d5f58e87a63918f796cc`.

Verdict: accepted as a paper result at the exact target revision. No open finding was identified. The earlier probability-chain and density reviews remain the explicit premises of this addendum. Actual graph root and physical-subspace transfer are still separate.

Exposure: the reviewer had completed reviews of all four probability dependencies. The author then supplied this frozen extension, and the integrator was informed of the additional review. No live root graph synthesis was read before this file was frozen.

The selected bounds genuinely concern all endpoints of distance-r pairs, before any conditioning on their number. Their restriction to a fixed p divides probabilities by a positive limiting Poisson mass. Over a finite set of p values that denominator has a positive minimum. Consequently the stated uniformity over finite p sets is valid and does not replace sampling without replacement by independent marking.

For v equal to the sum of the 2p selected coordinate vectors, A_Vv=v and every selected antisymmetric vector is orthogonal to both v and e. The exact free-vector normalization gives

\[
 f_p^TZf_p=e^TZe-2pw/m+o_P(s).
\]

The host star contributes -kappa+kappa p/m+o(s). Its p-dependent correction cancels half of the displayed quadratic correction, up to p(kappa-w)/m=o(s). The collective constant therefore remains 63/32 before the complementary correction. All pair signs yield the same diagonal 33/16-beta_n. The selected operator estimates and exact antisymmetric orthogonality make the whole mixed row and off-diagonal pair block o_P(s), not merely each formal leading term.

The analytic pencil and metric estimates do not depend on p. The marked-coordinate projector has compression 1/2 on the collective vector and identity on the p-dimensional antisymmetric block. The selected residual norm remains o_P(sqrt(s)), while the collective column is O_P(sqrt(s)). With the fixed complementary gap these give the claimed o_P(s) mixed and pair corrections.

The complementary space removes all p negative resonant vectors and the single collective negative vector. Thus it contains no unremoved eigenvalue at the target level. The other lattice levels remain separated by a fixed amount independent of the auxiliary cutoff. The p=0 case removes only the collective vector and has the same gap because the distance-r count is zero.

In the finite matching calculation, the collective vector excludes all p selected pairs but includes the other pair endpoints. Its first-order complementary column therefore has coefficient kappa on every selected symmetric pair vector and coefficient -v_j on each nonresonant symmetric pair vector. This gives

\[
 m\Sigma^S=-p\kappa^2/(\kappa+w)
               -\sum_jv_j^2/(\kappa+v_j)+o(1).
\]

All selected positive channels remain in the complement. Replacing p kappa squared by p w squared is valid for fixed p. The same column and full-operator cutoff bounds then transfer this expression to the actual pencil. Both tails and the common Poisson coupling remain exactly those of the reviewed one-pair proof.

The law with P_0=p is the deterministic translation L_p=L_0+kappa p/(2theta), with all other counts coupled identically. Smooth density, absence of atoms and positive probabilities of both orderings therefore persist. For p=0 there is no pair ordering statement, as the target says. The rank-p pair block remains a grouped subspace, and no individual basis is selected.

The moment formulas are correct. For each j>=1, the negative-offset mean lambda_0 kappa/(1+2^j) cancels the positive-offset drift of the same size. Both separate sums are finite. The remaining mean is 51/32+kappa p/(2theta). The two variance contributions at j and -j are equal. Summing them and using lambda_0=kappa theta/2 gives

\[
 \operatorname{Var}(L_p)=\frac{\kappa^3}{\theta}
              \sum_{j\ge1}\frac{2^j}{(1+2^j)^2}.
\]

The variance is independent of p because the k=0 coordinate is fixed under conditioning. Mixing its original Poisson law adds kappa cubed/(8theta) to the variance and changes the mean to 51/32+kappa squared/4=15/8. These are moments of the limiting scalar only. The target correctly makes no finite-n moment-convergence assertion.

Finally, tightness of p_n and convergence for each fixed p justify the unconditional mixture by a finite-p truncation. This treats the random dimension explicitly. No extra precision for the unresolved splitting inside the repeated pair block is inferred.
