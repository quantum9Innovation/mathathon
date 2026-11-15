# Audit of the assembled degree-three construction

Date: 15 November 2026.

Reviewed source: `../unweighted-degree-dichotomy.tex`

Final-source SHA256: `7fee1542cb46ef2267241233dd4ad292b16dad56c61749126b81360095e5965f`

Scope: Section 5, “A degree-three unit-weight lower construction,” including the reservoir existence specialization, fanout circuit, pivot identities, uniform mass choices, low relative compression, and the final strict-count lower bound. The general separated-mass lemma in Section 4 was checked against the independently proved companion note.

**Verdict: PASS.** No mathematical correction is required in the reviewed Section 5. No edits were made to the assembled source.

Final-hash refresh: the initial review covered source SHA256 `c78a3c62a705403864bb1381a08d238a413198d47f268f3944f10441ce07f1a5`. The final source above was reread and Section 5's mathematical argument, formulas, parameter choices, and conclusions are unchanged. Its lemma title and introductory sentence received only wording changes. The stronger Jensen-based outlier theorem in Section 6 is outside this audit's scope and was separately audited by the root and path-upper agents. This Section 5 PASS carries forward to the final source hash.

Checks supporting that verdict:

1. **Source and graph class.** Bordenave, arXiv:1502.04482v4, Theorem 1, explicitly samples uniform *simple* `d`-regular graphs along every sequence with `nd` even. At `d=3`, taking epsilon `(3-2sqrt(2))/2` gives a cubic Laplacian gap at least the displayed `gamma_0` for some graph at every sufficiently large even size. The positive gap forces connectedness. Subdividing one edge gives a degree-two port; the stated variance estimate preserves a uniform positive gap. All final host degrees are at most three and the edited edge is a bridge.

2. **Contacts and fanout.** The port resistance is resistance to the reservoir mean. Static minimization correctly places it in series: neck resistance `ell+r_i`, and edited root-anchor resistance `1+r_0` versus `1/2+r_0`. The graph remains unit-weight before doubling. The root-to-leaf voltage drop is bounded by the geometric sum of descendant-current bounds, uniformly in the order of grounded terminals. The exact Thevenin increment is `v_j^2/(ell+r_j+rho_j)`, so `Delta g_j >=1/(4Km)` follows from the stated constants.

3. **Determinants and direction.** With `f(g)=(c_0'+g)/(c_0+g)`, the determinant ratio on trailing terminals is exactly `f(g_(i-1))/f(g_m)`. Its reverse pivot ratio is `f(g_(i-1))/f(g_i)>1`, with the displayed uniform lower logarithmic increment `h/m`. This verifies both the denominator and the elimination order in equation (5.2). The effective terminal update is positive rank one by the Schur inverse identity.

4. **Mass parameter choices.** The contact cube is compact. Its terminal stiffness matrices stay SPD and depend continuously on contacts; the rank-one update vector can also be chosen continuously through the Schur formula. The convergent-family version of the separated-mass lemma therefore makes the terminal separation uniform over the cube. The anchor limit has one exact zero and `m` positive eigenvalues bounded away from zero for fixed terminal masses, uniformly over contacts. The stated successive margins `3/4`, `5/8`, and `1/2` of `alpha h/m` are consistent.

5. **Reservoir low-space limit.** With the finite core fixed, the fast block has a uniform gap despite its growing dimension: internal reservoir energy controls mean-zero deviations, and the pinned-core Dirichlet form controls the remaining fixed core norm. The static Schur matrix is exactly `N_s^(-1/2) K(r_s) N_s^(-1/2)`, not an asserted exact fractional reduction. Couplings are `O(s^-1/2)` and the frequency correction is `O(|lambda|/s)`. The graph-subspace equation gives the stated low isometries and scaled low endpoint matrices.

6. **Relative fractional calculus.** High updated spectral components leak into the baseline low space in norm `O(s^-1/2)`, so their compressed positive fractional contribution is `O(s^-1)`. It vanishes after multiplying by `s^alpha` precisely for `alpha<1`. The baseline inverse fractional factors then yield the claimed relative compression, with the shared zero direction treated by pseudoinverse calculus. This step correctly allows a nonvanishing high relative response.

7. **Finite realization and count.** Contact compactness converts subsequential convergence to sufficient uniform approximation for the fixed selected masses. Compression min-max transfers the `m` low eigenvalue lower bounds to the actual finite graph. A power of two in the stated interval exists for small epsilon and gives a strict count of order `1/epsilon`. The determinant budget supplies the matching upper order.

Ancillary cleanup completed in the bounded-degree standalone files: references now use Bordenave's Theorem 1 rather than Alon; the companion proof reference points to the existing `.tex` file and contains no pending-proof placeholder. The standalone PDF was rebuilt after these changes.
