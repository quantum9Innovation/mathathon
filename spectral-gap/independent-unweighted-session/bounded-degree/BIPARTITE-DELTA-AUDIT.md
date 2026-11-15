# Bipartite strengthening: independent delta audit

Date: 15 November 2026.

Old audited snapshot: `../audited-snapshot-7fee1542/unweighted-degree-dichotomy.tex`

Old-source SHA256: `7fee1542cb46ef2267241233dd4ad292b16dad56c61749126b81360095e5965f`

New source: `../unweighted-degree-dichotomy.tex`

New-source SHA256: `a2fa32dea9bd90061103327c083ae8d587ed6b772fc340f48f378a1754f5d158`

Scope: the exact source diff consists of the abstract's bipartite assertion and the new Corollary `cor:bipartite` with its proof. The previously audited argument is unchanged. This audit checks only that delta and does not replace `ASSEMBLED-AUDIT.md`.

**Verdict: PASS.** The added corollary and abstract assertion are valid. No source changes are required or were made.

The checks were:

1. **Cubic double covers.** Bordenave's Theorem 1 for uniform simple cubic graphs gives, at every sufficiently large even original size, a graph whose nontrivial adjacency spectrum lies in `[-3+gamma_0,3-gamma_0]`. The double-cover adjacency matrix is exactly `[[0,A],[A,0]]`, with spectrum consisting of both signs of the original spectrum. It is simple and cubic. The original spectral bound excludes a second `3` and any `-3`; consequently the cover's `3` and `-3` are each simple. Its `3` is simple, so the regular cover is connected, and its combinatorial Laplacian gap is at least `gamma_0`. Original sizes `2k` give cover sizes `4k`.

2. **Odd subdivision and its gap.** Replacing an edge by three edges preserves its endpoints' opposite colors, hence preserves bipartiteness. Both added vertices have degree two. Cauchy--Schwarz gives old energy at most `3Q`; the old-vertex variance about its old mean is therefore at most `3Q/gamma_0`. Each new vertex has an old neighbor, so each additional squared deviation is at most `2Q+6Q/gamma_0`. Summing all terms gives the variance bound `(4+15/gamma_0)Q`; minimizing over the mean proves the displayed uniform gap `gamma_bip=1/(4+15/gamma_0)`.

3. **Sizes and contacts.** Reservoir sizes `4k+2` are available for every sufficiently large `k`. Rounding to this arithmetic progression after common scaling realizes every prescribed finite positive mass ratio. Their port resistance to the mean is at most `1/gamma_bip`, by the same pseudoinverse-gap estimate used in the main construction.

4. **Assembly.** The core is a tree, and every reservoir has only one attachment. Each reservoir's bipartition can therefore be independently flipped to make its attachment edge proper. This includes the anchor. The full host is connected, simple, bipartite, and of maximum degree three, and the edited root-anchor edge remains a bridge.

5. **Transfer of the existing proof.** Replacing the old uniform reservoir-gap/contact constants by the new positive constants changes only the fixed positive lower-bound constant. The fanout circuit inequalities, compact contact parameter choices, mass separation, anchor limit, and relative low-space convergence all continue to apply. The finite examples therefore retain an `Omega_alpha(1/epsilon)` strict count, while the same determinant argument gives the matching upper order.

Primary-source requirement: no additional external theorem is needed. The sole existence input remains Bordenave, *A new proof of Friedman's second eigenvalue theorem and its extension to random lifts*, Theorem 1, arXiv:1502.04482v4. The double-cover spectrum, connectivity, odd subdivision, variance estimate, and bipartition assembly above are elementary deductions, verified directly in this delta audit.
