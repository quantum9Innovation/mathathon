# A common transition for interacting graph attachments

This round establishes two reviewed paper results. The first gives a common spectral transition for a class of fixed finite attachments to a sparse random regular graph. The second determines a finer random law at a previously unresolved collective-pair collision in the cubic duplication model. The finite matrix ingredients have separate formal checks. The complete random-graph theorems are not formally encoded.

## 1. Why the threshold is structural

Start with a uniform simple labelled d-regular graph on n vertices, with fixed d>=3. Attach a fixed finite system at each of m predetermined distinct vertices. Each attachment has one simple local mode calibrated to the host eigenvalue d, with nonzero coupling to the constant host vector. The precise calibration and the allowed polynomial couplings are in the [class theorem](structural/vector-port-v1.md).

There are two competing sources of an eigenvalue displacement above d. The collective mode sees all m attachments through the constant host vector. Its scale is sqrt(m/n). A nearby marked pair interacts through the tree Green function, whose strength decays like (d-1) to the negative graph distance. The strongest pair interaction has scale m squared/n. Equating the two scales gives m of order n^(1/3).

The [sharp theorem](root/sharp-growth-v1.md) makes this heuristic exact for the whole stated class. If s=sqrt(m/n), then, for every sequence 1<=m=o(n),

\[
\frac{\lambda_{\max}-d}{s}\longrightarrow\kappa
\quad\text{in probability}
\quad\Longleftrightarrow\quad
\frac{m^3}{n}\longrightarrow0.
\]

The attachment determines the positive constant kappa. The exponent is common to the class.

| Mark growth | Proved behavior |
| --- | --- |
| m=o(n^(1/3)) | The complete top m+1 cluster has collective shifts plus and minus kappa s, with the other shifts o_P(s) |
| m/n^(1/3) tends to c>0 | Collective modes coexist with random pair modes at the same scale |
| n^(1/3)<<m<<sqrt(n) | The top displacement has tight scale m squared/n and stays bounded away from zero at that scale |
| n^(1/3)<<m=o(n) | The top displacement divided by s diverges in probability. The preceding upper width claim is not extended to this entire range |

At criticality, nearby marked pairs form a matching with high probability on each retained distance scale. Distances are integers. Consequently their spectral strengths lie on a geometric lattice. If q=d-1 and the fractional part of log_q(1/s) tends to phi, the signed spectral measure away from zero tends to

\[
\delta_\kappa+\delta_{-\kappa}
+\sum_{j\in\mathbb Z}P_j
 \bigl(\delta_{h q^{\phi-j}}+\delta_{-h q^{\phi-j}}\bigr),
\qquad
\mathbb E P_j=\frac{d c^{3/2}}{2q}q^{j-\phi}.
\]

The P_j are independent Poisson variables. The full signed measure is not a Poisson process because its signs are paired and its collective levels are deterministic. Integer distances therefore remain visible in subsequential spectral laws.

## 2. What information about an attachment matters

Let C be its fixed internal symmetric matrix, and b(x) its vector polynomial describing the host coupling. Different attachment coordinates may use different polynomials. Let nu_d be the root spectral measure of the infinite d-regular tree. The local boundary matrix must satisfy

\[
K_0=dI-C-\int\frac{b(x)b(x)^T}{d-x}\,d\nu_d(x)\succeq0,
\qquad \ker K_0=\operatorname{span}(v),\qquad \|v\|=1.
\]

Choose the sign of v so beta=b(d)^T v>0. Set

\[
D=1+\int\frac{(b(x)^Tv)^2}{(d-x)^2}\,d\nu_d(x),
\qquad \kappa=\frac\beta{\sqrt D},
\qquad h=\frac{d-1}{d(d-2)}\kappa^2.
\]

These local quantities govern the collective strength, pair strength and physical mass. A unit pair mode has limiting mass 1/D in the added vertices and (D-1)/D in the original host. The theorem proves an actual graph-space lift and convergence of entire isolated spectral subspaces, including repeated pair levels.

Three simple unweighted cubic examples are covered by the same argument:

| Attachment at each mark | Added vertices | kappa squared | Pair coefficient h | Added-vertex mass of a pair mode |
| --- | --- | --- | --- | --- |
| One vertex joined to the mark's three neighbors | 1 | 9/8 | 3/4 | 1/8 |
| A triangle, with the mark joined to two triangle vertices | 3 | 18/31 | 12/31 | 11/31 |
| A seven-leaf star, with its center joined to the mark | 8 | 9/26 | 3/13 | 8/13 |

The general theorem also includes weighted and signed operators. Nonzero stationary coupling is essential. With the signed coupling (dI-A)E, independently marked vertices can instead support m exact compact modes at d, alongside the constant host mode. This cancellation example identifies a boundary of the theorem. It is not a counterexample within the positive unweighted examples above.

## 3. A finer collision has a different answer

For cubic duplication, set kappa=3/sqrt(8), s=sqrt(m/n), r=floor(log_2(1/s)) and w=(3/4)2^(-r)/s. The preceding round resolved a logarithmic negative-mode separation. This round assumes the finer deterministic tuning

\[
\frac{w-\kappa+(\kappa^2/2)sr}{s}\longrightarrow\beta\in\mathbb R.
\]

The [retuned graph theorem](root/retuned-graph-law-v1.md) centers the eigenvalues at

\[
\zeta_n=3-\kappa s-\frac{\kappa^2}{2}s^2r
\]

and examines physical scale s squared=m/n. If there are p marked pairs at distance r, the negative collision window has p+1 eigenvalues. Their limiting shifts are one random collective level L_p and the level 33/16-beta repeated p times.

L_p has a bounded smooth density and finite variance. When p>=1, either ordering of the collective and pair levels has positive probability for every finite beta. The limiting collective-to-pair coupling is zero at this scale. The rank-one collective subspace and the whole rank-p pair subspace still have definite, different physical masses. A basis within a repeated pair group is not selected.

The key mechanism is an exact combination of two fluctuations. A raw pair interaction of size t contributes t to one term and -t squared/(kappa+t) through elimination of complementary modes. Their sum is

\[
J(t)=t-\frac{t^2}{\kappa+t}=\frac{\kappa t}{\kappa+t}.
\]

This is bounded as t grows. Keeping the common Poisson variables in both terms converts an apparent infinite-mean fluctuation into the finite-variance collective law. Omitting that elimination correction gives the wrong answer. The proof handles every fixed pair multiplicity and shows that every finite beta is attainable with integer graph sizes.

## 4. What this contributes and what it leaves open

The conceptual progress is a local-to-global classification within a concrete class: a few local resonance quantities determine a common competition between collective and geometric pair modes. The fine cubic result also identifies a cancellation that changes the distribution, rather than only its constants.

The [priority audit](priority/PRIORITY-v1.md) checks nine primary sources on graph decoration, elimination, non-backtracking correspondence, growing-rank deformation and sparse localization. These methods are established. No inspected theorem directly supplies the combined result here. Historical firstness and correspondence to a named published open problem remain unverified. These are adjacency resonance results, with no claimed normalized-Laplacian, mixing-time or solver consequence.

The [formal packet](formalization/README-v2.md) contains 57 new finite supporting declarations and 16 unchanged reused declarations. A separate source replay passed all 73. Actual matrices, constructed profiles, lift identities, compact modes and finite Schur calculations are encoded. Random-graph probability, infinite-series convergence and the analytic transfer to graph spectral projections remain paper proofs.

The most useful next structural question is whether multiple local resonant directions split into one collective direction and a predictable family of dark directions, and at which scale those directions acquire interactions. The present theorem assumes a simple local kernel. The [next problem packet](NEXT_PROBLEM.md) specifies a bounded test of that extension.
