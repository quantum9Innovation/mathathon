# Growing defect resonances in random regular graphs

November 15, 2026, America/Los_Angeles.

The requested growing-defect theorem is proved in paper form and has passed a separate review of its complete dependency chain. The result extends to a weighted family at every fixed degree, with arbitrary bounded weak interactions among the defects. A further reviewed theorem describes the mass and direction of the collective eigenvectors. Key finite matrix steps are checked in Lean. The complete probability theorem is not formalized.

## Main graph theorem

Start with a uniform simple labelled cubic graph on n vertices. Fix m distinct labels before sampling. Add one new vertex for each label, connected to that label's three original neighbours. Keep the original graph and add no edges among new vertices.

For

\[
m^3(\log n)^2/n\longrightarrow0,\qquad s=\sqrt{m/n},
\]

the largest m+1 adjacency eigenvalues satisfy

\[
\mu_1=3+\frac3{\sqrt8}s+o_{\mathbb P}(s),
\qquad
\mu_{m+1}=3-\frac3{\sqrt8}s+o_{\mathbb P}(s),
\]

\[
\max_{2\le j\le m}|\mu_j-3|=o_{\mathbb P}(s).
\]

The middle formula applies when m>=2. Interlacing bounds every remaining upper eigenvalue by the original host's second eigenvalue. This contains the entire requested range \(m\le n^{1/3-\varepsilon}\).

Read the [complete graph proof](root/graph-theorem-v1.md), its [independent full-chain review](reviews/combined-v1-review.md), and the [second application review](reviews/application-by-probability-v1.md). The latter declares its author's role in developing the probability input.

## Why the cluster has this shape

All defects couple to the same constant host vector. Their collective sum therefore creates two split modes. Combinations perpendicular to that sum have zero shift at the first scale. The theorem controls all m-1 intermediate eigenvalues together, even as m grows.

The proof has three ingredients:

1. A [marked-resolvent estimate](probability/proof-v1.md) controls an entire m by m matrix at a scale smaller than sqrt(m/n). It uses one-walk exposure for diagonal errors, exact label symmetry off the diagonal, and an operator bound for the tail.
2. An [exact Schur reduction](root/transfer-v1.md) retains the host's isolated eigenvector and the stationary correction.
3. A dimension-free inertia and eigenvalue comparison transfers the small effective matrix into all ordered graph eigenvalues. Repeated effective eigenvalues require no spacing assumption.

For m=2, the top and third eigenvalues are \(3\pm3/(2\sqrt n)+o_{\mathbb P}(n^{-1/2})\). The second remains \(3+o_{\mathbb P}(n^{-1/2})\). This is collective interaction through a common host mode, rather than two independent copies of the one-defect split.

## Structural extension

For fixed d>=3, use attachment matrix \(B=\sqrt{d-2}\,AE\), and give the added sector a symmetric interaction matrix sH with bounded norm. Define

\[
D_d=\frac{2(d-1)^2}{(d-2)^2},
\qquad
\kappa_d=\frac{d(d-2)^{3/2}}{\sqrt2(d-1)},
\qquad e=m^{-1/2}\mathbf1_m.
\]

The entire ordered near-d cluster, shifted by d and divided by s, is approximated with maximum error tending to zero in probability by the eigenvalues of

\[
\begin{pmatrix}
0&\kappa_d e^\top\\
\kappa_d e&H/D_d
\end{pmatrix}.
\]

One graph event supports this approximation for every H in a fixed operator-norm ball. Thus H can be chosen after observing the graph. The marked labels cannot be selected that way. For d other than three, the attachment is weighted. An arbitrary H can include diagonal potentials and signed interactions.

This is the structural conclusion beyond the original example. It predicts the whole interacting cluster from a specified effective matrix while exposing the required probabilistic input.

## Eigenvector consequence

The [reviewed mass theorem](root/eigenvector-masses-v1.md) applies when H=0. Each of the two extreme collective modes has asymptotically half its squared norm in the original host's constant direction.

In the cubic case, its other masses are 1/16 on the added vertices and 7/16 in the perpendicular host component. Each intermediate unit eigenvector has vanishing constant-direction mass, mass 1/8 on added vertices, and mass 7/8 in the perpendicular host component. These statements hold uniformly within repeated intermediate eigenspaces.

The extreme modes are therefore hybrids. This does not prove a spatial decay profile or pure localization. The [exact-revision review](reviews/eigenvector-masses-v1-review.md) checks the normalization through the actual resolvent derivative.

## Formal verification

The [formalization record](formalization/README.md) identifies the exact encoded objects and remaining bridges. Three source files prove:

- The actual finite collective matrix's two nonzero eigenvectors, exclusion of other nonzero eigenvalues, and its kernel membership criterion.
- Selection-matrix compression and the correct stationary correction.
- Construction of the centered projected inverse from an invertible shifted matrix, followed by the actual marked identity at the host eigenvalue.

The final sources contain 27 checked theorems, with no sorry, admitted proof or custom axiom. Printed dependencies use only standard foundational axioms. Fresh source compilations passed with pinned Lean 4.31.0 and mathlib revisions, using an existing dependency cache read-only.

The spectral-gap hypothesis implying shifted invertibility, the random-graph probability estimates, derivative limits, inertia and ordered multiplicities, and final asymptotic transfer remain paper bridges. Declaration count does not measure how much of the random-graph theorem is formalized. The [independent scope audit](reviews/formal-scope-v2.md) records these boundaries.

An additional [exact rational diagnostic](root/check_finite_algebra.py) passes 120 finite cases on three cubic hosts, including 24 evaluations at the Perron eigenvalue. It checks algebra and does not prove the asymptotics.

## Priority and significance

The [primary-source audit](priority/PRIORITY-v1.md) compares the result with fixed-rank deformation theory, Huang's growing-rank work, regular-graph local laws and tree scattering. A [separate overlap comparison](priority/EIGENVECTOR_PRIORITY-v1.md) covers the eigenvector extension.

Compressed resolvents, effective matrices, inertia transfer and derivative overlap formulas are established methods. The inspected theorems do not directly provide the stated fixed-degree regular-graph precision and localized growing-defect law. Historical firstness remains unverified, and no exact published open problem corresponding to this target was identified.

The credible contribution candidate is the quantitative graph input and its consequences in this model. The theorem does not establish an optimal m threshold, a bulk-edge transition, a smaller-scale law for the intermediate modes, improved mixing, or a solver guarantee.

## Reproduction and next frontier

From the workspace root, the finite diagnostic runs with:

~~~text
python3 mathathon/spectral-gap/growing-defects-round-01/root/check_finite_algebra.py
~~~

The pinned formal validation runs with:

~~~text
python3 mathathon/spectral-gap/growing-defects-round-01/formalization/validate.py
~~~

The latter accepts explicit toolchain and dependency-cache paths. It compiles the local proof sources anew and does not rebuild or modify another project's dependencies. See the formalization record for the exact environment and limits.

The [handoff](HANDOFF.md) and [verification receipt](VERIFICATION.json) bind the final evidence. The canonical statuses are SG-19, SG-20 and SG-21 in [CLAIM_LEDGER.md](../CLAIM_LEDGER.md).

The next unresolved structural question is whether the n^(1/3) power marks the onset of marked-pair interactions. The present proof does not establish that threshold or remove the logarithmic loss. A converse or an effective theory retaining the first close pairs would be new work, beyond this completed round.
