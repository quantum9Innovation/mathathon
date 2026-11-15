# Collective resonances for growing defect sets in random regular graphs

November 15, 2026, America/Los_Angeles.

Status at freezing: complete assembled paper proof awaiting separate review. The original cubic graph target is proved below from two frozen component arguments. A weighted fixed-degree family with arbitrary weak interactions supplies the structural extension. Priority and formalization scope remain separate.

## 1. The original unweighted cubic theorem

Let n tend through even integers, and let G_n be uniformly sampled among simple labelled cubic graphs on n vertices. Let A_n be its adjacency matrix. For each n choose distinct labels c_1,...,c_m deterministically before sampling, where m=m(n)>=1 satisfies

\[
\frac{m^3(\log n)^2}{n}\longrightarrow0.
\tag{1}
\]

Add new vertices v_1,...,v_m. Join v_i to the three original neighbours of c_i, keep all original vertices and edges, and add no edges between new vertices. Set \(E=(e_{c_1},\ldots,e_{c_m})\), so the augmented adjacency is

\[
\mathcal A_n=
\begin{pmatrix}A_n&A_nE\\E^\top A_n&0\end{pmatrix}.
\]

Let its eigenvalues be \(\mu_1\ge\cdots\ge\mu_{n+m}\) and put \(s_n=\sqrt{m/n}\). Then

\[
\frac{\mu_1-3}{s_n}\xrightarrow{\mathbb P}\frac3{\sqrt8},
\qquad
\frac{\mu_{m+1}-3}{s_n}\xrightarrow{\mathbb P}-\frac3{\sqrt8}.
\tag{2}
\]

For sequences with m>=2,

\[
\max_{2\le j\le m}\frac{|\mu_j-3|}{s_n}
\xrightarrow{\mathbb P}0.
\tag{3}
\]

For every realized graph,

\[
\mu_{m+2}\le\lambda_2(A_n).
\tag{4}
\]

With probability tending to one, these are precisely the m+1 eigenvalues in a shrinking neighbourhood of 3 and all other eigenvalues lie below a fixed smaller threshold. The graph is not regular after augmentation.

Condition (1) includes every requested sequence \(1\le m\le n^{1/3-\varepsilon}\), for fixed \(0<\varepsilon<1/3\). No assumption that m tends to infinity is made. The proof does not claim that (1) is optimal.

The following stronger statement implies (2) through (4).

## 2. A structural weighted family

Fix an integer d>=3. Let A_n be the adjacency of a uniform simple labelled d-regular graph, along nd even. Choose E and m as above with (1). Put

\[
a=d-2,\qquad s_n=\sqrt{m/n},\qquad
D_d=\frac{2(d-1)^2}{(d-2)^2},\qquad
\kappa_d=\frac{d(d-2)^{3/2}}{\sqrt2(d-1)}.
\tag{5}
\]

Let H be any real symmetric m by m matrix and define

\[
\mathcal A_n(H)=
\begin{pmatrix}
A_n&\sqrt a\,A_nE\\
\sqrt a\,E^\top A_n&s_n H
\end{pmatrix}.
\tag{6}
\]

For d=3 and H=0 this is exactly the original unweighted graph. For other d, the new-to-host edges have weight sqrt(d-2). A general H describes symmetric interactions and diagonal potentials in the new sector, not necessarily the adjacency of a simple graph.

Write \(e_m=m^{-1/2}\mathbf1_m\), and form the explicit (m+1) by (m+1) matrix

\[
\mathcal M_{d,m}(H)=
\begin{pmatrix}
0&\kappa_d e_m^\top\\
\kappa_d e_m&H/D_d
\end{pmatrix}.
\tag{7}
\]

Let \(\theta_1(H)\ge\cdots\ge\theta_{m+1}(H)\) be its eigenvalues. For every fixed finite H_0>=0,

\[
\sup_{\substack{H=H^\top\\\|H\|\le H_0}}
\max_{1\le j\le m+1}
\left|
\frac{\mu_j(\mathcal A_n(H))-d}{s_n}-\theta_j(H)
\right|
\xrightarrow{\mathbb P}0.
\tag{8}
\]

The supremum is over all such matrices of the current dimension, on the same sampled host. Thus H may also be selected after observing the host, provided its norm is bounded by H_0. The marked labels must still have been fixed before sampling. No simultaneous statement over all possible marked sets is asserted.

With probability tending to one, uniformly over the displayed H, there are exactly m+1 eigenvalues in \((d-Ls_n,d+Ls_n)\) for a fixed L depending only on d and H_0. All remaining upper eigenvalues obey

\[
\mu_{m+2}(\mathcal A_n(H))\le\lambda_2(A_n).
\tag{9}
\]

The effective matrix may have collisions or repeated eigenvalues. No eigenvalue spacing hypothesis is required.

## 3. Frozen proof inputs

The [probability theorem](../probability/proof-v1.md), SHA256
56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b,
provides the following statements.

For \(u=n^{-1/2}\mathbf1\), \(Q=I-uu^\top\), choose fixed
\(2\sqrt{d-1}/d<\rho<1\). The event

\[
\mathcal H_n=\{\|A_n-duu^\top\|\le d\rho\}
\tag{10}
\]

has probability tending to one. On it define

\[
G_E(z)=E^\top Q(zI-A_n|_{u^\perp})^{-1}QE.
\]

Under (1),

\[
\|G_E(d)-gI_m\|=o_{\mathbb P}(s_n),\qquad
\|G_E'(d)-g'I_m\|=o_{\mathbb P}(1),
\tag{11}
\]

where

\[
g=\frac{d-1}{d(d-2)},\qquad
g'=-\frac{(d-1)((d-1)^2+1)}{d^2(d-2)^3}.
\tag{12}
\]

The probability theorem defines these quantities arbitrarily off the good event and uses inverses only on it. It also gives

\[
\Pr(E^\top A_n E\ne0)\le\frac{dm(m-1)}{2(n-1)}=o(1).
\tag{13}
\]

The [finite deterministic transfer](transfer-v1.md), SHA256
deb05e53631ad4d273f48b2d6253014352c1263010d3990ebcc4e0b616351b99,
compares the whole cluster to an effective matrix through a dimension-free explicit error. It requires a fixed gap below the isolated host eigenvalue, bounded attachment norm, a positive reference derivative, and the value and derivative errors checked below.

The probability input itself uses a published host-gap theorem and positive limiting simplicity probability, with exact source passages recorded there. These are external mathematical dependencies, not formalized inputs in this packet.

## 4. The projected identity including the stationary term

Work on (10). The orthogonal complement of u is A_n-invariant. Let

\[
R_Q(z)=Q(zI-A_n|_{u^\perp})^{-1}Q.
\]

On that complement, \(A_nR_Q(z)=zR_Q(z)-Q\). Since A_n commutes with Q,

\[
A_nR_Q(z)A_n=z^2R_Q(z)-zQ-A_nQ.
\tag{14}
\]

Compress by E. Because \(E^\top E=I_m\), \(E^\top uu^\top E=J_m/n\), and \(A_nuu^\top=d uu^\top\), equation (14) becomes

\[
E^\top A_nR_Q(z)A_nE
=z^2G_E(z)-zI_m-E^\top A_nE+\frac{z+d}{n}J_m.
\tag{15}
\]

For \(B=\sqrt a\,A_nE\), \(C=s_nH\), the actual Schur regular part is therefore

\[
F_H(z)
=(d-1)zI_m-s_nH-a z^2G_E(z)
+aE^\top A_nE-\frac{a(z+d)}nJ_m.
\tag{16}
\]

The sign of the stationary correction and its inclusion at z=d are essential. No full-space inverse at the Perron pole has been used.

## 5. Calibration and error bounds

The choice a=d-2 makes the limiting constant in (16) vanish at z=d:

\[
(d-1)d-a d^2g=0.
\tag{17}
\]

On the additional event \(E^\top A_nE=0\), let \(Z_H=-s_nH\). Formula (16) gives

\[
\|F_H(d)-Z_H\|
\le a d^2\|G_E(d)-gI_m\|+2ad\,m/n
=o_{\mathbb P}(s_n).
\tag{18}
\]

The bound has no dependence on H. Here \(m/n=s_n^2=o(s_n)\).

Differentiating (16),

\[
F_H'(d)
=(d-1)I_m-a(2dG_E(d)+d^2G_E'(d))-\frac anJ_m.
\]

Substitution of (12) gives

\[
(d-1)-a(2dg+d^2g')=\frac{2(d-1)^2}{(d-2)^2}=D_d.
\tag{19}
\]

Consequently

\[
\|F_H'(d)-D_dI_m\|
\le a\left(2d\|G_E(d)-gI_m\|
+d^2\|G_E'(d)-g'I_m\|+m/n\right)
=o_{\mathbb P}(1).
\tag{20}
\]

This estimate is also independent of H. Moreover, \(\|B\|\le d\sqrt a\) because E is an isometry and ||A_n||=d. The host-complement upper spectral gap is \(\gamma=d(1-\rho)>0\).

These are exactly the deterministic transfer hypotheses with reference derivative \(D=D_dI_m\). Its coupling vector is

\[
b=B^\top u=\frac{d\sqrt a}{\sqrt n}\mathbf1_m.
\tag{21}
\]

Thus its effective matrix T_H satisfies the exact identity

\[
T_H=s_n\mathcal M_{d,m}(H).
\tag{22}
\]

The sign in the lower-right block is positive H/D_d because Z_H=-s_nH.

## 6. Uniform whole-cluster transfer

For ||H||<=H_0, equation (7) gives

\[
\|\mathcal M_{d,m}(H)\|\le\kappa_d+H_0/D_d.
\]

Fix \(L>\kappa_d+H_0/D_d+1\), and set \(h_n=Ls_n\). For all sufficiently large n, h_n<gamma/2.

In the finite transfer bound, let

\[
e_{0,n}=a d^2\|G_E(d)-gI_m\|+2ad\,m/n,
\]

\[
e_{1,n}=a\left(2d\|G_E(d)-gI_m\|
+d^2\|G_E'(d)-g'I_m\|+m/n\right).
\]

Equations (18) and (20) show \(e_{0,n}/s_n\to0\) and \(e_{1,n}\to0\) in probability. Uniformly over H,

\[
\frac{\eta_{h_n}}{s_n}
\le\frac1{D_d}\left(
\frac{e_{0,n}}{s_n}+L e_{1,n}
+\frac{ad^2L^2s_n}{(\gamma-h_n)^3}
\right)
\xrightarrow{\mathbb P}0.
\tag{23}
\]

Intersect the host-gap event, the no-marked-edge event, and the event that the right side of (23) is less than one. Its probability tends to one. On this one event the finite transfer theorem applies to every H in the norm ball. It gives the uniform ordered comparison (8), as well as exactly m+1 eigenvalues in the displayed shrinking interval.

The supremum in (8) is measurable. For each finite n and each host, the admissible H form a compact subset of a finite-dimensional space. Ordered eigenvalues depend continuously on matrix entries, so the supremum is a maximum of a continuous function. The host probability space is finite.

Finally, A_n is a principal submatrix of (6). Interlacing gives (9) on every graph, for every H. This completes the structural theorem.

## 7. Original theorem and worked cases

For d=3 and H=0, equations (5) and (7) give \(D_3=8\), \(\kappa_3=3/\sqrt8\), and

\[
\mathcal M_{3,m}(0)=
\begin{pmatrix}
0&(3/\sqrt8)e_m^\top\\
(3/\sqrt8)e_m&0
\end{pmatrix}.
\]

Its eigenvalues are \(3/\sqrt8\), \(-3/\sqrt8\), and zero with multiplicity m-1. The explicit orthogonal decomposition is given in Section 6 of the deterministic transfer proof. Equation (8) now proves (2) and (3), and (9) proves (4).

For m=1, this recovers the two SG-17 displacements. For m=2, the top and third eigenvalues are

\[
3+\frac{3}{2\sqrt n}+o_{\mathbb P}(n^{-1/2}),
\qquad
3-\frac{3}{2\sqrt n}+o_{\mathbb P}(n^{-1/2}),
\]

and the second is \(3+o_{\mathbb P}(n^{-1/2})\). The two defects couple to the same constant host vector. Their sum couples to that vector, while their difference is orthogonal to it at leading order.

The structural statement also describes weak interactions. If \(H=hI_m\), the m-1 orthogonal modes have effective eigenvalue h/D_d, and the other two effective eigenvalues are

\[
\frac{h/D_d\pm\sqrt{(h/D_d)^2+4\kappa_d^2}}2.
\tag{24}
\]

More generally, whenever \(He_m=h e_m\), the orthogonal sector inherits \(H|_{e_m^\perp}/D_d\) and the remaining two eigenvalues are still (24). Arbitrary H need not preserve that decomposition, but (8) still predicts all ordered eigenvalues using the finite matrix (7).

## 8. A boundary case that changes the hypotheses

The marked set is fixed before sampling. It is not valid to choose marks after seeing the graph so as to force close pairs while retaining the scalar approximation (11).

For example, the Green matrix on two adjacent vertices in the infinite cubic tree, evaluated at z=3, is

\[
\begin{pmatrix}2/3&1/3\\1/3&2/3\end{pmatrix}.
\]

The off-diagonal entry is \(g_3(3)r(3)=(2/3)(1/2)=1/3\). It is not a vanishing error to \((2/3)I_2\). Retaining their adjacency in (16) at d=3 gives the limiting regular part with off-diagonal entry -2 and diagonal zero when H=0. Such geometry requires a different effective matrix and is outside the scalar critical approximation.

Predetermined labels can still be adjacent on rare realizations of the stated model. Equation (13) controls those realizations, rather than excluding them from the sample space.

## 9. What remains unproved

No optimal growth threshold, logarithm-free endpoint, residual distribution of the intermediate modes, or bulk-edge transition is asserted. The m^(1/3) scale may reflect first close-pair interactions, but that geometric interpretation needs a separate theorem.

The adjacency law does not imply a vanishing normalized-Laplacian gap or a solver advantage. Deliberate weighted or unweighted attachments do not supply occurrence probabilities for spontaneous tangles in a different random graph model.

The proof mechanism uses classical Schur complements, inertia, perturbation bounds and tree Green functions. The potential contribution is the localized marked-resolvent precision and the resulting finite-host collective law, including the uniform weak-interaction extension. The bounded priority audit has not certified historical firstness.
