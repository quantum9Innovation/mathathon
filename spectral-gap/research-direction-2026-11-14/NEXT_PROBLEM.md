# Collective resonances from duplicated cubic neighbourhoods

November 14, 2026, America/Los_Angeles.

Status: proposed mathematical target, unproved and not yet priority-cleared. This packet is a concrete next investigation, not a new accepted SG claim.

## Exact model

Let n tend to infinity through even integers. Let G_n be uniform among simple labelled cubic graphs on n vertices, with adjacency A_n. Fix a deterministic set of distinct labels c_1,...,c_m before sampling G_n. The integer m=m(n) may grow.

Add m new vertices v_1,...,v_m. For each i, join v_i to the three original neighbours of c_i. Keep every original vertex and edge. Add no edges between new vertices. The augmented adjacency is

\[
\mathcal A_n=
\begin{pmatrix}
A_n&A_n E\\
E^\top A_n&0
\end{pmatrix},
\qquad E=(e_{c_1},\ldots,e_{c_m}).
\]

The augmented graph is not cubic. Write its adjacency eigenvalues as \(\mu_1\ge\cdots\ge\mu_{n+m}\). Put \(s_n=\sqrt{m/n}\).

## Candidate conclusion

For each fixed \(0<\varepsilon<1/3\), and every sequence \(1\le m(n)\le n^{1/3-\varepsilon}\), test whether

\[
\frac{\mu_1-3}{s_n}\xrightarrow{\mathbb P}\frac3{\sqrt8},
\qquad
\frac{\mu_{m+1}-3}{s_n}\xrightarrow{\mathbb P}-\frac3{\sqrt8},
\]

and, for sequences with m>=2,

\[
\max_{2\le j\le m}\frac{|\mu_j-3|}{s_n}
\xrightarrow{\mathbb P}0.
\]

Interlacing gives \(\mu_{m+2}\le\lambda_2(A_n)\). The candidate therefore predicts two separated collective resonances and m-1 intermediate modes near 3. The m=1 case recovers SG-17.

This range is motivated by a crude proof route, not an optimal threshold claim. No distribution for the intermediate modes is proposed.

## The first unproved estimate

Let \(u=n^{-1/2}\mathbf1\), \(Q=I-uu^\top\), and work on a host-gap event \(\|A_n-3uu^\top\|\le3\rho\) for a fixed \(\rho<1\), whose probability tends to one. Define the m by m marked resolvent

\[
G_E(z)=E^\top Q(zI-A_n|_{u^\perp})^{-1}QE.
\]

The required estimate is

\[
\left\|G_E(3)-\frac23 I_m\right\|
=o_{\mathbb P}(s_n),
\tag{R1}
\]

with derivative convergence

\[
\left\|G_E'(3)+\frac{10}{9}I_m\right\|
\xrightarrow{\mathbb P}0.
\tag{R2}
\]

Use the same exceptional-event convention as SG-17. On the complement of the host-gap event, extend the resolvent quantities arbitrarily without using them in deterministic deductions.

SG-17 supplies the fixed-root diagonal estimate. It does not directly prove (R1) or (R2) when m grows.

## A discriminating proof attempt

Truncate the projected random-walk series at \(L=C\log n\), with C chosen to control the tail in operator norm. The fixed-root single-walk bound suggests total diagonal excess of order \(mL^3/n\). Label symmetry suggests total off-diagonal return mass of order \(m^2L/n\). The stationary subtraction contributes at most order \(mL/n\) in operator norm.

The critical comparison is

\[
\frac{m^2L/n}{\sqrt{m/n}}
=\frac{m^{3/2}L}{\sqrt n}\longrightarrow0
\]

in the proposed range. Derivative series add powers of L but only require o(1) control. These are proof-route estimates to establish, not already accepted uniform bounds.

Check the exact off-diagonal symmetry identity under the uniform simple graph law, keep conditioning on the host-gap event separate from unconditional nonnegative estimates, and bound the projected tail as an operator. Do not sum an entrywise tail m squared times when the operator norm gives a dimension-free estimate.

The expected number of host edges among marked labels is of order m squared over n. Their absence with high probability must be established before dropping \(E^\top A_n E\).

## Deterministic transfer

Eliminate the host subspace perpendicular to u, retaining u itself. The exact reduced Hermitian pencil near 3 is

\[
K_n(z)=
\begin{pmatrix}
z-3&-\frac3{\sqrt n}\mathbf1_m^\top\\
-\frac3{\sqrt n}\mathbf1_m&F_n(z)
\end{pmatrix},
\]

where

\[
F_n(z)=zI_m-E^\top A_n Q(zI-A_n|_{u^\perp})^{-1}QA_n E.
\]

The exact useful identity is

\[
F_n(z)=2zI_m-z^2G_E(z)+E^\top A_nE-\frac{z+3}{n}\mathbf1_m\mathbf1_m^\top.
\]

The term with the all-ones matrix must be retained. Under (R1), (R2), the host gap and absence of marked host edges, the expected expansion is

\[
F_n(3+s_n y)=8s_n y I_m+o_{\mathbb P}(s_n)
\]

uniformly for bounded y. After a fixed diagonal congruence, K_n has a rank-two leading perturbation with eigenvalues \(3s_n/\sqrt8\), \(-3s_n/\sqrt8\) and m-1 zeros.

The proof must still justify the root count and ordering for a growing-dimensional pencil. A determinant expansion alone is insufficient. A possible route uses monotonicity of K_n in z, uniform operator errors and inertia across intervals. Interlacing then identifies which augmented eigenvalues the roots represent.

## Falsification and scope checks

1. Reconstruct m=1 with the exact SG-17 coefficient and stationary correction.
2. Derive m=2 explicitly, including the intermediate mode and the off-diagonal resolvent term.
3. Test graph-dependent or conditioned choices forced to be adjacent or to lie on a short cycle. Those choices change the sampling model. Rare such realizations of predetermined labels remain allowed and must be controlled probabilistically.
4. Distinguish an adjacency resonance from the normalized-Laplacian mixing gap.
5. Compare the proposed growing-rank regime with existing sparse finite-rank perturbation and local-law results before asserting novelty.

Success for the next bounded round is a proof and separate review of (R1), (R2) and the deterministic transfer, or the first precise obstruction with a revised target justified by evidence. Do not weaken the model or parameter range silently.

The larger research question is where collective modes stop following this law as defect density or local interactions increase. That question is not answered by proving a small safe range.
