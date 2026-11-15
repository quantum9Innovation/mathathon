# The critical lattice spectral law

November 15, 2026. Owner: root. Revision 1, frozen for separate exact-revision review.

## 1. The limiting random object

Fix d>=3 and c>0. Use the uniform simple labelled d-regular host and critically weighted H=0 attachment B=sqrt(d-2)AE, with predetermined marks m/n^(1/3)->c. Define

\[
q=d-1,\quad s=\sqrt{m/n},\quad
\phi_n=\{\log_q(1/s)\},\quad
\kappa=\frac{d(d-2)^{3/2}}{\sqrt2 q},\quad
h=\frac{d(d-2)^2}{2q},\quad \vartheta=c^{3/2}.
\tag{1}
\]

Braces denote fractional part. Consider any subsequence on which phi_n tends to phi in [0,1]. The endpoint phi=1 is permitted, and will describe the same law as phi=0 after reindexing.

Let (P_k) indexed by all integers k be independent Poisson random variables with means

\[
\lambda_k(\phi)=\frac d{2q}\vartheta q^{k-\phi}.
\tag{2}
\]

Associate to each of its P_k occurrences the positive pair amplitude

\[
w_k(\phi)=h q^{\phi-k}.                                  \tag{3}
\]

Define the random measure on the punctured real line

\[
\Xi_\phi=\delta_\kappa+\delta_{-\kappa}
+\sum_{k\in\mathbb Z}P_k\bigl(\delta_{w_k}+\delta_{-w_k}\bigr).
\tag{4}
\]

The positive pair measure is a Poisson random measure on a geometric lattice. The full signed spectral measure (4) is not Poisson: each pair gives perfectly linked positive and negative atoms, and the collective atoms are deterministic.

For every epsilon>0, only finitely many atoms have absolute value greater than epsilon almost surely, since sum_(w_k>epsilon)lambda_k is finite. Their maximum is finite almost surely because this sum tends to zero as epsilon tends to infinity. There are infinitely many positive pair atoms accumulating at zero almost surely. For example, sum_(k>=1)Pr(P_k=0)=sum exp(-lambda_k)<infinity, so eventually P_k>0 by the first Borel-Cantelli lemma. Thus the positive atoms of (4), including kappa and multiplicities, have a well-defined decreasing ordering

\[
L_1(\phi)\ge L_2(\phi)\ge\cdots>0,
\qquad L_j(\phi)\longrightarrow0.
\tag{5}
\]

## 2. Spectral limit theorem

Let mu_1>=...>=mu_(n+m) be the eigenvalues of the actual augmented adjacency. For every fixed positive integer ell, along the stated phase subsequence,

\[
\left(
\left(\frac{\mu_j-d}{s}\right)_{j=1}^{\ell},
\left(\frac{d-\mu_{m+2-j}}{s}\right)_{j=1}^{\ell}
\right)
\xrightarrow{\mathrm d}
\left((L_j(\phi))_{j=1}^{\ell},(L_j(\phi))_{j=1}^{\ell}\right).
\tag{6}
\]

The top and bottom edges of the near-d cluster share the same limiting positive sequence. The symmetry is a statement about the limit, not an exact symmetry of each augmented graph.

The corresponding near-d spectral measure

\[
\Xi_n=\sum_{j=1}^{m+1}\delta_{(\mu_j-d)/s}
\]

converges in distribution, vaguely on the punctured real line, to (4). Atoms at zero are omitted when viewing these measures on that space. The bulk eigenvalues beyond this cluster are not part of the statement.

In particular,

\[
\frac{\mu_1-d}{s}\xrightarrow{\mathrm d}
X_\phi:=\max\left\{\kappa,\sup_{k:P_k>0}h q^{\phi-k}\right\}.
\tag{7}
\]

This is an explicit critical law. It holds for every predetermined label sequence, but not simultaneously over all marked sets. Outside degree three the critical attachment is weighted. An arbitrary nonzero interaction block H is not covered by this law.

## 3. Exact distribution of the top eigenvalue

For every real x,

\[
F_\phi(x):=\mathbb P(X_\phi\le x)=
\begin{cases}
0,&x<\kappa,\\
\displaystyle\exp\left[-\sum_{k:w_k(\phi)>x}\lambda_k(\phi)\right],&x\ge\kappa.
\end{cases}
\tag{8}
\]

The strict inequality in the sum is essential at lattice atoms. Summing the geometric series gives, for x>=kappa,

\[
F_\phi(x)=
\exp\left[
-\frac{d\vartheta}{2(q-1)}
q^{\lceil\phi+\log_q(h/x)\rceil-1-\phi}
\right].                                                \tag{9}
\]

Indeed, w_k>x is equivalent to k<phi+log_q(h/x), whose largest integer solution is ceil(phi+log_q(h/x))-1. Thus (9) is right continuous at every lattice point, including when a pair level coincides with kappa.

For the original cubic model,

\[
\kappa=3/\sqrt8,\qquad h=3/4,\qquad
\lambda_k=(3/4)c^{3/2}2^{k-\phi},\qquad
w_k=(3/4)2^{\phi-k}.
\tag{10}
\]

These formulas specify the entire limiting top distribution through c and one distance phase.

## 4. Proof by two-sided truncation

The geometric input is [the finite-window pair-count theorem](../probability/pair-counts-v1.md), SHA256 702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29. It proves joint convergence of the number of marked pairs at distances r_n+k to the independent Poisson counts (2), for each fixed finite set of k. Here r_n=floor(log_q(1/s)).

The spectral input is [the effective-operator theorem](effective-operator-v1.md), SHA256 13b559897d6ed9253a2fc6dd4dede5dd03914c078558d759542afc9c54d28864. For every fixed K>=0 it approximates the entire ordered scaled cluster by the collective values plus and minus kappa, the pair levels with distance at most r_n+K, and zeros. For every eta>0 the limiting upper probability of an error greater than eta is at most C eta^(-2)q^(-K). Its high-probability matching and uniqueness events are already included in that estimate.

There are two distinct truncations. Fix J,K>=0 and retain only pair offsets -J<=k<=K. The probability of discarding any stronger pair on the left is bounded uniformly in n by

\[
\mathbb P\{\text{some marked pair has distance}<r_n-J\}
\le C m^2q^{r_n-J}/n\le C_{d,c}q^{-J}.                   \tag{11}
\]

This is the deterministic ball-size bound and label symmetry. The same bound holds for the probability that the limiting Poisson family has any P_k>0 with k<-J, by summing its means.

For fixed J,K, the finite-window theorem, the deterministic convergence phi_n->phi and the continuous mapping theorem give convergence of the retained pair multiset together with the two collective atoms. This remains valid at collisions of amplitudes with kappa and at repeated pair levels. Conditional on any fixed finite vector of integer counts, the ordered, zero-padded lists are continuous functions of their amplitudes. Counts have the discrete topology, so this proves the assertion without a simple-eigenvalue assumption.

For the limiting object, all discarded weak levels with k>K have size at most

\[
h q^{\phi-K-1}\le h q^{-K}.                              \tag{12}
\]

Deleting them changes each positive or reflected-negative ordered coordinate, padded with zeros when necessary, by at most h q^(-K). The weak prelimit interactions are controlled by the effective theorem, not by an entrywise estimate or by their total absolute sum.

Apply these comparisons to any bounded Lipschitz function of the first ell upper and first ell reflected lower coordinates. The expectation difference is bounded by a multiple of the coordinate-error tolerance, plus the probabilities in (11), the corresponding limiting left-tail probability, and C eta^(-2)q^(-K). First send n to infinity for fixed J,K and eta, then J and K to infinity, then eta to zero. This proves (6) and hence (7).

For vague convergence, take finitely many continuous compactly supported test functions on the punctured line. Their supports lie at positive distance a from zero. Choose K so large that h q^(-K)<a/4. On an operator comparison event with error below a/4, only ideal eigenvalues with absolute value at least a/2 can contribute. Their number is tight by the finite-window Poisson convergence and (11). Uniform continuity of the test functions controls the changes of their values on this tight finite set. The same truncation argument proves joint convergence of the integrals of all such finite collections. Local tightness of counts follows from the same comparison, giving convergence of the random locally finite measures to (4).

Formula (8) now follows from independence of the Poisson counts. Only finitely much intensity is involved above each positive x, so the zero-count probability is exp minus that intensity. This also justifies the infinite product used there.

## 5. The distance phase is not erased by the spectrum

The laws at phi=0 and phi=1 coincide. Replacing k by k-1 simultaneously identifies their amplitudes and means. Apart from that identification, every two phases give distinct top laws.

To prove distinction, choose phi,psi in [0,1) with phi!=psi. Their geometric lattices are disjoint: h q^(phi-k)=h q^(psi-l) would imply phi-psi=k-l, an integer. Select any k with w_k(phi)>kappa. The top law at phase phi has a strictly positive atom there:

\[
\mathbb P(X_\phi=w_k(\phi))
=\exp\left[-\sum_{j<k}\lambda_j(\phi)\right]
\left(1-e^{-\lambda_k(\phi)}\right)>0.                    \tag{13}
\]

At phase psi the top is supported on {kappa} and its own pair lattice, so it has no atom at that point. Hence the distributions differ. This proves actual spectral phase dependence, not merely integer-distance oscillation.

The family phi->law(X_phi) is weakly continuous when [0,1] has its endpoints identified. For each finite window, Poisson means and amplitudes vary continuously in phi. The left-tail bound O(q^(-J)) and weak-amplitude bound O(q^(-K)) are uniform over phi in [0,1]. Finite-window convergence followed by these uniform truncations proves continuity, and the endpoint reindexing handles the quotient.

Consequently, for any admissible size sequence with m/n^(1/3)->c, the normalized top has a weak limit if and only if its distance phases converge on this circle. Sufficiency follows from continuity and the subsequence theorem. For necessity, if the phases fail to converge, compactness gives two subsequences with different circle limits. The limit theorem and (13) give distinct spectral limits on those subsequences, contradicting weak convergence of the original sequence.

## 6. No full-sequence law over all admissible sizes

Suppose n runs through all sufficiently large integers with nd even, and m(n)/n^(1/3)->c. Then

\[
\log_q(1/s)=\tfrac13\log_q n-\tfrac12\log_q c+o(1).
\tag{14}
\]

For any prescribed phi in (0,1), choose n_j to be a nearest admissible integer to

\[
c^{3/2}q^{3(j+\phi)}.
\tag{15}
\]

The rounding error is bounded, since admissible sizes have spacing at most two. Relative rounding error tends to zero. Equation (14) therefore tends to j+phi modulo one, so phi_(n_j)->phi. Every such phi occurs as a subsequential phase.

By Section 5, two different choices yield different top distributions. Thus the normalized top has no full-sequence weak limit over all admissible sizes. It has the explicit family of subsequential laws (8). Along a selected phase-convergent size sequence, a genuine weak limit does exist.

## 7. Tail behavior and interpretation

Before imposing the collective floor, the pair maximum is an extreme-value law on a geometric lattice. For x>=kappa, its displayed intensity lies between

\[
\frac{d h\vartheta}{2q(q-1)x}
\quad\hbox{and}\quad
\frac{d h\vartheta}{2(q-1)x}.                            \tag{16}
\]

Thus the top has reciprocal-order upper tails and infinite first moment. This is consistent with the previous theorem that the normalized finite-n expectations diverge despite tightness. No convergence of moments is inferred from weak convergence.

The formula also satisfies

\[
F_\phi(qx)=F_\phi(x)^{1/q}\quad(x>=\kappa).               \tag{17}
\]

The geometric oscillation is therefore retained in the limit. The untruncated pair maximum has the familiar discrete scaling of a max-semistable extreme-value law. The actual top has a deterministic collective floor, and the whole signed spectrum has paired dependence. These qualifications are part of the statement.

## 8. Limits and attribution

The proof covers the fixed-degree critical attachment with H=0 and predetermined marks. It gives eigenvalue laws and joint upper/lower cluster limits. It does not prove spatial localization of eigenvectors. It does not address a normalized Laplacian, mixing time or solver performance.

Poisson approximation, integer-distance subsequences, semistable extreme laws and spectral Poisson phenomena have established precedents. The [priority comparison](../priority/PRIORITY-v1.md) records them. The possible distinguishing content is this explicit law for bounded-degree partial neighbourhood duplication and its coexistence with the finite host's collective mode. Historical firstness and a match to an exact published open problem remain unverified.

The finite formal packet verifies its stated matrix components. The graph probability, analytic approximation, spectral transfer, infinite point process and weak-limit theorem remain paper arguments with separate reviews.
