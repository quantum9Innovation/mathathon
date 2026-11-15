# The retuned negative graph law and spectral subspaces

November 15, 2026. Owner: root. Revision 1, frozen for independent review.

Status: proposed complete paper application of the frozen probability chain. Historical priority and full formalization are separate questions.

Exposure: the author reconstructed the compensated quadratic, signed coupling and collective self-energy proofs. The self-energy formula and a Fourier argument were discussed with the probability author before their respective freezes. This file is the actual graph root and physical-subspace application. It is not an independent probability proof.

## 1. Model and finer tuning

Let A be a uniform simple labelled cubic adjacency matrix on even n vertices. Let E select m predetermined distinct labels and set

\[
\mathcal A=\begin{pmatrix}A&AE\\E^\top A&0\end{pmatrix},
\qquad m/n^{1/3}\longrightarrow c>0.
\]

Write

\[
s=\sqrt{m/n},\quad \theta=c^{3/2},\quad
\kappa=3/\sqrt8,\quad
r=\lfloor\log_2(1/s)\rfloor,\quad
w=\frac34\,2^{-r}/s.
\]

Assume the deterministic next detuning satisfies

\[
\beta_n=\frac{w-\kappa+(\kappa^2/2)sr}{s}
\longrightarrow\beta\in\mathbb R.
\tag{1}
\]

This implies distance phase tending to 1/2 and the preceding logarithmic retuning. Define the physical center and fixed coarse window

\[
\zeta_n=3-\kappa s-\frac{\kappa^2}{2}s^2r,
\qquad
I_n=3+s(-\kappa-\epsilon,-\kappa+\epsilon),
\tag{2}
\]

where epsilon>0 is fixed and sufficiently small, for example epsilon=kappa/10. Let p_n be the number of unordered marked pairs at host distance r.

## 2. Limit law

Let P_k, k in Z, be independent Poisson variables with

\[
\lambda_k=\frac{\kappa\theta}{2}2^k
=\frac{3\theta}{4\sqrt2}2^k,\qquad
t_k=\kappa2^{-k},\qquad
J(t)=\frac{\kappa t}{\kappa+t}.
\tag{3}
\]

Define the finite random variable

\[
\mathcal L=\frac{51}{32}
+\frac1\theta\left[
\sum_{k\le0}J(t_k)P_k
+\sum_{k\ge1}\bigl(J(t_k)P_k-t_k\lambda_k\bigr)
\right].
\tag{4}
\]

The positive-offset series is a convergent centered L2 series plus a summable deterministic drift. The negative-offset sum has finite intensity and bounded jumps. In particular the combined variable has finite second moment, despite the infinite-mean terms in its earlier uncombined representation.

**Theorem 1.** With probability tending to one, the actual adjacency matrix has exactly p_n+1 eigenvalues in I_n. Their fine-scale point measure converges jointly with p_n:

\[
\left(p_n,\ \sum_{\mu\in\operatorname{spec}(\mathcal A)\cap I_n}
\delta_{(\mu-\zeta_n)/s^2}\right)
\ \Longrightarrow\
\left(P_0,\ \delta_{\mathcal L}+P_0\,\delta_{33/16-\beta}\right).
\tag{5}
\]

Eigenvalues and atoms are counted with multiplicity. Conditional on p_n=p, for every fixed p>=0, the p+1 ordered shifts converge to the ordering of

\[
\mathcal L_p,\quad 33/16-\beta
\text{ repeated }p\text{ times},
\tag{6}
\]

where L_p has the law of L conditional on P_0=p.

Every L_p has a bounded smooth density. For p>=1 the collective and pair limiting levels are distinct almost surely, and both possible orderings have positive probability for every finite beta. The conditional moments of the limit are

\[
\mathbb E\mathcal L_p=\frac{51}{32}+\frac{\kappa p}{2\theta},
\qquad
\operatorname{Var}(\mathcal L_p)
=\frac{\kappa^3}{\theta}
\sum_{k\ge1}\frac{2^k}{(1+2^k)^2}.
\tag{7}
\]

No convergence of the finite-n moments is asserted. The new physical scale is s squared=m/n, of order n^(-2/3). It is smaller than the previously resolved s squared r scale.

Every finite beta in (1) is attained by admissible even integer n and integer m with the specified c. There is no additional forced restriction on beta from integer graph sizes. The earlier distance phase alone does not determine this next law.

## 3. Actual physical subspaces

Let u be the constant unit host vector, and on a fixed host-gap event let R_Q(z) be the projected host resolvent. On the high-probability short-matching event, let a_1,...,a_p be the unit antisymmetric marked vectors for the p pairs at distance r, extended by zero in the retained host coordinate. Let f be the unit constant vector on the m-2p remaining marked coordinates, and put

\[
c_-=(h-f)/\sqrt2,\qquad
\mathcal J_0(\alpha,v)=
\left(\alpha u+R_Q(3)AEv/\sqrt8,\ v/\sqrt8\right).
\tag{8}
\]

The single host coordinate is denoted h. For p=0 the list of pair vectors is empty and f=e. All definitions can be extended arbitrarily on exceptional events.

Conditional on each fixed p, the actual graph eigenvalue corresponding to L_p has a rank-one spectral projection approaching the orthogonal projection onto span(J_0 c_-) in operator norm. The other p eigenvalues in I_n have a combined rank-p spectral projection approaching the projection onto

\[
\operatorname{span}\{\mathcal J_0a_1,\ldots,\mathcal J_0a_p\}.
\tag{9}
\]

For p=0 only the first assertion remains. These projections are well defined with conditional probability tending to one by the separation of the two fine-scale levels. One may identify the collective eigenvalue as the unique eigenvector in the window whose squared projection onto the constant host direction tends to 1/2. Ties in an exceptional finite-n labeling can be resolved arbitrarily.

The physical masses, in the order constant host direction, added vertices, and host perpendicular to the constant direction, are

\[
\text{collective}:\quad (1/2,1/16,7/16),
\qquad
\text{pair subspace}:\quad (0,1/8,7/8).
\tag{10}
\]

For the pair subspace this is a uniform quadratic-form statement for all its unit vectors. The theorem does not select individual vectors inside the p-dimensional pair group when p>1.

The leading signed collective-to-pair coupling is zero at this scale. The random ordering in (5) therefore comes from diagonal fluctuations and not from a nonzero limiting avoided-crossing matrix.

## 4. Frozen probability premises

The argument uses these exact files:

- probability/collective-limit-v1.md, SHA256 e492d3dfa506167ba28782e316129146e72f8046e96bbaf50b265e42d3fc307d.
- probability/signed-coupling-v1.md, SHA256 68660a0914a02b0a6bf53f2ccef75a2b844859e9dafc7f8a9e106db3921d5fba.
- probability/collective-self-energy-v1.md, SHA256 a3c6b1b42bed9f7f3c7c5d45c1292df5a207951e709e318db24f6f711c9d9d4d.
- probability/density-and-tuning-v1.md, SHA256 cf3e7ef384fad52dd78f22fbdb2d121a8c99049f4736012c4a7dfeae14a91098.
- probability/multiplicity-extension-v1.md, SHA256 2649c74230d20b7411cdf1a92276c63b8181e0674e53d5f58e87a63918f796cc.

They have separate reconstruction reviews. The accepted SG-27 and SG-28 graph proofs provide the coarse cluster count and the physical Gram estimates, with revisions recorded in input/PRIOR_BASELINE.json. The present application uses an exact energy-dependent Schur equation, so it does not infer a fine-scale theorem from the older O_P(s) normalized-cluster remainder.

## 5. Exact graph equation and the retained small block

Put

\[
F(z)=zI-E^\top A R_Q(z)AE,
\qquad
\mathcal T_n(x)=
\begin{pmatrix}
0&\kappa e^\top\\
\kappa e&xI-F(3+sx)/(8s)
\end{pmatrix}.
\tag{11}
\]

Elimination of the positive host complement from zI-Acal, followed by congruence by diag(1,8^(-1/2)I) and division by s, gives exactly

\[
xI-\mathcal T_n(x).
\tag{12}
\]

Its kernel reconstructs the actual graph eigenvector. This identity is valid at the host pole x=0 because the host constant direction has been retained.

Condition on p_n=p for a fixed p. Let U_- have columns c_-,a_1,...,a_p and let Q_-=I-U_-U_- transpose. In the coarse window about -kappa, the complementary compression has a fixed spectral gap with conditional probability tending to one. This uses the already reviewed fixed cutoff then increasing-cutoff argument. Thus the second Schur reduction is exact:

\[
xI_{p+1}-\mathcal B_n(x),
\]

\[
\mathcal B_n(x)=U_-^\top\mathcal T_n(x)U_-
+U_-^\top\mathcal T_n(x)Q_-
(xI-Q_-\mathcal T_n(x)Q_-)^{-1}
Q_-\mathcal T_n(x)U_-.
\tag{13}
\]

Write x_n^0=-kappa-(kappa squared/2)sr. The frozen probability chain establishes, uniformly for |x-x_n^0|<=Ms for each fixed M,

\[
\mathcal B_n(x)=x_n^0 I_{p+1}
+s\,\operatorname{diag}(L_{n,p},(33/16-\beta_n)I_p)
+o_P(s),
\tag{14}
\]

where L_(n,p) converges in law to L_p. The off-diagonal block is o_P(s) and the error in the full pair block is o_P(s), in operator norm for this fixed p. The complementary coupling columns are O_P(sqrt(s)) for the collective direction and o_P(sqrt(s)) for the pair directions.

The same proofs show that the norm of the derivative B_n'(x) is o_P(1) uniformly on the interval. Indeed T_n'(x)=O_P(s log squared n). The derivative of the complementary inverse is bounded, while its coupling columns are O_P(sqrt(s)). The derivative of the resulting self-energy is O_P(s), with smaller terms from differentiating the columns.

## 6. Ordered root comparison

Choose M large enough to contain the deterministic pair coefficient and, with high conditional probability, the tight variable L_(n,p). On the event of (14) with error less than a fixed small multiple of s, the matrix xI-B_n(x) is negative definite at x=x_n^0-Ms and positive definite at x=x_n^0+Ms. Its derivative is positive definite because ||B_n'||<1/2 with probability tending to one.

Every ordered eigenvalue of this symmetric matrix is therefore strictly increasing through zero. There are exactly p+1 roots in the interval, counted with multiplicity. Weyl comparison in (14), or the inertia argument applied at each ordered diagonal value plus or minus the uniform error, shows that their rescaled displacements differ by o_P(1) from the ordering of

\[
L_{n,p},\quad 33/16-\beta_n\text{ repeated }p\text{ times}.
\tag{15}
\]

The two exact Schur reductions preserve kernel multiplicity and the change in inertia, so these roots are precisely the actual graph eigenvalues in this neighborhood. The previous coarse critical subspace theorem gives exactly p+1 eigenvalues in I_n. Hence none have been lost by taking M large and then letting it increase. This proves the conditional ordered form (6).

The pair count converges to Poisson(lambda_0), so it is tight. For every finite p range the preceding conditional limits and error bounds apply. Truncating that range and then removing the truncation proves the joint finite-point-measure limit (5). This does not interchange an unbounded conditional estimate with a limit.

## 7. Noncoincidence and projector transfer

The density proof gives P(L_p=33/16-beta)=0. Fix a small delta>0 and work on the event

\[
|L_{n,p}-(33/16-\beta_n)|>2\delta.
\tag{16}
\]

Its limiting complement can be made arbitrarily small by sending delta to zero, after n tends to infinity. On this event the two groups of diagonal entries in (14) have gap at least 2delta s. The o_P(s) matrix error consequently makes the collective kernel coordinate approach its first coordinate axis and the combined pair kernel coordinates approach the other p-dimensional coordinate space. This is the elementary spectral projection estimate for a self-adjoint matrix separated into two groups. It makes no choice of basis inside the pair group.

For every retained kernel vector, exact reconstruction from the second Schur step gives

\[
z_{\rm ret}
=U_-\xi+
(xI-Q_-\mathcal T_n(x)Q_-)^{-1}
Q_-\mathcal T_n(x)U_-\xi.
\tag{17}
\]

The second term has norm O_P(sqrt(s)) uniformly on bounded normalized xi. Thus the retained collective and pair spaces approach the corresponding reference spaces in U_-.

For x in the coarse bounded window, reconstruction from the first Schur step is

\[
\mathcal J_x(\alpha,v)=
\left(\alpha u+R_Q(3+sx)AEv/\sqrt8,\ v/\sqrt8\right).
\tag{18}
\]

The host gap gives ||J_x-J_0||=O(s) uniformly there. Also J_0 transpose J_0=I+o_P(1), by the frozen derivative estimate. Normalizing these actual graph eigenvectors therefore preserves the reference subspace convergence. For fixed p, orthonormal bases can be compared through their projection matrices, and the errors remain o_P(1). Sending delta to zero proves the projector assertions.

The physical mass forms of J_0 are exactly the motif contribution ||v|| squared/8, the host constant contribution alpha squared, and a host-complement Gram form tending to 7||v|| squared/8. Applying these to c_- and the antisymmetric pair span proves (10).

## 8. Why the final collective law is different from the raw quadratic

The raw centered quadratic has a compensated lattice-Poisson limit C with infinite mean from rare strong pairs. Its contribution to the collective coefficient is (kappa squared/2)C+63/32. The exact complementary correction contributes

\[
-\frac1\theta\sum_k\frac{t_k^2}{\kappa+t_k}P_k.
\tag{19}
\]

These use the same pair process. Their random large-jump terms cancel, leaving the bounded kernel J(t). The constant becomes 51/32. Consequently the effective collective fluctuation has finite second moment and a smooth density. Replacing the complementary correction by zero would produce the wrong law and miss this regularization.

At the same time antisymmetry removes the leading collective-to-negative-pair interaction. Both facts are needed: the collective shift is random, but the pair subspace does not acquire a nonzero leading mixing angle at this scale.

## 9. Scope

The theorem resolves deterministic finite beta retunings of the negative collision in the cubic H=0 duplication model, including every fixed resonant pair multiplicity and the resulting unconditional mixture. It does not resolve finer splittings inside a repeated pair subspace, a graph-adaptively chosen beta, or conditioning on a shrinking near-coincidence event.

The broader polynomial-port theorem in this round supplies a first-order structural law. Its finer coefficients need not equal those here. In particular its nonseparable residual can survive at physical order s squared. No extension of the constants 33/16 or 51/32 to arbitrary attachments is asserted.

This is a paper theorem. The finite formal packet supports actual attachment algebra and finite Schur components, but the random geometry, probability limits, Fourier argument, spectral projections and analytic transfer are not encoded end to end.

Requested review: verify the nonlinear root count and uniformity, the exact reconstruction of physical graph vectors, the transition from fixed p to the mixture, and the distinction between random ordering and mixing. Check every scale against the exact Schur equation rather than the older normalized-cluster error.
