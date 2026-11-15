# Sharp growth criterion for a simple local resonant channel

November 15, 2026. Owner: root. Revision 1, frozen for independent review.

Status: proposed paper extension of the nonseparable-port theorem. It uses the accepted host estimates and an explicit full-resolvent pair witness. No new general Schur principle is claimed.

Exposure: the author read and reviewed structural/vector-port-v1.md and the earlier sharp cubic and weighted pair proofs. The general lower-bound derivation below was developed separately in this file. Its critical law is supplied by the already frozen structural theorem.

## 1. Model and statement

Use the fixed local data of structural/vector-port-v1.md, SHA256 ff889b703f36bdf1bea9854c20c41b97578abdd92a474fc5e7c6bcc03472cde8. In particular the vector polynomial b(x), internal symmetric matrix C and unit vector v satisfy

\[
K_0=dI-C-\int\frac{b(x)b(x)^\top}{d-x}\,d\nu_d(x)\succeq0,
\qquad \ker K_0=\operatorname{span}(v),
\qquad \beta=b(d)^\top v>0.
\tag{1}
\]

Write

\[
p(x)=b(x)^\top v,\quad
k(z)=\int\frac{p(x)^2}{z-x}\,d\nu_d(x),\quad
D=1-k'(d),\quad \kappa=\beta/\sqrt D.
\tag{2}
\]

The augmented matrix Acal is the same fixed vector-polynomial attachment at m predetermined distinct marks of a uniform simple labelled d-regular host. Let

\[
s=\sqrt{m/n},\qquad \theta=ms=\sqrt{m^3/n}.
\]

The following hold.

1. For every sequence 1<=m=o(n),

\[
\frac{\lambda_{\max}(\mathcal A)-d}{s}
\longrightarrow\kappa\quad\hbox{in probability}
\quad\Longleftrightarrow\quad m^3/n\longrightarrow0.
\tag{3}
\]

In the sufficient regime, the complete top m+1 cluster, divided by s after centering, is within o_P(1) in ordered maximum distance of the star spectrum plus and minus kappa and m-1 zeros.

2. There is a fixed constant A_0>0 depending only on the local data and d such that, for every fixed T>0 and theta_0>0 with liminf theta>=theta_0,

\[
\liminf_n\Pr\left\{
(\lambda_{\max}(\mathcal A)-d)/s>T
\right\}\ge \frac{A_0\theta_0}{T+A_0\theta_0}.
\tag{4}
\]

If theta tends to infinity while m=o(n), the normalized top displacement tends to positive infinity in probability.

3. For m=o(sqrt(n)), put

\[
t=m^2/n,\qquad w_n=\max(s,t).
\]

Then the entire top m+1 cluster has width O_P(w_n) about d, and its complement stays a fixed distance below d with probability tending to one. If n^(1/3)<<m<<sqrt(n), the top displacement is Theta_P(t). Here the latter means tightness after division by t and being bounded away from zero in probability. No deterministic postcritical coefficient is asserted.

Together with the separate critical Poisson law, these give a sharp transition for the whole fixed local class. The general class can be weighted or signed. Its triangle and seven-leaf-star specializations are simple unweighted graphs.

## 2. Subcritical sufficiency

On the same fixed-radius locality event as in the vector-port theorem, the full marked self-energy deviation is

\[
\Delta_n(d)
=(G_E(d)-g_d(d)I_m)\otimes b(d)b(d)^\top
+(J_m/n)\otimes R_d(d),
\tag{5}
\]

with the fixed matrix R_d(d) given there. The locality failure probability is O((m+m squared)/n), hence tends to zero when m cubed/n tends to zero. The accepted log-free host estimate SG-22 gives G_E-g_d I=o_P(s), while J_m/n has norm s squared. Thus Delta_n(d)=o_P(s).

The fixed-derivative SG-22 estimates also give G_v'(d)-g_v'(d)I=o_P(1). The same endpoint inertia argument as the vector-port theorem supplies exactly m+1 top eigenvalues in a fixed interval about d, with a fixed complementary gap. Its physical map satisfies HJ=sVT+W, where W=O(s squared), J transpose W=0 and

\[
T=\begin{pmatrix}0&\kappa e^\top\\
\kappa e&(G_v(d)-g_v(d)I)/(Ds)\end{pmatrix}.
\]

Here ||T||=O_P(1), and its lower block is o_P(1). The Gram matrix is I+o_P(1). The dimension-free leakage and normalization argument therefore gives an actual cluster isometry U with

\[
\|U^\top(\mathcal A-dI)U/s-T\|=o_P(1).
\]

The star has eigenvalues plus and minus kappa and m-1 zeros. Ordered comparison proves the sufficient assertion, including bounded m. No critical relation m proportional to n^(1/3) is used in this paragraph.

## 3. A deterministic pair witness for the full class

Compress the actual motif coordinates to their local unit vector v. By the variational principle the top eigenvalue of Acal is at least that of

\[
\mathcal A_v=
\begin{pmatrix}
A&p(A)E\\
E^\top p(A)&c_v I_m
\end{pmatrix},
\qquad c_v=v^\top Cv=d-k(d).
\tag{6}
\]

This is an isometric compression of the actual graph operator, not a comparison obtained by discarding a possibly positive error.

Let ell_0 be a fixed integer larger than twice the degree of p. Suppose all marked host neighborhoods needed for polynomial diagonal moments are trees. For real z>d put

\[
\rho(z)=\frac{z-\sqrt{z^2-4q}}{2q},\qquad
g(z)=\frac1{z-d\rho(z)},\qquad q=d-1.
\]

The full host Green entries obey

\[
((zI-A)^{-1})_{uu}\ge g(z),\qquad
((zI-A)^{-1})_{uv}\ge g(z)\rho(z)^{\operatorname{dist}(u,v)}.
\tag{7}
\]

For the second inequality fix a lift of a shortest path to the universal d-regular cover. Every walk from its chosen root lift to the chosen endpoint lift projects injectively to a walk from u to v, because lifting from a fixed initial point is unique. Summing the nonnegative resolvent walk series gives (7). The diagonal uses the same chosen root lift. Convergence follows from z>d.

The polynomial quotient

\[
D_z(x)=\frac{p(z)^2-p(x)^2}{z-x}
\]

has fixed degree below ell_0. Polynomial locality makes its diagonal equal to the tree value at a marked root. It has zero off-diagonal between two roots at distance greater than ell_0. Thus, for two marks at distance ell with ell_0<ell<=R, the positive unit pair vector y gives

\[
y^\top\bigl[zI-c_v I-E^\top p(A)(zI-A)^{-1}p(A)E\bigr]y
\le a(z)-p(z)^2g(z)\rho(z)^R,
\tag{8}
\]

where

\[
a(z)=z-c_v-k(z),\qquad a(d)=0,\qquad a'(d)=D.
\]

No sign restriction on the polynomial coefficients is needed: outside its fixed support the off-diagonal coefficient is p(z) squared times the positive host Green entry.

Set

\[
B_0=\frac{\beta^2g(d)}{8D}>0.
\tag{9}
\]

If delta_n tends to zero, R_n=floor(log_q(B_0/delta_n)) tends to infinity, and delta_n R_n tends to zero, then at z=d+delta_n, for all large n,

\[
a(z)\le \tfrac32D\delta_n,\qquad
p(z)^2g(z)\rho(z)^{R_n}\ge2D\delta_n.
\tag{10}
\]

Indeed p(z) squared g(z) tends to beta squared g(d), and
q^R rho(d+delta)^R tends to one whenever delta R tends to zero. Also q^(-R)>=delta/B_0. The factor 8 in (9) leaves the stated fixed margin after taking both continuous factors at least half their limits.

The right side of (8) is then negative. Since zI-A is positive definite, exact Schur inertia for (6) implies

\[
\lambda_{\max}(\mathcal A)\ge\lambda_{\max}(\mathcal A_v)>d+\delta_n.
\tag{11}
\]

This lower witness uses neither a host spectral-gap theorem nor an isotropic resolvent approximation.

## 4. Close-pair probability at the necessary radius

Assume theta is bounded below by a positive constant and m=o(n). Then m tends to infinity and s tends to zero. Fix T>0 and choose delta_n=T s and R_n as in Section 3. Thus R_n tends to infinity,

\[
q^{2R_n}/n=O(1/m)=o(1),
\qquad
q^{R_n}\ge B_0/(q T s).
\tag{12}
\]

The standard breadth-first configuration exposure bounds the probability that the radius-R_n ball at a specified root is not a tree by C_d q^(2R_n)/n. Conditioning on simplicity costs only a fixed factor. Therefore, by Markov's inequality, a fraction 1-o_P(1) of all roots has the full tree ball.

Consider the auxiliary graph on the host vertices whose edges join pairs at distances ell_0+1 through R_n. Its maximum degree is at most

\[
\Delta_R=d\sum_{j=\ell_0}^{R_n-1}q^j,
\]

and on the preceding high-probability event its edge count M_R satisfies

\[
M_R\ge(1-o(1))n\Delta_R/2.
\tag{13}
\]

For the invariant pair-count statistic, predetermined marks have the same law as a uniform independent m-subset sampled after the host. Let X count its induced edges and p_j=(m)_j/(n)_j. Conditional on this host,

\[
\mu=\mathbb E X=p_2M_R,
\qquad
\mathbb E X^2\le\mu+p_3n\Delta_R^2+p_2^2M_R^2.
\tag{14}
\]

The equal-edge terms give mu. Pairs sharing a vertex contribute at most p_3 times n Delta_R squared. Disjoint pairs have inclusion probability p_4<=p_2 squared. On (13), the middle term divided by mu squared is O(1/m). Hence Cauchy-Schwarz gives

\[
\Pr(X>0\mid A)\ge
\frac{\mu}{1+(1+O(1/m))\mu}.
\tag{15}
\]

Since Delta_R is asymptotic to d q^R/(q-1), equations (12)-(14) give

\[
\mu\ge(1-o(1))A_0\theta/T,
\qquad
A_0=\frac{dB_0}{2q(q-1)}.
\tag{16}
\]

Every marked fixed-radius neighborhood is a tree with failure probability O(m/n), which vanishes. This last event is not imposed as a conditioning assumption in (14). Subtract its failure probability after the pair-count estimate. The pair witness (11), (15) and (16) prove (4). When theta tends to infinity, the same bounds give probability tending to one for each fixed T.

If m cubed/n does not tend to zero, take a subsequence with theta bounded below and choose T>kappa. Equation (4) contradicts convergence in probability to kappa. This proves the necessary part of (3).

## 5. Uniform upper width in the dilute range

Suppose m=o(sqrt(n)). The accepted variable-cutoff host estimate, close-pair-transition-round-01/root/cluster-width-v1.md, SHA256 e40164dcf711cca13d945b666645c26aa8095b835e1e727d2d6d7159a78e7b8f, gives

\[
\|G_E(d)-g(d)I\|=O_P(w_n).
\tag{17}
\]

The fixed polynomial locality event has probability tending to one. By (5), the full motif Schur matrix satisfies

\[
F_n(d)=I_m\otimes K_0+O_P(w_n).
\tag{18}
\]

Its derivative is at least the identity and is bounded above in operator norm on a fixed host-gap interval, independently of m. The host-to-motif vector has norm ||b(d)||s<=||b(d)||w_n.

Fix a large deterministic M and work on ||F_n(d)-I tensor K_0||<=M w_n. Take h_n=C_M w_n, where C_M is larger than M+2||b(d)||+2. At d+h_n the full retained Schur matrix is positive definite by F_n(d+h_n)>=I tensor K_0+(C_M-M)w_n I and the host diagonal h_n.

At d-h_n, the local kernel restriction is at most -(C_M-M)w_n. Its local complementary restriction remains uniformly positive, because h_n and w_n tend to zero. Min-max gives exactly m negative eigenvalues of F_n(d-h_n), with negative magnitudes at least (C_M-M)w_n and positive eigenvalues separated from zero. The host diagonal adds one negative direction. The host-star perturbation has norm at most ||b(d)||w_n, too small to change this inertia. Thus the full retained matrix has exactly m+1 negative eigenvalues there.

The eliminated host complement is positive. Exact inertia proves that all top m+1 eigenvalues are inside [d-h_n,d+h_n]. The fixed-endpoint argument gives a fixed gap below the rest of this cluster. Sending M to infinity through the tight error event proves its O_P(w_n) width. The argument does not use the invalid m-row interlacing bound after km vertices have been added.

## 6. Postcritical lower scale

Suppose n^(1/3)<<m<<sqrt(n) and put t=m squared/n. Then t tends to zero and t/s=theta tends to infinity. For a fixed small a>0 take delta_n=a t and R_n=floor(log_q(B_0/(a t))). As before delta_n R_n tends to zero, while

\[
q^{2R_n}/n=O(n/m^4)=o(1).
\]

The same annulus sampling argument gives conditional expected pair count at least (1-o(1))A_0/a. Its second-moment ratio has the same O(1/m) overlap term. Consequently

\[
\liminf_n\Pr\{\lambda_{\max}(\mathcal A)-d>a t\}
\ge \frac{A_0}{a+A_0}.
\tag{19}
\]

Letting a decrease to zero proves that the displacement divided by t is bounded away from zero in probability. Section 5 supplies tightness. This establishes the claimed Theta_P(t) scale.

## 7. Scope and requested review

The result preserves fixed local data, a simple local resonance, nonzero coupling to the host constant mode, and predetermined marks. It is not a uniform assertion over all marked sets in one graph. The lower divergence holds through m=o(n), while the upper width and matching postcritical scale stop at m=o(sqrt(n)).

The spectral gap of the host is used for the subcritical and upper statements, but not for the full-resolvent lower witness. The conclusion concerns adjacency or the specified symmetric weighted operator. It does not assert a normalized-Laplacian gap or mixing law.

Review should check the compressed actual motif matrix in (6), polynomial diagonal and off-diagonal locality, the universal-cover lower kernel, the annulus second moment, all growth ranges, and the top-cluster count in the presence of nonresonant local channels.
