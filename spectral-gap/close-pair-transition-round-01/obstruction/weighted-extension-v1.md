# Fixed-degree weighted close-pair obstruction

November 15, 2026, America/Los_Angeles.

Status at freezing: complete paper extension awaiting independent review. Its elementary sampling argument is the one proved in [the frozen cubic proof](proof-v1.md), SHA256 cadd1408ff45526a328b78f7b2f063fa599278603e90282c216e364c68280a35. No current-round subcritical attempt was read before freezing this extension.

## Statement

Fix d>=3, set q=d-1 and a=d-2, and let n tend through admissible values. Let A be a uniform simple labelled d-regular host. Choose m distinct deterministic marked labels before sampling, with coordinate inclusion E, where m tends to infinity and m=o(n). Put

\[
B=\sqrt a\,AE,\qquad s=\sqrt{m/n},\qquad
\theta=\sqrt{m^3/n},\qquad
\mathcal A_H=\begin{pmatrix}A&B\\B^\top&sH\end{pmatrix}.
\tag{1}
\]

Here H is any real symmetric matrix with norm at most H_0, where H_0>=0 is fixed. The following probability event holds simultaneously for every such H, including graph-dependent H. Define

\[
\beta_d=\frac{d^2(d-2)}{6(d-1)^2}.
\tag{2}
\]

For every fixed K>0 and theta_0>0 with liminf theta>=theta_0,

\[
\liminf_n\mathbb P\left\{
\inf_{\substack{H=H^\top\\\|H\|\le H_0}}
\frac{\lambda_{\max}(\mathcal A_H)-d}{s}>K
\right\}
\ge\frac{\beta_d\theta_0}{K+H_0+\beta_d\theta_0}.
\tag{3}
\]

If theta tends to infinity, the infimum in (3) tends to positive infinity in probability. For d=3, H_0=0, this is exactly the cubic lower bound since beta_3=3/8. For d other than three the attachment is weighted, so this is not an unweighted duplication theorem.

## Deterministic pair lemma

For z>d let

\[
t_d(z)=\frac{z-\sqrt{z^2-4q}}{2q},\qquad
g_d(z)=\frac1{z-dt_d(z)},\qquad
f_d(z)=(d-1)z-a z^2g_d(z).
\tag{4}
\]

The d-regular-tree kernel at distance ell is g_d(z)t_d(z)^ell. The same unique-lift and nonnegative-walk argument as in the cubic proof gives these as lower bounds for full host Green entries at z>d.

For H=0, exact Schur reduction gives

\[
F(z)=(d-1)zI-a z^2E^\top(zI-A)^{-1}E+a E^\top AE.
\tag{5}
\]

If two marks have distance 2<=ell<=r, their normalized positive pair vector y therefore satisfies

\[
y^\top F(z)y\le f_d(z)-a z^2g_d(z)t_d(z)^r.
\tag{6}
\]

The scalar values and derivative at d are

\[
t_d(d)=q^{-1},\qquad
g_d(d)=\frac{q}{d(d-2)},\qquad
f_d(d)=0,\qquad
f_d'(d)=D_d=\frac{2q^2}{(d-2)^2}.
\tag{7}
\]

These follow by differentiating q t_d(z)^2-z t_d(z)+1=0 and substituting in (4). In particular, t_d'(d)=-1/[q(d-2)]. Set

\[
c_d=\frac{d(d-2)^2}{3q},\qquad z_r=d+c_dq^{-r}.
\tag{8}
\]

Then D_d c_d=2dq/3 and a d^2g_d(d)=dq. Since r q^(-r) tends to zero, q^r t_d(z_r)^r tends to one. Consequently the right side of (6), multiplied by q^r, tends to

\[
D_d c_d-dq=-dq/3<0.
\tag{9}
\]

For all sufficiently large r, uniformly over hosts and eligible pairs, the exact Schur Rayleigh witness proves

\[
\lambda_{\max}(\mathcal A_0)>d+c_dq^{-r}.
\tag{10}
\]

## Pair probability and the constants

The maximal number of host vertices at distances two through r from one root is

\[
L_{d,r}=d\sum_{j=1}^{r-1}q^j
=\frac{d(q^r-q)}{d-2}.
\tag{11}
\]

Breadth-first configuration exposure uses O_d(q^r) pairings. At each step the probability of meeting a previously discovered vertex is O_d(q^r/n), provided q^r=o(n). Thus the failure probability is O_d(q^(2r)/n). Conditioning on simplicity costs a bounded constant, because the classical fixed-d simplicity limit is positive. The exact elementary argument in Section 3 of the cubic proof applies with these d-dependent constants.

Fix a threshold T>0 and take

\[
r=\left\lfloor\log_q\frac{c_d}{T s}\right\rfloor.
\tag{12}
\]

Then r tends to infinity, q^(2r)/n=O_d,T(1/m), and q^r>=c_d/(q T s). With probability tending to one, a fraction 1-o(1) of roots has the full distance neighbourhood. The auxiliary graph of distances two through r therefore has edge count at least (1-o(1))n L_(d,r)/2 and maximum degree at most L_(d,r).

Under the equivalent independent random-mark sampling, the number Y of close marked pairs has conditional mean

\[
\mu\ge(1-o(1))\frac{d}{2(d-2)}\frac{m^2q^r}{n}
\ge(1-o(1))\frac{d c_d}{2(d-2)q}\frac{\theta}{T}
=(1-o(1))\frac{\beta_d\theta}{T}.
\tag{13}
\]

The variance argument uses only maximum degree and edge count, so equations (17) through (19) of the cubic proof apply without changing their normalized bound. It follows that

\[
\liminf_n\mathbb P\{Y>0\}
\ge\frac{\beta_d\theta_0}{T+\beta_d\theta_0}.
\tag{14}
\]

The deterministic pair lemma gives lambda_max(A_0)>d+T s on this event. The probability tends to one when theta tends to infinity.

Finally, the difference between A_H and A_0 has operator norm at most s H_0. The variational principle gives simultaneously for all eligible H

\[
\lambda_{\max}(\mathcal A_H)
\ge\lambda_{\max}(\mathcal A_0)-sH_0.
\tag{15}
\]

Take T=K+H_0 in (14) to obtain (3). This proves the uniform supercritical assertion as well. Compactness of the finite-dimensional symmetric norm ball makes the infimum measurable.

## Scope

This extension preserves the predetermined-mark requirement. Uniformity over bounded H follows from one deterministic perturbation inequality on the same pair event. It is not uniformity over marked sets. No spectral-gap theorem, centered-resolvent approximation, spatial localization theorem or critical limiting distribution is used or asserted. The exact constants provide lower bounds and are not claimed optimal.
