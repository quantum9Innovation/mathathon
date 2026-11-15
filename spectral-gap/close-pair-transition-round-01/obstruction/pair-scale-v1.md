# Lower bound at the pair-interaction scale

November 15, 2026, America/Los_Angeles.

Status at freezing: complete paper corollary awaiting independent review. This note uses the deterministic pair and sampling arguments from [proof-v1.md](proof-v1.md) and [weighted-extension-v1.md](weighted-extension-v1.md). It does not use a current-round subcritical proof or an upper estimate.

## Statement

Use the fixed-d weighted model B=sqrt(d-2)AE, initially with H=0. Marks are deterministic before sampling the uniform simple labelled d-regular host. Assume

\[
\frac{m}{n^{1/4}}\longrightarrow\infty,\qquad
\frac{m}{\sqrt n}\longrightarrow0.
\tag{1}
\]

Define

\[
a_n=\frac{m^2}{n},\qquad
\beta_d=\frac{d^2(d-2)}{6(d-1)^2},\qquad
X_n=\frac{\lambda_{\max}(\mathcal A_0)-d}{a_n}.
\tag{2}
\]

For every fixed K>0,

\[
\liminf_n\mathbb P\{X_n>K\}\ge\frac{\beta_d}{K+\beta_d},
\qquad
\limsup_n\mathbb P\{X_n\le K\}\le\frac{K}{K+\beta_d}.
\tag{3}
\]

In particular X_n is bounded away from zero in probability in the following precise sense: for every epsilon>0 there exists c>0 such that limsup P(X_n<=c)<epsilon. No upper tightness or matching asymptotic follows from this note alone.

In the smaller range

\[
n^{1/3}\ll m\ll\sqrt n,
\tag{4}
\]

the same bounds hold with X_n replaced by

\[
\inf_{\substack{H=H^\top\\\|H\|\le H_0}}
\frac{\lambda_{\max}(\mathcal A_H)-d}{a_n}
\tag{5}
\]

for every fixed H_0. Here the defect block is s_n H with s_n=sqrt(m/n). For d=3 and H=0, (3) reads liminf P(X_n>K)>=3/(8K+3).

## Proof

Write q=d-1 and c_d=d(d-2)^2/[3(d-1)], as in the weighted pair lemma. For a fixed K>0 take

\[
r_n=\left\lfloor\log_q\frac{c_d}{K a_n}\right\rfloor.
\tag{6}
\]

The upper restriction in (1) gives a_n tending to zero and r_n tending to infinity. The lower restriction gives

\[
\frac{q^{2r_n}}n=O_{d,K}\left(\frac{n}{m^4}\right)\longrightarrow0.
\tag{7}
\]

Thus with probability tending to one almost all roots have the maximal distance neighbourhood through radius r_n. The auxiliary graph joins distances two through r_n and has asymptotically at least d n q^(r_n)/[2(d-2)] edges. Under equivalent uniform random-mark sampling its induced edge count Y has conditional mean

\[
\mu\ge(1-o(1))\frac{d}{2(d-2)}\frac{m^2q^{r_n}}n
\ge(1-o(1))\frac{d c_d}{2(d-2)qK}
=(1-o(1))\frac{\beta_d}{K}.
\tag{8}
\]

Its conditional variance divided by mu^2 is at most 1/mu+O(1/m), by the same sampling calculation as in the cubic proof. The second-moment inequality gives

\[
\liminf_n\mathbb P\{Y>0\}\ge\frac{\beta_d}{K+\beta_d}.
\tag{9}
\]

On this event, the deterministic pair lemma yields

\[
\lambda_{\max}(\mathcal A_0)>d+c_d q^{-r_n}\ge d+K a_n.
\tag{10}
\]

This proves (3). Taking complements proves its second inequality, and then letting the fixed K decrease proves the stated bound away from zero.

For the uniform-H extension, the exact norm comparison gives

\[
\inf_{\|H\|\le H_0}\frac{\lambda_{\max}(\mathcal A_H)-d}{a_n}
\ge X_n-\frac{H_0 s_n}{a_n}
=X_n-\frac{H_0}{\sqrt{m^3/n}}.
\tag{11}
\]

The final term tends to zero under (4). Given any eta>0, apply (3) at K+eta, use (11) for all sufficiently large n, then let eta decrease to zero. Continuity of beta_d/(K+beta_d) gives exactly the bounds claimed for (5).

## Limits

The lower estimate applies below the collective transition as well, where m^2/n may be smaller than sqrt(m/n). It does not by itself identify the dominant scale there. In the supercritical range (4), a_n/s_n tends to infinity. A separate upper bound of order a_n is needed to identify a matching scale. This note supplies no localization law, limiting distribution or optimal constants.
