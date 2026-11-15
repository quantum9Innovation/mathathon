# One-step disjoint-set repair is a specialization of existing core refinement

Status: NOT an open frontier in the disjoint-set formulation. The argument below is independently reconstructed, with arbitrary degree weights, from the core-refinement machinery in [Lap Chi Lau, *Algorithmic Spectral Graph Theory*, 16 September 2026](https://cs.uwaterloo.ca/~lapchi/papers/ASGT.pdf), Section 7.7, printed pp. 99--104: Lemmas 7.18--7.21 and Algorithm 5. Printed p. 105, Problem 7.24, describes the cut-improvement primitive. The source states the section for regular graphs; retaining the original degree measure gives the weighted formulation below. No new spectral or fractional-response mechanism is needed.

Downloaded 2026-11-15 as `lau2026.pdf`.

SHA256: `cf8207a49678ae493540978fa9158de14427c4dfc605b09dd385bdf83fa92cc0`.

Related older primary work is [Oveis Gharan--Trevisan, *Partitioning into Expanders*, arXiv:1309.3223v3, SODA 2014](https://arxiv.org/abs/1309.3223), Theorem 1.7 and Lemma 1.13. That work treats internal/external expansion and explicitly addresses the failure of naive splitting when external boundary concentrates. It is relevant background, but Lau's later low-space/core overlap argument gives the direct specialization here.

## Precise weighted theorem

Let H be a finite undirected weighted graph with positive degrees d(v). Let 2<=k<=|V|, and suppose H contains k-1 pairwise disjoint nonempty sets A_i with one-sided conductance

\[
 \phi_H(A_i)=\frac{w(A_i,V\setminus A_i)}{\operatorname{vol}_H(A_i)}\le h.
\]

They need not cover V. Write lambda=lambda_k(H), for the normalized Laplacian. There exist k pairwise disjoint nonempty sets B_j such that

\[
 \boxed{\max_j\phi_H(B_j)\le
 \max\{h,4\sqrt{2\lambda}\}+8\sqrt\lambda.}
\]

In particular the bound is C(h+sqrt(lambda)) for an absolute C independent of k. No eigengap or pointwise-leakage assumption is required. The conclusion is disjoint sets; it does not require their union to be V.

## Independently reconstructed proof

All norms and volumes in this proof retain the original degrees of H. Put

\[
 \|f\|_d^2=\sum_v d(v)f(v)^2,\qquad
 \mathcal E_H(f)=\sum_{\{u,v\}}w_{uv}(f(u)-f(v))^2.
\]

If lambda=0, H has at least k connected components of positive volume, which give the conclusion. Assume lambda>0, and set

\[
 \tau=\max\{h,4\sqrt{2\lambda}\}>0.
\]

**1. Core inequality.** For each A_i, select a nonempty subset C_i minimizing global one-sided conductance among nonempty subsets of A_i. It has phi(C_i)<=h. Its minimality implies, for every T subset C_i,

\[
 w(T,V\setminus C_i)\le
 \phi_H(C_i)\operatorname{vol}(T)+w(T,C_i\setminus T)
 \le\tau\operatorname{vol}(T)+w(T,C_i\setminus T).
 \tag{1}
\]

For proper nonempty T, this follows by comparing C_i with C_i\T and rearranging; T=C_i follows from phi(C_i)<=tau. Therefore

\[
 \phi_H(T)\le\tau+2\phi_{C_i}(T),\qquad
 \phi_C(T):=\frac{w(T,C\setminus T)}{\operatorname{vol}_H(T)}.
 \tag{2}
\]

If some nonempty subset of V\(union_i C_i) has global conductance at most tau, add its minimum-conductance subset as a new core. This immediately gives k disjoint sets of conductance at most tau. Otherwise retain exactly p=k-1 cores and put U=union_i C_i. There is now no nonempty subset of V\U with conductance at most tau.

**2. Sparse cuts overlap the cores.** For any T subset V, (1) gives

\[
 \operatorname{cut}(T\setminus U)
 \le\operatorname{cut}(T)+\tau\operatorname{vol}(T\cap U).
 \tag{3}
\]

One way to check the edge accounting is to bound the difference in cuts by

\[
 \sum_i\bigl[w(T\cap C_i,V\setminus C_i)
             -w(T\cap C_i,C_i\setminus T)\bigr]
 \le\tau\operatorname{vol}(T\cap U).
\]

If phi_H(T)<=tau/2 and vol(TcapU)<vol(T)/4, (3) implies phi_H(T\U)<tau, a contradiction. Thus

\[
 \phi_H(T)\le\tau/2\quad\Longrightarrow\quad
 \operatorname{vol}(T\cap U)\ge\operatorname{vol}(T)/4.
 \tag{4}
\]

**3. Every low-energy direction retains mass.** Let F be the k-dimensional space of normalized-Laplacian eigenfunctions for the first k eigenvalues, represented as functions in L2(d). For all f in F,

\[
 \mathcal E_H(f)\le\lambda\|f\|_d^2.
\]

Suppose ||1_U f||_d^2<(1/8)||f||_d^2 for some nonzero f. For threshold sets T_t={v:f(v)^2>=t}, coarea and Cauchy--Schwarz give

\[
 \int\operatorname{cut}(T_t)\,dt
 =\sum_{\{u,v\}}w_{uv}|f(u)^2-f(v)^2|
 \le\sqrt{2\lambda}\|f\|_d^2
 \le(\tau/4)\|f\|_d^2,
\]

\[
 \int\operatorname{vol}(T_t)\,dt=\|f\|_d^2,\qquad
 \int\operatorname{vol}(T_t\cap U)\,dt=\|1_Uf\|_d^2.
\]

Consequently some nonempty T_t satisfies

\[
 \operatorname{cut}(T_t)+2\tau\operatorname{vol}(T_t\cap U)
 <(\tau/2)\operatorname{vol}(T_t).
\]

Both terms on the left are nonnegative, contradicting (4). We have proved

\[
 \|1_Uf\|_d^2\ge\tfrac18\|f\|_d^2\quad(f\in F).
 \tag{5}
\]

The strict inequality in the contradiction and the inclusive conclusion in (5) handle equality at the chosen threshold; no unstated strict spectral gap is used.

**4. A core has a small second local eigenvalue.** Restriction from F to U is injective by (5). On this k-dimensional restricted space,

\[
 \frac{\sum_i\mathcal E_{H[C_i]}(f)}{\|1_Uf\|_d^2}
 \le8\lambda.
\]

The block-diagonal local operator, with block D_{C_i}^{-1/2}L_{H[C_i]}D_{C_i}^{-1/2}, therefore has at least k eigenvalues at most 8lambda. There are only k-1 blocks. Every block has a zero constant eigenvalue, so some block has a second eigenvalue mu<=8lambda. Here the local mass matrix uses original d(v), not internal degrees. Equivalently, fill missing degree with self-loops.

**5. Split only that core.** If mu=0, choose two local connected components. Otherwise a local second eigenfunction has nonzero positive and negative parts. Their supports are disjoint and each part has local Rayleigh quotient at most mu. Ordinary threshold Cheeger rounding produces two disjoint nonempty subsets T_+,T_- of this core with

\[
 \phi_{C_i}(T_\pm)\le\sqrt{2\mu}\le4\sqrt\lambda.
\]

By (2), both have global conductance at most tau+8sqrt(lambda). Retain the other k-2 cores. This gives exactly k disjoint sets and proves the theorem.

The proof uses classical cut improvement and local Cheeger rounding, with the overlap mechanism cited above. Exact minimum-ratio subsets can be obtained by parametric minimum cut for rational weights. No nearly-linear running-time claim is made here.

## Application after one positive edge addition

Suppose G has a k-partition C_1,...,C_k with max_i phi_G(C_i)<=h. Form G' by adding positive conductance t between u and v.

If both endpoints lie in one block, no block boundary increases and that block's degree volume increases; the original k-partition still has maximum conductance at most h.

Otherwise, merge the two endpoint blocks. Their union M has

\[
 \operatorname{cut}_{G'}(M)=\operatorname{cut}_{G}(M)
 \le h[\operatorname{vol}_G(C_a)+\operatorname{vol}_G(C_b)],
\]

\[
 \operatorname{vol}_{G'}(M)=
 \operatorname{vol}_G(C_a)+\operatorname{vol}_G(C_b)+2t.
\]

Thus M has conductance at most h in G'. The untouched blocks also retain that bound. We obtain k-1 disjoint sets covering V in G', and the theorem above supplies k disjoint sets with

\[
 \max_j\phi_{G'}(B_j)\le
 \max\{h,4\sqrt{2\lambda_k(G')}\}+8\sqrt{\lambda_k(G')}.
\]

This answers the aggregate-leakage existence question for disjoint sets. It is a corollary of existing refinement machinery, not evidence of a new partitioning breakthrough. Preserving full coverage, specified balance, bounded label recourse, or nearly-linear update time would require additional theorems. Those stronger formulations should not be called open solely because this argument does not prove them.
