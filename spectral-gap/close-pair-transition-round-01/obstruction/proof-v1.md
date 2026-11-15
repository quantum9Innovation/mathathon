# Close marked pairs force failure of the cubic collective law

November 15, 2026, America/Los_Angeles.

Status at freezing: complete paper proof awaiting independent exact-revision review. Historical priority and end-to-end formalization are separate. No current-round probability attempt was read before freezing this proof.

## 1. Model and theorem

Let n tend to infinity through even integers. Let A be the adjacency matrix of a uniform simple labelled cubic graph on n vertices. Choose a deterministic set of m distinct labels before sampling the graph, and let E contain their coordinate vectors. Define

\[
\mathcal A=\begin{pmatrix}A&AE\\E^\top A&0\end{pmatrix},\qquad
\Lambda_n=\lambda_{\max}(\mathcal A),\qquad
s_n=\sqrt{m/n},\qquad \theta_n=\sqrt{m^3/n}.
\tag{1}
\]

Thus each new vertex duplicates the original neighbours of its corresponding marked vertex. There are no edges between new vertices. Assume throughout that m tends to infinity and m=o(n).

**Theorem.** For every fixed K>0 and every theta_0>0 such that
\(\liminf_n\theta_n\ge\theta_0\),

\[
\liminf_n\mathbb P\left\{\frac{\Lambda_n-3}{s_n}>K\right\}
\ge \frac{3\theta_0}{8K+3\theta_0}.
\tag{2}
\]

In particular, if m/n^(1/3) tends to a in (0,infinity), the right side can be taken as

\[
\frac{3a^{3/2}}{8K+3a^{3/2}}.
\tag{3}
\]

If m/n^(1/3) tends to infinity, then

\[
\frac{\Lambda_n-3}{s_n}\xrightarrow{\mathbb P}+\infty.
\tag{4}
\]

The whole dilute range m=o(n) is allowed in (4). No matching upper bound for Lambda_n or limiting law at criticality is asserted.

The previous cubic star approximation predicts (Lambda_n-3)/s_n tending to kappa_3=3/sqrt(8). Taking any K>kappa_3 in (2) disproves that convergence at the critical mark count. It consequently disproves the entire ordered cluster approximation there. Equation (4) proves a stronger top-eigenvalue failure in the supercritical dilute range. These conclusions concern actual eigenvalues, not merely a failure of a resolvent estimate.

## 2. A deterministic pair obstruction

There is an integer r_0 such that the following holds for every simple cubic host graph, connected or not. If two marked vertices have host distance ell with 2<=ell<=r and r>=r_0, then

\[
\lambda_{\max}(\mathcal A)>3+\frac12\,2^{-r}.
\tag{5}
\]

No assumption on the other marked vertices is needed.

### 2.1 Universal-cover lower bounds

For z>3, put R(z)=(zI-A)^(-1). Its convergent walk expansion has nonnegative terms. The rooted universal cover of each cubic component is the cubic tree. Every host walk starting at a has a unique lift starting at a chosen lift of a. Select a lift of b reached by lifting a shortest a-to-b path of length ell. All tree walks to that lift project to distinct host walks from a to b.

Let

\[
t(z)=\frac{z-\sqrt{z^2-8}}4,\qquad
g(z)=\frac1{z-3t(z)}.
\tag{6}
\]

The cubic-tree Green kernel at distance ell is g(z)t(z)^ell. This follows either from its walk expansion or by solving the radial resolvent equation. Consequently, for any two vertices a,b at distance ell,

\[
R_{aa}(z)\ge g(z),\qquad R_{bb}(z)\ge g(z),\qquad
R_{ab}(z)\ge g(z)t(z)^\ell.
\tag{7}
\]

The graph need not be tree-like near either mark. Positivity of the full resolvent above the host spectral radius is essential here. No corresponding entrywise assertion about a Perron-centered resolvent is being made.

### 2.2 Exact Schur witness

Write B=AE and

\[
F(z)=zI_m-B^\top R(z)B
=2zI_m-z^2E^\top R(z)E+E^\top AE.
\tag{8}
\]

The identity uses A R(z) A=z^2R(z)-zI-A. Take the unit marked-coordinate vector y having entries 1/sqrt(2) at the two selected marks and zero elsewhere. Their host distance is at least two, so the relevant diagonal and cross entries of E^top A E vanish. Equations (7) and (8) give

\[
y^\top F(z)y
\le f(z)-z^2g(z)t(z)^\ell
\le f(z)-z^2g(z)t(z)^r,
\quad f(z)=2z-z^2g(z),
\tag{9}
\]

where 0<t(z)<1.

At z=3 the scalar quantities satisfy

\[
t(3)=\frac12,\quad t'(3)=-\frac12,\quad
g(3)=\frac23,\quad g'(3)=-\frac{10}9,\quad
f(3)=0,\quad f'(3)=8.
\tag{10}
\]

Set z_r=3+2^(-r)/2. Taylor expansion at 3, together with r 2^(-r) tending to zero, gives

\[
2^r f(z_r)\longrightarrow4,\qquad
2^r t(z_r)^r\longrightarrow1,\qquad
z_r^2g(z_r)\longrightarrow6.
\tag{11}
\]

For the middle assertion, r log(2t(z_r)) tends to zero, since log(2t(z)) is differentiable at 3 and vanishes there. Thus the right side of (9), multiplied by 2^r, tends to -2. It is negative for every sufficiently large r, uniformly over host graphs and eligible pairs.

Finally put h=R(z_r)B y. Direct block multiplication yields

\[
\left\langle(h,y),(z_rI-\mathcal A)(h,y)\right\rangle
=y^\top F(z_r)y<0.
\tag{12}
\]

The vector (h,y) is nonzero. The variational principle proves (5). Equivalently, this is the negative direction of the Schur complement when z_rI-A is positive definite.

## 3. The host has nearly maximal distance neighbourhoods

For an integer r>=2 define

\[
L_r=3(2^r-2).
\tag{13}
\]

Every vertex of every simple cubic graph has at most L_r other vertices at distances between two and r. A collision-free breadth-first exploration to depth r has exactly L_r such vertices.

We use the configuration model with three distinguished half-edges at each labelled vertex. Its probability of simplicity, denoted alpha_n, tends to exp(-2)>0. Conditioning on simplicity gives the uniform simple labelled cubic law, since every simple graph has the same (3!)^n number of pairing representations. The positive simplicity limit is the only external random-graph theorem used in this proof. Its source and the previously inspected exact formula are recorded in [sources-v1.md](sources-v1.md).

For completeness, the neighbourhood estimate follows by elementary exposure. Before the first collision, breadth-first exploration to depth r uses at most T_r=3(2^r-1) fresh pairings and discovers at most T_r+1 vertices. At a fresh pairing, at most 3(T_r+1) half-edges belong to already discovered vertices. The available partner count is at least 3n-2T_r-1. When T_r<=n/2 and n is sufficiently large, this denominator is at least n. A union bound therefore bounds the collision probability by

\[
\frac{T_r\,3(T_r+1)}n\le\frac{27\,4^r}n.
\tag{14}
\]

Exploration of half-edges from the depth-r boundary is unnecessary. The collision-free event already gives all the required metric spheres. Edges between boundary vertices do not change their distances from the root.

After conditioning on simplicity, the probability that a specified root fails to have L_r vertices at distances two through r is at most 27 4^r/(alpha_n n). Hence, if 4^r/n tends to zero, the fraction of failing roots tends to zero in probability by Markov's inequality.

## 4. Sampling marks and counting close pairs

The distribution of the uniform labelled host is invariant under all label permutations. Therefore a permutation-invariant statement about the augmented spectrum and host distances for a fixed set of m marked labels has exactly the same probability if the marks are instead a uniformly random m-subset, independently of the host. This equality concerns the joint event and does not permit adaptive mark selection. We use this alternative sampling order only inside the proof.

Fix a host graph. Form a simple auxiliary graph J_r on its n vertices by joining a and b precisely when 2<=dist(a,b)<=r. Its maximum degree is at most L_r. If at least (1-epsilon)n roots have maximal distance neighbourhoods, then its edge count q_r obeys

\[
\frac{(1-\varepsilon)nL_r}{2}\le q_r\le\frac{nL_r}{2}.
\tag{15}
\]

Let Y count edges of J_r whose two endpoints belong to the random m-subset. Write p_k=(m)_k/(n)_k, where the falling factorial is used. Then

\[
\mu:=\mathbb E(Y\mid A)=q_r p_2.
\tag{16}
\]

Pairs of disjoint auxiliary edges have nonpositive covariance, because p_4<=p_2^2. For m>=4 this follows by conditioning on inclusion of the first two endpoints: each subsequent inclusion probability is smaller than the corresponding probability before those endpoints were included. For m<4 it follows immediately from p_4=0. Two edges sharing one vertex have covariance at most p_3. There are at most n L_r^2/2 unordered pairs of edges sharing a vertex. Thus

\[
\operatorname{Var}(Y\mid A)\le\mu+nL_r^2p_3.
\tag{17}
\]

On the event in (15),

\[
\frac{\operatorname{Var}(Y\mid A)}{\mu^2}
\le\frac1\mu+\frac4{(1-\varepsilon)^2}\frac{p_3}{n p_2^2}
=\frac1\mu+\frac4{(1-\varepsilon)^2}
\frac{(m-2)(n-1)}{(n-2)m(m-1)}
\le\frac1\mu+\frac8{(1-\varepsilon)^2m}
\tag{18}
\]

for sufficiently large n. The second-moment inequality now gives

\[
\mathbb P(Y>0\mid A)
\ge
\left(1+\frac1\mu+\frac8{(1-\varepsilon)^2m}\right)^{-1}.
\tag{19}
\]

No independence of auxiliary edges is assumed.

## 5. Choice of radius and conclusion

Fix K>0 and set

\[
r_n=\left\lfloor\log_2\frac1{2K s_n}\right\rfloor.
\tag{20}
\]

Since m=o(n), r_n tends to infinity. Its defining bounds give

\[
\frac1{4K s_n}\le2^{r_n}\le\frac1{2K s_n},\qquad
\frac{4^{r_n}}n\le\frac1{4K^2m}\longrightarrow0.
\tag{21}
\]

The exploration assumption T_(r_n)<=n/2 holds for large n. Choose a deterministic epsilon_n tending to zero such that with probability tending to one at least (1-epsilon_n)n roots have maximal neighbourhoods. For example, a constant multiple of m^(-1/2) suffices by (14) and the positive lower bound on alpha_n.

On this host event, (13), (15), (16) and m tending to infinity imply the uniform lower bound

\[
\mu\ge(1-o(1))\frac{3m^2 2^{r_n}}{2n}
\ge(1-o(1))\frac{3\theta_n}{8K}.
\tag{22}
\]

If Y>0, an eligible pair exists. Equations (5) and (21) then give the strict inequality

\[
\Lambda_n>3+\frac12\,2^{-r_n}\ge3+K s_n.
\tag{23}
\]

Combine (19), (22) and (23), then remove the host conditioning. If liminf theta_n>=theta_0>0, monotonicity and continuity of x/(1+x) give exactly (2). If theta_n tends to infinity, the conditional lower bound in (19) tends to one. Since K was arbitrary, this proves (4).

At criticality, (3) follows from theta_n tending to a^(3/2). The explicit constants are convenient lower bounds and are not claimed optimal.

## 6. Dependencies, exposure and limitations

The precise model and previous star prediction were supplied in the frozen problem packet and the accepted previous-round graph theorem. This proof does not use the current-round subcritical argument, a random-regular spectral gap theorem, the previous marked-resolvent estimate or its logarithmic growth restriction. It uses positivity above the full host spectrum, the universal cover, a finite-dimensional Schur witness, elementary sampling moments, and the classical positive simplicity probability.

The deterministic witness proves the existence of an eigenvalue above the tested location. It does not prove that its eigenvector is localized near the chosen pair or that a pair accounts for the full top eigenvalue. The probability lower bound is not a Poisson limit and does not describe the complete critical distribution. The critical radius has a floor, which is retained through explicit inequalities rather than replaced by a limiting constant.

Only one fixed predetermined mark set is asserted for each n. There is no simultaneous event over all mark sets. The randomness of the auxiliary mark sample is a label-symmetry proof device. No claim about an adjacency spectral gap, normalized Laplacian gap, mixing time or algorithmic performance follows directly.
