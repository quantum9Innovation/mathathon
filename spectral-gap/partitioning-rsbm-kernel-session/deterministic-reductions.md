# Deterministic reductions and a bounded-support estimate

These are reductions and partial results, **not** a proof of full bulk-eigenvalue simplicity. The identity that the planted assignment is an adjacency eigenvector is elementary and already central to the RSBM literature; it is not claimed as new here.

Put `m=2N`, `d=d1+d2`, and `delta=d1-d2>0`. All asymptotics below are along admissible block sizes. The graph is simple, with two independent uniform simple `d1`-regular internal graphs and an independent uniform simple `d2`-regular bipartite cross graph.

## 1. The exact unresolved matrix

Write

\[
A=\begin{pmatrix}C&B\\B^T&D\end{pmatrix},\qquad
\sigma=(\mathbf1_N,-\mathbf1_N)^T.
\]

Both `span{1,sigma}` and its orthogonal complement

\[
W=\{(x,y):\mathbf1^Tx=\mathbf1^Ty=0\}
\]

are invariant under `A`. The restriction of `A` to the first space has eigenvalues `d` and `delta`. Consequently

\[
\dim\ker(A-\delta I)=1
\quad\Longleftrightarrow\quad
(A-\delta I)|_W\text{ is invertible}.
\]

In particular, if

\[
p_A(t)=(t-d)(t-\delta)q_A(t),
\]

then the target is exactly `q_A(delta) != 0`. This is a prescribed-point nonsingularity problem for the random operator on `W`, not a statement that the planted eigenvalue is outside the bulk.

Let `S=diag(sigma)`, let `L_in` be the Laplacian of the union of the two internal graphs, and let `L_cross` be the Laplacian of the cross graph. Direct multiplication gives

\[
S(\delta I-A)S=L_{\rm in}-L_{\rm cross}=:L_w.
\]

This is the ordinary weighted Laplacian with edge weight `+1` on internal edges and `-1` on cross edges. It has row sum zero. The target is equivalent to

\[
\operatorname{rank} L_w=m-1.
\]

The weighted matrix-tree identity therefore gives a second exact equivalent statement:

\[
\tau_w:=\sum_{T\text{ spanning tree}}(-1)^{|T\cap E_{\rm cross}|}\ne0.
\]

Indeed, every principal `(m-1)`-cofactor of `L_w` equals `tau_w`. If its rank is `m-1`, its adjugate is a nonzero scalar multiple of `11^T`; if its rank is smaller all such cofactors vanish. The alternating signs prevent the usual positivity argument for a connected graph. Connectivity alone does not imply the required rank.

## 2. The hard `(d1,d2)=(2,1)` case

For every `d2=1`, relabeling the second block by the cross perfect matching makes `B=I`. Because the internal graph law is invariant under relabeling and independent of the matching, `C,D` remain independent uniform simple `d1`-regular adjacency matrices. The equation

\[
\begin{pmatrix}C-\delta I&I\\I&D-\delta I\end{pmatrix}
\binom{x}{y}=0
\]

is equivalent to

\[
y=(\delta I-C)x,\qquad
\big((\delta I-D)(\delta I-C)-I\big)x=0.
\]

This correspondence is a linear isomorphism of the kernels. Thus, for `(2,1)`, where `delta=1`, the full problem is precisely

\[
\ker(DC-C-D)=\operatorname{span}\{\mathbf1_N\}.
\]

The product matrix is generally nonsymmetric; no unjustified simultaneous diagonalization of `C,D` is available. Both its row and column sums are zero, so its kernel splits as the constants plus the kernel of its restriction to `1^perp`.

## 3. Exact recovery needs no analytic gap once simplicity holds

Given `A` and the integers `d1,d2`, compute a rational nullspace of the integer matrix `M=A-delta I` by exact elimination. If its dimension is one, any nonzero vector `v` in that nullspace is `c sigma`, with `c != 0`. Dividing by `v_1` gives a vector with entries exactly `+1` and `-1`, equal to the planted assignment up to its unavoidable global sign.

This is polynomial-time in the bit model. For fixed degrees, every minor of `M` has absolute value at most `(d+delta^2)^(m/2)` by Hadamard's bound. Standard fraction-free elimination therefore uses integers with polynomially many bits and polynomially many arithmetic operations. There is no need to know an outlier gap or approximate a bulk eigenvector numerically.

A one-sided finite-field certificate is also possible: if an odd-prime reduction of `M` has rank `m-1`, then its rational rank is `m-1`, and a normalized modular kernel vector is exactly the reduction of `sigma` up to sign. Choose an odd prime not dividing `d2`: odd primes dividing `d2` give the independent modular kernel vectors `1` and `sigma`, while modulo 2 the two signs cannot be distinguished. No high-probability claim about a fixed prime follows from this certificate.

## 4. Rigorous partial result: small-support obstructions are polynomially rare

**Proposition.** Fix `d1>d2>0`. There exists a constant `epsilon=epsilon(d1,d2)>0` such that, with `d=d1+d2` and `delta=d1-d2`,

\[
\mathbb P\big[\exists\,0\ne x:\ Ax=\delta x,
\ |\operatorname{supp}x|\le \epsilon N\big]
=O_{d_1,d_2}\big(N^{-(d-2)(\delta+1)}\big).
\]

No such eigenvector has support below `2(delta+1)`. In particular, for `(2,1)`, with probability `1-O(N^-2)` every eigenvector of eigenvalue 1 has support larger than `epsilon N`.

**Proof.** Since \(A\mathbf1=d\mathbf1\) and `delta != d`, every such real eigenvector has coordinate sum zero, and hence has both positive and negative entries. At a vertex whose positive coordinate is maximal, the eigenvector equation implies that it has at least `delta` positive neighbors: if there were `r<delta` positive neighbors, the neighbor sum would be at most `r` times that maximal coordinate. Applying the same argument to `-x`, its support size `s` obeys

\[
s\ge 2(\delta+1).
\]

Let `S` be the support, let `T=N(S)\setminus S`, and let `F` consist of all edges with at least one endpoint in `S`. Every vertex of `T` has at least two neighbors in `S`, because the eigenvector equation at that zero coordinate is a sum of nonzero support coordinates that must vanish. Write `e` for the number of edges inside `S` and `b` for the number from `S` to `T`. Then

\[
ds=2e+b,\quad |T|\le b/2,\quad
|E(F)|-|V(F)|=e+b-s-|T|
\ge (d-2)s/2.
\]

For fixed `s`, a direct fixed-pattern subgraph count already gives probability `O(N^{-(d-2)s/2})`. The following exposure argument gives a uniform bound up to a small fixed fraction of `N`.

Use independent internal configuration pairings and the bipartite configuration matching. Fix a labeled set `S` of size `s`. Expose the partners of its `ds` stubs, always skipping stubs already paired in an earlier exposure. Call an exposure a collision if its partner lies in `S` or at an exterior vertex previously touched in this exposure process. For `s <= epsilon N`, each conditional collision probability is at most `C s/N`, where `C` depends only on the degrees: at most `d s+d^2 s` target stubs belong to these vertices, while each relevant remaining pairing pool has at least a constant times `N` stubs if `epsilon` is sufficiently small.

There are `e+b` exposures and exactly `|T|` first touches of an exterior vertex. Therefore the number of collisions is

\[
e+b-|T|\ge e+b/2=ds/2.
\]

Pad the exploration with noncollisions to `ds` steps if needed. A union bound over subsets of `ceil(ds/2)` step indices, using the conditional probability bound at each selected step, shows

\[
\mathbb P[\text{every exterior neighbor of }S
\text{ is touched at least twice}]
\le 2^{ds}(Cs/N)^{ds/2}.
\]

Taking a union bound over the at most `(2 e N/s)^s` choices of `S`, and putting `a=(d-2)/2>0`, gives

\[
\mathbb P[\exists\text{ such }S,\ |S|=s]
\le [K(s/N)^a]^s
\]

for a degree-dependent constant `K`. Shrink `epsilon` so that `K e^a (2 epsilon)^a<1/2`. The ratio between the bound at `s+1` and at `s` is at most

\[
K e^a((s+1)/N)^a\le 1/2
\]

throughout this range for all sufficiently large `N`. Summing from `r=2(delta+1)` to `floor(epsilon N)` is thus `O(N^{-ar})`, as claimed. Finally, conditioning all three fixed-degree factors on simplicity costs only a degree-dependent constant, using the standard positive limiting probability of simplicity, including its bipartite version; see [Janson, *The probability that a random multigraph is simple, II*](https://arxiv.org/abs/1307.6344). QED.

This is a standard unique-neighbor/exposure argument specialized to this eigenvalue. It rules out finite gadgets and, more generally, support on a sufficiently small fixed fraction of vertices as a nonvanishing-probability obstruction. It does **not** exclude an additional eigenvector supported on a positive fraction of vertices, and does not prove identifiability or the desired one-dimensional kernel.
