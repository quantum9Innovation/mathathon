# Polynomial Boolean recovery for the uniform-simple RSBM(2,1)

Prepared 2026-11-15. This is a derived proof, independently audited in this
session. Historical priority is not asserted. It proves recovery, **not**
one-dimensionality of the real eigenspace at eigenvalue 1.

## Result

Let each planted block have size `N`. Independently sample a uniform simple
2-regular graph in each block and a uniform perfect matching between the
blocks. Let `A` be the resulting adjacency matrix, on `n=2N` vertices.

**Theorem.** There is a deterministic algorithm, with running time bounded
by a fixed polynomial in `n`, which recovers the planted partition up to
global exchange with probability `1-O(N^-2)`, along every admissible size.
There is also an algorithm of expected polynomial running time that lists
all equitable `(2,1)` partitions on every input from the model.

The new ingredient needed beyond the existing Boolean rigidity proof is
only

\[
 \mathbb E\,2^{\dim_{\mathbb F_2}\ker(A-I)}=O(N^{24}).       \tag{1}
\]

Consequently the real eigenspace at 1 has dimension `O(log N)` with high
probability. Enumerating the sign choices on a set of pivot coordinates
then suffices; real corank one is unnecessary for recovery.

Two equivalent algorithms are given below. The binary affine version uses
only arithmetic over `F_2`; the direct spectral version uses rational
linear algebra. Neither algorithm knows the planted matching or signs.

## 1. Configuration model and an exact first moment

First use two independent degree-two configuration models: every vertex
has two distinguished stubs, and a uniform perfect pairing of the `2N`
stubs determines the internal multigraph. A loop contributes twice to
the adjacency diagonal. The cross matching can be gauged to identity by
relabeling the second block. Independence and relabeling invariance imply
that the two internal matrices `C_+,C_-` remain independent configuration
matrices. Thus

\[
 A=\begin{pmatrix}C_+&I\\I&C_-\end{pmatrix}.
\]

Conjugating `A-I` by `diag(I,-I)` gives

\[
 M=\begin{pmatrix}C_+-I&-I\\-I&C_--I\end{pmatrix}.
\]

All the following counting is over a fixed field `F_p`; we ultimately take
`p=2`. A kernel vector `(x,z)` satisfies

\[
 C_+x=x+z,\qquad C_-z=x+z.                              \tag{2}
\]

At coordinate `i`, write `a=x_i`, `d=z_i`. Let `b,c` be the `x` labels at
the partners of its two distinguished plus stubs, and `e,f` the `z` labels
at the partners of its minus stubs. Equation (2) is exactly

\[
 b+c=a+d=e+f.
\]

An ordered local profile is therefore determined by
`(a,d,b,e) in F_p^4`, with `c=a+d-b` and `f=a+d-e`. Let
`n_{a,d,b,e}` count the vertices of each profile. Define the stub tables

\[
\begin{split}
 m^+_{uv}&=\sum_{a,d,b,e}n_{a,d,b,e}\,1_{a=u}
                   (1_{b=v}+1_{a+d-b=v}),\\
 m^-_{uv}&=\sum_{a,d,b,e}n_{a,d,b,e}\,1_{d=u}
                   (1_{e=v}+1_{a+d-e=v}).
\end{split}
\]

The indicators here take integer values; the tables are ordinary
nonnegative integer tables. Pairing is possible precisely when each
table is symmetric and has even diagonal entries. Put

\[
 W(m)=\prod_{u<v}m_{uv}!\prod_u(m_{uu}-1)!!,
 \qquad (-1)!!=1.
\]

For a fixed assignment of profiles to the `N` labeled coordinates, the
number of compatible plus pairings is `W(m^+)`: pair each off-diagonal
stub class bijectively with its reverse class, and pair every diagonal
class internally. The minus count is independent and identical in form.
Every pairing and kernel vector determine exactly one profile assignment,
since the stubs are distinguished. Hence

\[
 \mathbb E|\ker M|
 =\sum_{\substack{n:\sum n=N\\m^+,m^-\text{ valid}}}
       \frac{N!}{\prod n_{a,d,b,e}!}
       \frac{W(m^+)W(m^-)}{((2N-1)!!)^2}.                \tag{3}
\]

This includes loops and parallel edges correctly. It is the exact formula
already derived in
`../partitioning-rsbm-obstruction-session/finite-field-21-entropy.txt`.
The argument below needs only its nonpositive entropy exponent, not its
equality cases or any local central limit theorem.

## 2. Nonpositive entropy by two symmetrizations

For one type, set `T=n/N`, `Q^+=m^+/(2N)`, `Q^-=m^-/(2N)` and let `H`
be Shannon entropy with natural logarithms and `0 log 0=0`. Regard `T`
as the law of `(a,d,b,e)` and define `c=a+d-b`, `f=a+d-e`.

Consider the commuting bijections

\[
 s(a,d,b,e)=(a,d,a+d-b,e),\qquad
 t(a,d,b,e)=(a,d,b,a+d-e).
\]

They interchange `b,c` and `e,f`. Each leaves both stub tables `Q^+,Q^-`
unchanged. Let `\bar T` be the average of the four laws `T,sT,tT,stT`.
Concavity and invariance of entropy under bijections give
`H(T)<=H(\bar T)`. Under `\bar T`, the labels at each pair of stubs are
exchangeable, so

\[
 Q^+=\operatorname{law}_{\bar T}(a,b),\qquad
 Q^-=\operatorname{law}_{\bar T}(d,e).
\]

Subadditivity of entropy for the two pairs `(a,b)` and `(d,e)` now gives

\[
\begin{split}
 \Phi(T)&:=H(T)-H(Q^+)-H(Q^-)\\
 &\le H(\bar T)-H_{\bar T}(a,b)-H_{\bar T}(d,e)\\
 &=-I_{\bar T}((a,b);(d,e))\le0.                        \tag{4}
\end{split}
\]

This proof is valid in characteristic two. It does not need the tables'
pairing constraints, an equality classification, or odd characteristic.

## 3. Explicit polynomial bound

The elementary bounds, for every integer `r>=0`, are

\[
 r\log r-r\le\log r!\le r\log r-r+1+\log(r+1).
\]

For even `r>=0`, applying these to `r!/(2^{r/2}(r/2)!)` gives

\[
 \log(r-1)!!\le\tfrac r2\log r-\tfrac r2+1+\log(r+1).
\]

Both use the zero conventions above. With `q=p(p+1)/2`, symmetry of a
valid table `m`, and `\sum_{u,v}m_{uv}=2N`, it follows that

\[
 \log W(m)\le N\log(2N)-N-NH(Q)
                    +q[1+\log(2N+1)].
\]

The denominator has the lower bound

\[
 \log(2N-1)!!\ge N\log(2N)-N-1-\log(N+1).
\]

Thus

\[
 \frac{W(m)}{(2N-1)!!}
 \le e^{q+1}(2N+1)^{q+1}e^{-NH(Q)}.                    \tag{5}
\]

The multinomial bound is
`N!/\prod n! <= exp(NH(T))`. Combining (4) and (5), every summand of
(3) is at most `e^{2(q+1)}(2N+1)^{2(q+1)}`. There are at most
`(N+1)^{p^4}` types. Consequently, for every fixed prime `p`,

\[
 \boxed{\mathbb E|\ker_{\mathbb F_p}M|
 \le e^{p(p+1)+2}(2N+1)^{p(p+1)+2}(N+1)^{p^4}.}       \tag{6}
\]

In particular, with `p=2`,

\[
 \mathbb E\,2^{\dim_{\mathbb F_2}\ker(A-I)}
 \le e^8(2N+1)^8(N+1)^{16}=O(N^{24}).                  \tag{7}
\]

No estimate uniform in growing `p` is asserted or needed.

## 4. Transfer to exactly uniform simple 2-regular blocks

Every labeled simple 2-regular graph has exactly `2^N` realizations by
the distinguished-stub pairing model. Conditioning on simplicity
therefore yields exactly the uniform simple model, not a weighted
permutation model. In one block the simplicity probability tends to
`e^{-3/4}`; for two independent blocks it tends to `e^{-3/2}>0`.

For completeness, the one-block probability is the ratio

\[
 \frac{[z^N](1-z)^{-1/2}e^{-z/2-z^2/4}}
      {[z^N](1-z)^{-1/2}}\longrightarrow e^{-3/4}.
\]

Since the kernel size is nonnegative, its conditional expectation is at
most its unconditional expectation divided by this positive probability.
This proves (1) in the requested model. In particular this transfer
avoids the noncontiguity between uniform simple 2-factors and
`P+P^T` for a uniform permutation `P`.

## 5. Binary affine recovery algorithm

For a sign assignment `sigma_i=(-1)^{z_i}`, the parity of the number of
opposite-sign neighbors at vertex `i` is

\[
 \sum_{j\sim i}(z_i+z_j)=((A+I)z)_i\quad\text{in }\mathbb F_2,
\]

because the degree is three. Every equitable `(2,1)` assignment therefore
satisfies

\[
 (A+I)z=\mathbf1 \quad\text{over }\mathbb F_2.          \tag{8}
\]

The parity equation alone permits either one or three opposite neighbors,
so candidates must be checked over the integers.

The algorithm, given only the cubic graph, is:

1. Solve (8) by binary Gaussian elimination; let `z_0+ker(A+I)` be its
   affine solution set and `k=dim ker(A+I)`.
2. For the bounded-time version, return failure if `2^k>n^{27}`.
3. Enumerate all `2^k` affine solutions in Gray-code order, adding one
   kernel basis vector at each step. For each, check that every vertex
   has exactly one opposite-sign neighbor. Return the first passing
   assignment, with a fixed global orientation if desired.

The planted assignment guarantees consistency. In fact (8) is consistent
for every simple cubic graph: `L=A+I` is symmetric over `F_2` with diagonal
all ones, so for `u in ker L`, `0=u^TLu=1^Tu`; hence
`1 in (ker L)^perp=image L`.

By (1) and Markov's inequality, the cutoff fails with probability
`O(N^-3)`. A candidate can be checked in `O(n)` operations. The algorithm
therefore has worst-case running time `O(n^28)` (a deliberately loose
polynomial), including elimination. Without the cutoff, enumeration has
expected running time `O(n^25)` and lists all equitable partitions if
desired. Success means recovery up to global sign.

The existing Boolean rigidity lemma states that the only passing
assignments are the planted assignment and its negative with probability
`1-O(N^-2)`; see
`../partitioning-rsbm-kernel-session/low-degree-identifiability.md`, or the
independent calculation in
`../partitioning-rsbm-obstruction-session/combinatorics-21.txt`.
Every passing assignment is balanced automatically: for `A sigma=sigma`,
symmetry and `A1=3 1` imply `3<1,sigma>=<1,sigma>`, hence `sum sigma=0`.
Combining rigidity with the cutoff bound proves the stated theorem.

## 6. Direct exact spectral recovery, if preferred

Let `r=dim_Q ker(A-I)` and `k=dim_F2 ker(A-I)`. Reduction of integer
minors gives `r<=k`; thus `E 2^r<=E 2^k=O(N^24)`.

Compute a rational basis `U` for the real eigenspace at 1 and choose `r`
rows `J` such that `U_J` is invertible. Every vector in the eigenspace is
determined by its coordinates on `J`. For each `epsilon in {+1,-1}^r`,
form `v=U U_J^{-1}epsilon` and check whether every coordinate is a sign.
This lists exactly the Boolean eigenvectors, including the planted one.
The same cutoff `2^r<=n^{27}` fails with probability `O(N^-3)`.

Exact elimination and these checks take polynomial bit complexity: every
row of `A-I` has four entries of magnitude one, so its minors have
`O(n)` bits by Hadamard's bound. Standard fraction-free elimination and
Cramer's rule give rational bases and reconstructed candidates with
polynomial bit length. The bound on `2^r` makes the full computation a
fixed polynomial. This route is closest to the original proposed
spectral recovery algorithm, but needs only logarithmic multiplicity.

## Scope and remaining spectral question

The argument establishes polynomial recovery in the exact requested
uniform-simple `(2,1)` model for all admissible block sizes. It supplies
no sharp constant for the finite-field first moment and does not prove
`dim_R ker(A-I)=1` with high probability. That is a strictly stronger
spectral conclusion requiring a separate argument; the moment session's
`../rsbm-cubic-moment-session/full-proof.md` addresses it independently.
The polynomial exponents above are coarse proof bounds, not practical
running-time predictions.
