# Independent audit: coarse type bounds suffice for polynomial recovery

Prepared 2026-11-15. This audits the exact configuration formula in
`spectral-gap/partitioning-rsbm-obstruction-session/finite-field-21-entropy.txt`.
It does **not** prove that the real eigenspace at eigenvalue 1 is simple.
The conclusion below is polynomial Boolean recovery, using the already
proved uniqueness of the Boolean partition with probability `1-O(N^-2)`.

## 1. Audited first-moment formula

After the cross matching is gauged to identity and the planted signs are
conjugated away, use

\[
M=\begin{pmatrix}C_+-I&-I\\-I&C_--I\end{pmatrix}.
\]

Both `C` matrices are independent degree-two configuration matrices on
`N` vertices. Loops count twice on their diagonal. Work over a fixed
prime field `F_p`. A vector `(x,z)` is in the kernel exactly when

\[
C_+x=x+z,\qquad C_-z=x+z.
\]

The ordered local profile at vertex `i` is `(A,D,B,E)=(x_i,z_i,B_i,E_i)`,
where `B_i` and `E_i` are the colors at the endpoints of the first of the
two distinguished stubs in the corresponding configuration. The other
two requested colors are

\[
C=A+D-B,\qquad F=A+D-E.
\]

For a profile-count table `n` with total `N`, define `m^+,m^-` as in the
source note. The symmetry and even diagonal conditions on each `m` are
exactly the conditions for a compatible pairing. There are

\[
W(m)=\prod_{u<v}m_{uv}!\prod_u(m_{uu}-1)!!
\]

compatible pairings: an arbitrary bijection for each pair of distinct
colors, and an ordinary perfect matching within each same-color pool.
Because the stubs are distinguished, no orientation factors are absent.
Each pairing and kernel vector determine their ordered profiles uniquely.
Consequently

\[
\mathbb E|\ker_{\mathbb F_p}M|
=\sum_{n\text{ valid}}
\frac{N!}{\prod n!}
\frac{W(m^+)W(m^-)}{((2N-1)!!)^2}.
\tag{1}
\]

This formula is valid for loops and parallel edges, with the stated loop
convention. It therefore applies to the degree-two configuration model
before conditioning on simplicity.

## 2. A short entropy proof, requiring no equality classification

Let `T=n/N`, `Q^+=m^+/(2N)`, and `Q^-=m^-/(2N)`. Then

\[
Q^+=\tfrac12\mathcal L(A,B)+\tfrac12\mathcal L(A,C),\qquad
Q^-=\tfrac12\mathcal L(D,E)+\tfrac12\mathcal L(D,F).
\]

The maps `B <-> C=A+D-B` and `E <-> F=A+D-E` are commuting bijections
of the local profile space. In particular, all four random vectors

\[
(A,D,B,E),\ (A,D,C,E),\ (A,D,B,F),\ (A,D,C,F)
\]

have the same entropy `H(T)`. Apply subadditivity to their partitions
into the two displayed color pairs, and average. Concavity then gives

\[
\begin{split}
H(T)
&\leq\tfrac12\{H(A,B)+H(A,C)+H(D,E)+H(D,F)\}\\
&\leq H(Q^+)+H(Q^-).
\end{split}
\tag{2}
\]

Thus the entropy exponent `Phi=H(T)-H(Q^+)-H(Q^-)` is nonpositive for
**every** local profile law. Symmetry of the edge tables is not needed
for (2). No claim about Gaussian prefactors or neighborhoods of the zero
set is needed for the following polynomial estimate.

Equivalently, symmetrize `T` under the two involutions. This leaves the
two `Q` laws unchanged and increases entropy. For the symmetrized law,
the exponent is exactly `-I((A,B);(D,E))`.

## 3. An explicit polynomial moment bound

Write `q=p(p+1)/2`. For an integer `t>=0`, put

\[
f(t)=\log(t!)-t\log t+t,
\]

with `0 log 0=0`. The elementary factorial estimates imply

\[
0\leq f(t)\leq 1+\tfrac12\log\max(1,t).
\tag{3}
\]

For a valid symmetric table `m` of total `2N`, expansion of the
factorials and `(2s-1)!!=(2s)!/(2^s s!)` gives

\[
\log W(m)
\leq N\log(2N)-N-NH(Q)
+q\bigl(1+\tfrac12\log(2N)\bigr).
\]

Indeed, an off-diagonal entry contributes an error `f(m_uv)`, while a
diagonal entry contributes `f(m_uu)-f(m_uu/2)<=f(m_uu)`. Also

\[
\log( (2N-1)!! )
\geq N\log(2N)-N-1-\tfrac12\log N.
\]

Together with the standard multinomial bound
`N!/prod n! <= exp(NH(T))`, each summand in (1) is at most

\[
e^{2(q+1)}(2N)^{q+1}\exp(N\Phi(T))
\leq e^{2(q+1)}(2N)^{q+1}.
\]

There are at most `(N+1)^(p^4)` profile-count tables, so

\[
\boxed{\quad
\mathbb E|\ker_{\mathbb F_p}M|
\leq e^{2(q+1)}(2N)^{q+1}(N+1)^{p^4}.
\quad}
\tag{4}
\]

For `p=3`, `q=6`, this is `O((N+1)^88)`. Conditioning the two
degree-two configurations on simplicity multiplies this bound by a
bounded constant, since the conditioning probability tends to
`exp(-3/2)>0`. Hence (4), up to a fixed constant, holds in the exact
uniform simple RSBM model.

The planted conjugation is invertible over `F_3`, although its signs
are unknown to the recovery algorithm. Thus the same estimate applies
to the kernel size of the observed matrix `A-I`.

## 4. Logarithmic nullity and a deterministic polynomial algorithm

Let `k=dim ker_F3(A-I)`. Equation (4) and Markov's inequality imply

\[
\Pr\{k>\lceil91\log_3(N+1)\rceil\}=O(N^{-3}).
\tag{5}
\]

The constants and exponents are deliberately coarse. They are fixed,
so the following algorithm has a deterministic polynomial running-time
bound, rather than merely a bound holding on a typical instance.

1. Compute a basis matrix `S` for `ker_F3(A-I)`, of size `2N x k`.
   If `k>ceil(91 log_3(N+1))`, return failure.
2. Choose `k` row indices `J` such that the square matrix `S_J` is
   invertible. Such rows exist because `S` has column rank `k`.
3. For every `a in {+1,-1}^k`, compute `v=S S_J^{-1} a` in `F_3`.
4. Discard `v` if any coordinate is zero. Otherwise lift its residues
   `1,2` uniquely to the integers `+1,-1`, obtaining `v_hat`, and check
   the integer identity `A v_hat=v_hat`.
5. Return any accepted vector with its first coordinate normalized to
   `+1`; if there is none, return failure.

Every Boolean eigenvector appears in step 3 because its pivot
coordinates belong to `{+1,-1}^k`. Conversely, the integer check accepts
only actual Boolean eigenvectors. The two signs remain distinct modulo
3; this is why a modulo-2 version of this enumeration would not work.

There are at most

\[
2^{\lceil91\log_3(N+1)\rceil}
\leq 2(N+1)^{91\log_3 2}
\]

candidates. All matrix arithmetic is over the fixed field `F_3` and all
integer checks use bounded integers. This proves polynomial running time
in the ordinary bit model, with a large fixed exponent.

The existing Boolean rigidity theorem states that the only accepted
vectors are the planted assignment and its negative with probability
`1-O(N^-2)`. Combining it with (5) gives polynomial exact recovery of
the planted partition, up to its global exchange, with probability
`1-O(N^-2)`.

## 5. What this does and does not settle

The argument bypasses the sharp finite-field moment asymptotic:
`E|ker|=O(p)` is unnecessary for polynomial recovery. A polynomial
moment bound already implies enough rank to enumerate the Boolean
candidates. The proof uses the uniform configuration model conditioned
on simplicity and makes no transfer from a single uniform permutation.

It leaves open whether `dim ker_R(A-I)=1` with high probability, and
does not provide a practical running-time guarantee. Its contribution
is an explicit polynomial recovery theorem for the hard `(2,1)` model.

## 6. Independent exact enumeration

`exact_moment_crosscheck.py` compares the type sum with a separate
enumeration of every pair of configuration stub matchings and its
modulo-3 matrix rank. It uses only the Python standard library. The
integer sums over pairing pairs agree:

| `N` | Direct pairing sum | Type sum | `E|ker_F3 M|` |
|---:|---:|---:|---:|
| 1 | 3 | 3 | 3 |
| 2 | 33 | 33 | 11/3 |
| 3 | 1323 | 1323 | 147/25 |

These include loops and parallel edges and test the exact counting
conventions. The proof itself is the combinatorial identity in section 1.
