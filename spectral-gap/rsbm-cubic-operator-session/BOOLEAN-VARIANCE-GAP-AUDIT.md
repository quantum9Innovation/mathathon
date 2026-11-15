# Independent audit of the root's uniform Boolean entropy gap

Read and checked against the actual
`../rsbm-general-coarse-recovery-root.txt`, Section 2, on 2026-11-15.
The calculation is correct for every fixed `a>b>=1`, hence `a>=2`.
It supplies a unified Boolean rigidity argument, including the cubic
case, beyond the `a>=3` mean/Fourier argument in the first general note.

## Exact entropy loss

First symmetrize each star under permutations of internal slots and of
cross slots. This preserves all edge-table laws and can only increase
star entropy. It is therefore enough to prove the upper bound on the
symmetrized entropy exponent. All labels in this audit are actual
integer signs, not residues in a finite field.

Write `X,Y` for roots in the two blocks, `A_i,C_i` for internal neighbors,
and `B_j,D_j` for cross neighbors. Their integer constraints are

\[
 \sum_{i=1}^a A_i+\sum_{j=1}^b B_j=\lambda X,
 \qquad
 \sum_{i=1}^a C_i+\sum_{j=1}^b D_j=\lambda Y,
 \qquad \lambda=a-b>0.
\]

Let `P_+` be the law of the plus root and the retained neighbors
`A_1,...,A_{a-1},B_1,...,B_b`. Define its conditional total correlation

\[
 J_+=(a-1)H(A_1\mid X)+bH(B_1\mid X)
       -H(A_1,\ldots,A_{a-1},B_1,\ldots,B_b\mid X),
\]

and define `J_-` analogously. Both are nonnegative. Because the omitted
neighbor is determined by the retained labels, the entropy cancellation
is exactly

\[
 L:=-\Phi=
 \frac{a-2}{2}\{I(X;A_1)+I(Y;C_1)\}
 +bI(X;B_1)+J_++J_- .                               \tag{1}
\]

For an unsymmetrized type, its additional entropy loss is nonnegative;
the eventual upper bound on `Phi` therefore still holds.

## Product comparison with the same internal conditional laws

Let `Q=law(Y)=law(B_j)`. Define `R_+` by keeping the same root law as
`P_+`, taking the retained internal neighbors conditionally independent
with their actual common conditional law `law(A_1|X)`, and taking the
cross neighbors independently with common law `Q`, independent of the
root and the internal neighbors. Direct expansion of relative entropy
gives

\[
 D(P_+\Vert R_+)=J_++bI(X;B_1)\le L.                   \tag{2}
\]

This expansion is valid even when probabilities vanish: every point of
positive `P_+` mass has positive mass under the corresponding product of
its marginals, and therefore under `R_+`. Zero-root-probability
conditionals can be chosen arbitrarily.

Set

\[
 m(X)=\mathbb E(A_1\mid X),\qquad
 v(X)=\operatorname{Var}(A_1\mid X),\qquad
 W=\lambda X-\sum_{i<a}A_i-\sum_j B_j.
\]

Under `P_+`, `W=A_a`, and slot exchangeability gives

\[
 \mathbb E_{P_+}(W-m(X))^2=\mathbb E v(X).
\]

Under `R_+`, conditional independence gives the exact formula

\[
\begin{split}
 \mathbb E_{R_+}(W-m(X))^2
  ={}&(a-1)\mathbb E v(X)+b\operatorname{Var}(Y)\\
     &+\mathbb E\{\lambda X-a m(X)-b\mathbb EY\}^2.
\end{split}
\]

Consequently, for every `a>=2`,

\[
 \mathbb E_{R_+}(W-m(X))^2
 -\mathbb E_{P_+}(W-m(X))^2
 \ge b\operatorname{Var}(Y).                          \tag{3}
\]

The coefficient `a-2` is nonnegative, so the argument includes `a=2`.
No independence of internal neighbors from the root is being assumed.

## Pinsker constant and explicit gap

For any retained tuple of signs,

\[
 |W-m(X)|\le\lambda+(a-1)+b+1=2a.
\]

Thus the same function `f=(W-m(X))^2` lies in `[0,4a^2]` under both
laws, including tuples that do not satisfy the original star equation.
With total variation defined as half the `L1` distance,

\[
 b\operatorname{Var}(Y)
 \le |\mathbb E_{R_+}f-\mathbb E_{P_+}f|
 \le4a^2\operatorname{TV}(P_+,R_+)
 \le4a^2\sqrt{L/2}.
\]

Therefore

\[
 \boxed{\quad -\Phi\ge
 \frac{b^2\operatorname{Var}(Y)^2}{8a^4}.\quad}        \tag{4}
\]

The block-reversed argument gives the same bound using `Var(X)`. For a
balanced alternative flipping fraction `r` in each block,
`Var(X)=Var(Y)=4r(1-r)`. Hence

\[
 \boxed{\quad\Phi\le
 -\frac{2b^2}{a^4}r^2(1-r)^2,\qquad a>b\ge1.\quad}    \tag{5}
\]

All constants in the root note are correct. The deficit is uniform over
all feasible integer Boolean star laws and strictly negative for
`0<r<1`. It has no prime, divisibility, residue-class, or extra
even-block-size hypothesis.

## Consequence with the independently proved count

Equation (1) of `GENERAL-POLYNOMIAL-RECOVERY.md`, now with Boolean sign
profiles and integer constraints, is an exact type count for these
partitions. Its factorial prefactors and number of types are polynomial
in `N` at fixed degrees. On any fixed interval
`epsilon<=r<=1/2`, (5) makes the total expected number of alternatives
exponentially small. The already proved small-support real-eigenvector
estimate handles `r<epsilon`, because `tau-sigma` is an eigenvector
supported precisely on the flipped vertices.

This proves Boolean rigidity uniformly for all fixed `a>b>=1`, including
the cubic case. Combined with the general polynomial binary kernel
moment and the affine algorithm in `GENERAL-POLYNOMIAL-RECOVERY.md`,
it establishes polynomial exact recovery for every fixed assortative
degree pair and every admissible block size. The coarser full-
finite-field phase analysis is unnecessary for this recovery theorem.
