# Adverse audit: aggregate fibers give a universal polynomial exponent

**Conclusion.** The proposed improvement is correct. For every fixed
`a>=2`, `b>=1`, every admissible `N`, every prime `p`, and every field
target `lambda`, the configuration model satisfies

\[
\boxed{
\mathbb E|\ker_{\mathbb F_p}(A-\lambda I)|
\le e^{p(p+1)+2+p^2}
 (aN+1)^{p(p+1)+2+2p^2}(bN+1)^{2p^2}.
}
\tag{1}
\]

For `p=2`, this reads

\[
\boxed{
\mathbb E\,2^{\dim_{\mathbb F_2}\ker(A-\lambda I)}
\le e^{12}(aN+1)^{16}(bN+1)^8.
}
\tag{2}
\]

Consequently the exponent of `N` is `24` for every fixed degree pair.
This is stronger than the earlier local-type enumeration bound.

## 1. Exact fibers contain all local-type and multinomial choices

Use the two internal distinguished-stub pairings and the cross-stub
bijection from the previous audit. One may use the original matrix
`A-lambda I`, with local plus constraint

\[
 \sum_{i=1}^a A_i+\sum_{j=1}^b B_j=\lambda X,
\]

and the corresponding minus constraint. The conjugated sign convention
works identically.

Fix a valid aggregate table triplet

\[
 m_+,m_-,h,
\]

where the internal tables are symmetric with even diagonals, their
entries sum to `aN`, and the oriented cross tables agree after
transposition and have total `bN`.

Let `Omega(m_+,m_-,h)` be the set of all ordered arrays of `N` plus
star profiles and `N` minus star profiles that satisfy the local field
constraints and have precisely these aggregate tables. Profiles retain
all distinguished slot orderings. Thus `Omega` includes root labels,
neighbor-label choices, local type choices, vertex orderings, and slot
orderings. None of these should be counted again outside `|Omega|`.

For each element of `Omega`, the number of compatible configurations
is the same:

\[
 W(m_+)W(m_-)\prod_{u,v}h_{uv}!,\qquad
 W(m)=\prod_{u<v}m_{uv}!\prod_u(m_{uu}-1)!!.
\]

Every configuration and kernel vector determine exactly one element
of exactly one such fiber. Therefore

\[
\begin{split}
\mathbb E|\ker_{\mathbb F_p}(A-\lambda I)|
=\sum_{\text{valid }m_+,m_-,h}
|\Omega(m_+,m_-,h)|\,
\frac{W(m_+)W(m_-)}{((aN-1)!!)^2}
\frac{\prod_{u,v}h_{uv}!}{(bN)!}.
\end{split}
\tag{3}
\]

Equivalently, the fiber cardinality is exactly the sum of the two
multinomial factors over all pairs of local types inducing the fixed
triplet. Thus (3) is a regrouping of the previously audited exact
formula, not a new probabilistic approximation.

## 2. Fiber entropy bound

There are two valid proofs. The second shows that no exchangeability
assumption is actually needed.

### Exchangeability proof

Put the uniform law on a nonempty fiber. Independent permutations of
the `N` plus coordinates and of the `N` minus coordinates preserve it.
At every vertex one may also permute its `a` internal slots and its
`b` cross slots. These operations preserve the local equation and all
three tables. They are bijections of the fiber, even when some labels
repeat and the group action is not free.

Hence the one-site laws `T_+,T_-` are exchangeable in their slots and
have pair tables

\[
 F_+=m_+/(aN),\qquad F_-=m_-/(aN),\qquad G=h/(bN).
\]

Entropy subadditivity over the `2N` sites gives

\[
 \log|\Omega|\le N\{H(T_+)+H(T_-)\}.
\]

The proved general star entropy inequality says

\[
 H(T_+)+H(T_-)
 \le\frac a2\{H(F_+)+H(F_-)\}+bH(G).
\]

Combining these gives

\[
\boxed{
 \log|\Omega|
 \le N\left[\frac a2\{H(F_+)+H(F_-)\}+bH(G)\right].
}
\tag{4}
\]

### Averaged-marginal proof

More generally, let `Omega` be any nonempty subset of a fiber. Under
its uniform law, let `T_i^+,T_j^-` denote the individual site laws and
let `T_+,T_-` denote their averages within the two classes. Then

\[
\begin{split}
\log|\Omega|
&\le\sum_iH(T_i^+)+\sum_jH(T_j^-)\\
&\le N\{H(T_+)+H(T_-)\},
\end{split}
\]

where the second inequality is entropy concavity. Because all arrays
have the same aggregate tables, the averaged stub tables of `T_+,T_-`
are exactly `F_+,F_-,G`. The star entropy inequality already
symmetrizes arbitrary site laws, so it applies to these averages and
proves (4). This proof handles arbitrary restrictions on a fiber and
does not require the uniform law to be a product law or exchangeable.

## 3. Factorial errors and table counting

Write `q=p(p+1)/2`. The previously audited zero-safe estimates give

\[
\begin{split}
 \frac{W(m_+)}{(aN-1)!!}
 &\le e^{q+1}(aN+1)^{q+1}e^{-(aN/2)H(F_+)},\\
 \frac{W(m_-)}{(aN-1)!!}
 &\le e^{q+1}(aN+1)^{q+1}e^{-(aN/2)H(F_-)},\\
 \frac{\prod_{u,v}h_{uv}!}{(bN)!}
 &\le e^{p^2}(bN+1)^{p^2}e^{-bNH(G)}.
\end{split}
\]

Multiplication by (4) cancels all three entropy terms. Each triplet
therefore contributes at most

\[
 e^{2(q+1)+p^2}(aN+1)^{2(q+1)}(bN+1)^{p^2}
\]

to (3). There are at most `(aN+1)^{2p^2}` pairs of internal tables and
at most `(bN+1)^{p^2}` cross tables. This counts invalid and
unrealizable tables too, which only makes it an upper bound. Summing
proves (1). For `p=2`, the internal exponent is
`2(q+1)+2p^2=8+8=16`, the cross exponent is `2p^2=8`, and the
constant is `e^{8+4}=e^{12}`, proving (2).

## 4. Adverse checks

- **Hidden multinomial factors:** absent. They are already included
  exactly in `|Omega|`, as seen by regrouping the local-type formula.
- **Dependencies between vertices or blocks:** harmless. Entropy
  subadditivity is an upper bound and requires no independence.
- **Distinguished stub order:** retained in every profile. Slot
  permutations act bijectively; repeated labels do not require a free
  group action or introduce an orbit-size denominator.
- **Root laws:** the row marginals of the averaged internal tables
  are the root laws. Internal symmetry identifies their column laws;
  cross-table consistency identifies the cross-neighbor root laws.
  These are exactly the marginal hypotheses of the entropy lemma.
- **Empty fibers:** omitted. Their contribution is zero and no uniform
  law is needed.
- **Loops and parallel edges:** remain included with the same
  distinguished-stub conventions as the original exact formula.
- **Characteristic two:** the omitted internal slot has coefficient
  one, so it is determined even if `lambda=0` in the field.
- **Additional parity:** none. Only the original admissibility of
  `aN` even is required before simple conditioning.

## 5. Consequences in the simple model

For fixed `a,b`, conditioning the three independent configuration
factors on simplicity costs only a degree-dependent constant and
gives exactly the requested independent uniform simple graphs.
Thus (2) yields

\[
 \mathbb E2^k=O_{a,b}(N^{24}),\qquad
 k=\dim_{\mathbb F_2}\ker(A-(a-b)I).
\]

The universal cutoff `2^k<=n^{27}` has failure probability
`O_{a,b}(N^-3)`. Binary affine enumeration therefore uses
`O_{a,b}(n^28)` elementary operations in the worst case. Without the
cutoff it lists all equitable partitions in
`O_{a,b}(n^25)` expected elementary operations. Index bit lengths
introduce at most logarithmic factors in the usual indexed bit model.
Both exponents are independent of the fixed degree pair.

The Boolean rigidity argument for `a>=3` can also use these fibers
with exact integer mark-bit constraints. The averaged-marginal proof
continues to hold, and its strict entropy gap at macroscopic overlap
then gives a polynomial prefactor times `exp(-cN)`; no count of
local-profile types is necessary there either.

Combined with the proved general small-support estimate and the
separate cubic rigidity proof, this gives one unified theorem: every
fixed `a>b>0`, along all admissible `N`, admits a deterministic
polynomial recovery algorithm with success probability
`1-O_{a,b}(N^-2)` and the universal operation bounds above. It still
does not assert real eigenspace simplicity.
