# Boolean rigidity near the planted partition

Fix integers `a>b>0`, let `D=a+b` and `delta=a-b`, and let each planted block have `N` vertices. The two internal graphs are independent uniform simple `a`-regular graphs; the cross graph is independent uniform simple `b`-regular bipartite. All limits are along admissible sizes, including odd `N` when `a` is even.

The unique-neighbor exposure proposition in `deterministic-reductions.md`, Section 4, gives constants `epsilon>0` and `C<infinity`, depending only on `a,b`, such that

\[
\Pr\{\exists\,0\ne x:\ Ax=\delta x,
\ |\operatorname{supp}x|\le\epsilon N\}
\le C N^{-(D-2)(\delta+1)}.
\]

It uses the internal and bipartite configuration models and conditioning on simplicity. Its proof has no parity assumption beyond `aN` being even. It is a standard unique-neighbor argument, not an imported full simplicity theorem.

**Near-planted corollary.** With probability at least

\[
1-O_{a,b}\big(N^{-(D-2)(\delta+1)}\big),
\]

there is no other admissible sign partition whose signs differ from the planted signs at at most `epsilon N` vertices. Equivalently, writing `k` for the number of flipped vertices in each planted block, there is no alternative with `1<=k<=epsilon N/2`.

**Proof.** Let `sigma` be the planted assignment and let `tau` be another sign vector satisfying `A tau=delta tau`. Both are balanced because \(A\mathbf1=D\mathbf1\) and `D!=delta`. Hence the flipped sets in the two planted blocks have equal size `k`. The nonzero vector

\[
x=\sigma-\tau
\]

is a `delta`-eigenvector with support size exactly `2k`. Applying the proposition proves the probability bound. Also `k>=delta+1` deterministically: a positive coordinate of `x` is `+2`, all positive coordinates lie in the first planted block, and its eigenvector equation requires at least `delta` positive neighbors. The same argument applies to the negative coordinates. QED.

Replacing `tau` by `-tau` replaces `k` by `N-k`; thus one may choose its global orientation with `k<=N/2` before dividing a Boolean-rigidity argument into near and macroscopic overlap regimes.

For internal degree `a=4`, including odd `N`, the near-planted bounds are:

| Cross degree `b` | `delta` | Necessary lower bound on `k` | Upper bound on near-planted failure |
|---|---:|---:|---:|
| 1 | 3 | 4 | `O(N^-12)` |
| 2 | 2 | 3 | `O(N^-12)` |
| 3 | 1 | 2 | `O(N^-10)` |

These bounds concern the near-planted alternatives only. An all-overlap rigidity theorem still requires the separate macroscopic estimate.

## Conditional enumeration when the real kernel is larger

Let `L=ker_Q(A-delta I)` have dimension `r`. Compute an exact rational basis and choose `r` coordinate positions on which restriction is injective, by selecting independent rows of its basis matrix. Every sign vector in `L` is determined by its signs at those `r` positions. Enumerating their `2^r` assignments, solving for the corresponding vector of `L`, and testing all coordinates for membership in `{+1,-1}` lists every admissible sign vector in

\[
2^r\operatorname{poly}(N)
\]

bit operations. Thus Boolean rigidity together with an independent bound `r=O(log N)` would give polynomial-time exact recovery even without real-kernel simplicity.

The small-support proposition does **not** imply that dimension bound. If every nonzero vector in an `r`-dimensional subspace of `R^(2N)` has support at least `s`, the elementary resulting bound is only `r<=2N-s+1`.

There is a concrete linear-algebra obstruction to any stronger inference from support and Boolean rigidity alone. Let `t_1,...,t_(2N)` be distinct real numbers, let `sigma` be balanced, and consider vectors

\[
(\sigma_i p(t_i))_{i=1}^{2N},\qquad \deg p\le N-1,
\]

subject also to the one linear constraint that their coordinate sum is zero. This subspace contains `sigma`, has dimension at least `N-1`, and every nonzero vector has support at least `N+1`. Its only sign vectors are `sigma` and `-sigma`: otherwise `p(t_i)^2=1` at all `2N` distinct points, forcing the polynomial `p^2-1`, of degree at most `2N-2`, to vanish identically. This is a subspace example, not a claim about the RSBM adjacency law. It shows precisely why the support estimate and Boolean uniqueness alone cannot justify logarithmic-dimension enumeration.
