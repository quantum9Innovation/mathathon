# A finite-field proof for even block sizes and internal degree at least three

This is a derived argument, not a theorem stated in the cited paper. The imported input is András Mészáros, *The distribution of sandpile groups of random regular graphs*, [arXiv:1806.03736v4](https://arxiv.org/pdf/1806.03736v4), Theorem 1.6 (PDF p. 3). Its model is the union of `d1 >= 3` independent uniform perfect matchings on an **even** number `N` of vertices. It does not directly cover odd block sizes or `d1 = 2`.

## Imported mixing statement

Fix an odd prime `p` and let `C_N` be the adjacency matrix of a sum of `d1 >= 3` independent uniform perfect matchings. For `x in F_p^N`, let `U_x` be distributed as follows:

- If `x = a 1`, then `U_x = d1 a 1` deterministically.
- If `x` is nonconstant, then `U_x` is uniform on the affine hyperplane `sum r = d1 sum x`, whose size is `p^(N-1)`.

For `V=F_p`, this is exactly the reference distribution in Theorem 1.6: every nonconstant vector has minimal affine coset `F_p`, and the tensor restriction is vacuous because `p` is odd. Extending both probabilities by zero outside their common support, put

`epsilon_N = sum_x sup_r |P(C_N x = r) - P(U_x = r)|`.

Then `epsilon_N -> 0` along even `N` for every fixed `p`. No uniformity in a growing prime is claimed.

## Single-block affine bound

Write `delta = d1-d2`, and choose `p` odd with `p` not dividing `d2`. Constants solve `(C_N-delta I)x=0` only when `x=0`. For nonconstant `x`, the reference probability `P(U_x=delta x)` is `p^(-N+1)` if `sum x=0` and zero otherwise. Hence

`E |ker(C_N-delta I)| <= 2 + epsilon_N`.

For every deterministic `b`, every nonempty solution set of `(C_N-delta I)x=b` is an affine copy of the kernel. Therefore, uniformly in `b`,

`sum_x P(C_N x = delta x+b) <= 2+epsilon_N`.

The same sum with `C_N x` replaced by `U_x` is at most `2+2 epsilon_N`.

## Two-block calculation

Let `C_1,C_2` be independent copies of `C_N`. Let `B` be any deterministic `N x N` matrix with row and column sums `d2`; it may subsequently be sampled independently. Put

```
A = [ C_1   B   ]
    [ B^T   C_2 ].
```

The expected number of vectors `(x,y)` in `ker(A-delta I)` is

`sum_(x,y) P(C_1 x = delta x - B y) P(C_2 y = delta y - B^T x)`.

Replace the first factor by its `U_x` reference, then replace the second. The first total error is at most `(2+epsilon_N)epsilon_N`, because for each fixed `x` the sum over `y` of the second factor is an affine solution expectation bounded above. The second error is at most `(2+2epsilon_N)epsilon_N`, using the corresponding reference affine bound in `x`. Total error is at most `4epsilon_N+3epsilon_N^2`, uniformly in `B`.

The reference sum is bounded by separating the following cases.

1. **Both `x,y` nonconstant.** The two hyperplane conditions coincide and are `sum x+sum y=0`, because `p` does not divide `d2`. There are at most `p^(2N-1)` pairs satisfying this condition, each contributing `p^(-2N+2)`. Contribution at most `p`.
2. **Both constant.** Writing `x=a1`, `y=b1`, the equations say `a+b=0`. Contribution exactly `p`.
3. **Exactly one constant.** If `x=a1`, the deterministic first-block equation says `By=-d2 a1`. For each `a`, this has at most `p^(N-rank_p B)` solutions. Each nonconstant `y` contributes at most `p^(-N+1)`. Contribution at most `p^(2-rank_p B)` in this orientation, and the same bound for the other.

Consequently,

`E |ker_Fp(A-delta I)| <= 2p + 2p^(2-rank_p B) + 4epsilon_N+3epsilon_N^2`.

If `B` is a simple `d2`-biregular biadjacency matrix and `p>d2`, choose a collection of rows with disjoint supports greedily. Each selected row excludes at most `d2(d2-1)+1` rows, so

`rank_p B >= N/[d2(d2-1)+1]`.

Thus, uniformly over all such `B`, the limsup of the expected kernel size is at most `2p`.

## Real conclusion and transfer

The planted vector `(1,-1)` is always in the integer kernel. If the real kernel has dimension at least two, the mod-`p` kernel does too (all integer minors of order `2N-1` vanish). Therefore

`limsup_(N even -> infinity) P(dim_R ker(A-delta I)>=2) <= 2/p`.

Letting fixed admissible primes `p` tend to infinity proves real kernel dimension one with high probability for the independent internal-matching model, uniformly over the simple regular cross matrix `B`.

The transfer to uniform-simple internal graphs is established by the following known contiguity, not by an assertion that the matching union itself is uniform. [Nguyen–Wood, arXiv:1806.10068v2, Section 4, proof of Theorem 1.6, PDF p. 8](https://arxiv.org/pdf/1806.10068v2) explicitly use [Janson (1995), Theorem 11](https://doi.org/10.1017/S0963548300001735) and [Molloy–Robalewska–Robinson–Wormald (1997), Theorem 3](https://doi.org/10.1002/(SICI)1098-2418(199705)10:3%3C305::AID-RSA1%3E3.0.CO;2-%23): the union of `d1>=3` independent uniform perfect matchings on an even vertex set is mutually contiguous with the `d1`-regular configuration model conditioned on having no loops. The MRRW publisher abstract explicitly states the all-`d1>=3` contiguity result.

Apply this relation to both independent internal factors. Finite products preserve mutual contiguity. An independent cross matrix with an arbitrary common distribution can be adjoined as well: if `f_N(C_1,C_2)` is the conditional probability over the cross matrix of the failure event, then `0<=f_N<=1` and its matching-model expectation tends to zero. Markov's inequality and product contiguity imply that its loopless-configuration expectation tends to zero. Finally, conditioning both configuration graphs on simplicity has probability bounded below, and yields exactly two independent uniform simple `d1`-regular graphs; the cross matrix retains its independent original distribution. Thus the kernel event holds with high probability in the requested uniform-simple RSBM along even `N`. No quantitative failure rate is supplied by these contiguity and fixed-prime arguments.

This establishes the requested claim for **even `N` and every fixed `d1>=3`, `d2>0`**. When `d1` is odd, admissibility already forces `N` even. For even `d1>=4`, odd admissible block sizes remain outside this particular imported mixing theorem. The case `(d1,d2)=(2,1)` remains outside it as well.
