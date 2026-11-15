# Odd block sizes: finite-field calculation after vertex insertion

This is a separate extension of the frozen even-block theorem. Its graph-law and colored-matching constructions are proved in `odd-block-surgery.md`. The following calculation establishes the required kernel estimate for those constructions, uniformly over the exposed local data.

Fix internal degree `k>d2>0`, with `k` even and `k>=6`, and let `N=n+1` be odd, so `n` is even. Put `delta=k-d2`. Fix an odd prime `p` not dividing `d2` and take all matrices over `F_p` for the counting argument.

## Generic partially exposed internal blocks

For each block, expose every matching touched by the `s=k/2` selected surgery edges and expose which edges were selected. The remaining internal matchings are independent and uniform, with counts `r_1,r_2>=k/2>=3`. Conditional on this exposed data the two internal adjacency matrices have the form

```
H_1 = [[M_1+F_1,u],[u^T,0]],
H_2 = [[M_2+F_2,z],[z^T,0]],
```

where `M_i` is a sum of `r_i` independent uniform perfect-matching matrices on the `n` old vertices; the matrices `F_i` and vectors `u,z` are fixed; `F_i` are symmetric; `u,z` are zero-one vectors, each with exactly `k` entries equal to one; and

```
F_1 1=(k-r_1)1-u,
F_2 1=(k-r_2)1-z.
```

These identities just express that every old vertex has degree `k` after including its possible edge to the inserted root.

Fix any simple `d2`-biregular cross matrix, split at the two root vertices as

```
B=[[B0,v],[w^T,b]],   b in {0,1}.
```

Thus `B0 1=d2 1-v`, `B0^T 1=d2 1-w`, and `sum v=sum w=d2-b`. The two-block eigenvector is written `(x,alpha;y,beta)`, with `x,y in F_p^n` and scalar root coordinates `alpha,beta`.

Its old-vertex equations are

```
M_1 x=(delta I-F_1)x-u alpha-B0 y-v beta,
M_2 y=(delta I-F_2)y-z beta-B0^T x-w alpha.
```

The root equations are

```
u^T x+w^T y+b beta=delta alpha,        (R1)
v^T x+z^T y+b alpha=delta beta.        (R2)
```

## Uniform affine bounds still hold

For a matching sum `M_i`, let `q_x^{(r_i)}` be Mészáros's reference law: point mass at `r_i a 1` for `x=a1`, and uniform mass `p^{-n+1}` on `sum t=r_i sum x` for nonconstant `x`. Let

`epsilon_n=max_{k/2<=r<=k} sum_x sup_t |P(M^(r)x=t)-q_x^(r)(t)|`.

There are finitely many possible `r>=3`, so Mészáros Theorem 1.6 gives `epsilon_n->0` for fixed `p`.

For every fixed vector `c`, the reference affine sum

`sum_x q_x^(r_1)((delta I-F_1)x+c)`

is at most `2`. For nonconstant `x`, the scalar condition is

`(d2 1-u)^T x=sum c`.

This is a nonzero linear functional because there are old vertices outside the fixed-size support of `u` and `p` does not divide `d2`. Hence at most `p^{n-1}` vectors contribute mass `p^{-n+1}`. For constant `x=a1`, the vector equation requires

`c=a(d2 1-u)`,

which allows at most one `a`. The same argument applies to the other block with `z`. Actual affine sums are therefore at most `2+epsilon_n`.

## Replacing the two random factors

Expand the expected size of the finite-field kernel by summing over `x,y,alpha,beta`, including the indicator of the two root equations. The conditional independence of `M_1,M_2` factors the two old-vertex probabilities. Replace each by its reference mass as in the even-block proof.

For every fixed `alpha,beta`, the first error is at most `(2+epsilon_n)epsilon_n` and the second at most `2epsilon_n`; dropping root indicators can only enlarge the bounds. Summing over the `p^2` root-coordinate pairs bounds the total replacement error by

`p^2(4epsilon_n+epsilon_n^2)=o(1)`.

The bound is uniform over all exposed `F_i,u,z`, all `r_i`, and all prescribed simple regular `B`.

## Both old-coordinate vectors nonconstant

The first reference hyperplane equation is

```
d2(sum x+sum y)-u^T x-w^T y
    +k alpha+(d2-b)beta=0.
```

After substitution of `(R1)`, this becomes

`sum x+sum y+alpha+beta=0`.             `(R0)`

The second reference hyperplane equation similarly becomes `(R0)` after substitution of `(R2)`. Thus for fixed root coordinates the constraints on `(x,y)` are exactly the three affine equations with coefficient rows

```
(1^T,1^T), (u^T,w^T), (v^T,z^T).
```

These rows have rank three for all sufficiently large `n`, over every field. A coordinate in the A block outside `supp u union supp v` first forces the coefficient of the first row to vanish. Since `|supp u|=k>d2>=|supp v|`, a coordinate in `supp u` outside `supp v` then forces the coefficient of the second row to vanish. Finally `z` is nonzero, so the coefficient of the third row vanishes.

There are at most `p^{2n-3}` solutions for each of `p^2` root-coordinate pairs. Each pair of reference masses is `p^{-2n+2}`. This contribution is at most `p`.

## Both old-coordinate vectors constant

Put `x=a1,y=c1`. The old reference vector equation in the first block reduces to

`d2(a+c)1+(alpha-a)u+(beta-c)v=0`.

Outside the local supports this forces `a+c=0`; on `supp u minus supp v` it then forces `alpha=a`. The second old reference equation uses `|supp z|=k>|supp w|` to force `beta=c`. The root equations are then satisfied exactly by the planted vector. There are precisely `p` possibilities.

## Exactly one old-coordinate vector constant

If `x=a1` and `y` is nonconstant, the first old reference equation requires

`B0 y=-d2 a1-(alpha-a)u-v beta`.

For each choice of `a,alpha,beta`, there are at most `p^{n-rank_p B0}` possible `y`; each remaining reference mass is at most `p^{-n+1}`. This orientation contributes at most `p^{4-rank_p B0}`. The other contributes the same bound. Since deleting a row and column lowers rank by at most two,

`rank_p B0 >= rank_p B-2 >= N/[d2(d2-1)+1]-2`.

The mixed terms tend to zero uniformly in the prescribed cross graph.

## Conditional conclusion

The full conditional moment bound is

```
E |ker_Fp(A-delta I)|
 <= 2p+2p^{4-rank_p B0}+p^2(4epsilon_n+epsilon_n^2).
```

The right side is uniform over the exposed local data. Averaging over those data, taking `n->infinity` for fixed `p`, using real corank at least two implies finite-field corank at least two, and then sending fixed primes to infinity proves simplicity with high probability in the colored-surgery model.

The graph-law transfer in the companion surgery note therefore extends the result to **odd block sizes and every fixed even internal degree `d1=k>=6`**, uniformly over any prescribed simple `d2`-biregular cross graph with `0<d2<k`. Together with the frozen even-block theorem, this covers all admissible sizes for `d1=3` and every `d1>=5`; the remaining cases are `(d1,d2)=(2,1)` and odd block sizes for `d1=4`.

The construction leaves only two untouched matchings when `k=4` and both selected edges touch different colors. Mészáros's degree-at-least-three theorem cannot be applied to that component of the selection law. Discarding it would discard an event of probability bounded away from zero, so the above proof does **not** extend to `k=4` by the same argument.
