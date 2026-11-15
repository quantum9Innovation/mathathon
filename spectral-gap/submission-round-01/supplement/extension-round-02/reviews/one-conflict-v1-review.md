# Review of the one-conflict envelope, revision 1

Date: November 14, 2026, America/Los_Angeles.

Decision: Accept Theorem SG-E4-A and Corollary SG-E4-B for their stated domains. No unsupported inference was found. The exact maximum is established for $b=1$. The factor $2^{b-1}$ for $b>1$ is accepted as an upper bound only.

The reviewed proof SHA256 is 4ed2c2cbe44c453eb401ebbf20eae09b35a9365d018f86abee262fc38dca83f4. The manifest SHA256 is e30019e3999be5d7857136956d86fdb51cd46f813677ee205d0bea601761597a. All seven output hashes and all three dependency hashes match that manifest.

Prior exposure includes the base mixed theorem, its mathematical review and its integration draft. This review independently reconstructs the new argument. The author's checker files were hashed but were not read, imported or executed. The separate integration candidate was not inspected before this review was frozen.

## 1. Accepted scope

For independent uniform permutations of a common dimension $n\ge2$, let $X$ be the original product with arbitrary permitted nonnegative integer powers. Let $a$ be its distinct colored support size, $h$ the consistent centered-singleton count and $b$ the inconsistent centered-singleton count. For $2\le a\le n$ and $b\ge1$, the accepted bound is

$$
|\mathbb EX|
\le
2^{b-1}
\frac{n^{-h-1}P_h(n,a-h-1)}{(n)_{a-1}}.
$$

When $b=1$, the right side without an extra factor is attained for every $0\le h\le a-2$. A centered singleton means precisely powers $(1,0)$. The theorem counts such cells, not the number of conflicting pairs.

## 2. Reconstruction of the decisive steps

### OC1. The kernel difference

Accepted. The positive polynomial gives

$$
K_{j,s}(n)=\frac{n^sP_j(n,s)}{(n)_{j+s}},
\qquad j+s\le n.
$$

Under depletion $s$, condition on the final requested compatible indicator. Its success probability is $1/(n-s)$. On success, the other $j$ requested cells remain compatible, the permutation dimension decreases by one, and the centered factors still have scale $n$. Therefore

$$
\mu_{j+1}(n,s)
=\frac{n}{n-s}\mu_j(n,s+1)-\mu_j(n,s).
$$

Multiplication by $F_n(s)$ gives exactly

$$
K_{j+1,s}=K_{j,s+1}-K_{j,s}\le K_{j,s+1}.
$$

The condition $j+s+1\le n$ ensures that the success probability is defined. At $j=0,s=n-1$, the remaining moment after success is the empty moment $\mu_0(n,n)=1$. No first moment on a zero-dimensional permutation is used.

### OC2. Positivity, exposure monotonicity and color merging

Accepted independently from the block weights. Each block weight

$$
\bigl((|B|-1)n+s\bigr)(|B|-1)!
$$

is nonnegative and increases with $s$. The multiplier $n^s/(n)_{j+s}$ has successive ratio $n/(n-j-s)\ge1$ whenever the next index is permitted. This proves kernel monotonicity, including $j=0$.

For two colors, take partitions of two disjoint labeled sets and unite them. These are a subset of all partitions of the union. Replacing both exposure parameters by their sum only increases the weights. Together with

$$
(n)_{j_1+s_1}(n)_{j_2+s_2}
\ge (n)_{j_1+s_1+j_2+s_2},
$$

this proves the stated kernel merger. Iteration uses the total index bound, not a separate unrecorded large-dimension hypothesis.

### OC3. The conflicting-neighbor case

Accepted. Let $T$ contain the $h$ globally consistent centered singletons and distinguish an inconsistent centered singleton $e_*$. If the selected support $S$ is internally incompatible in a color, its indicator product is identically zero.

Otherwise, when $S$ contains a conflicting neighbor of $e_*$, the distinguished indicator vanishes on the selected event. The remaining centered cells in $T$ survive conditioning because they are consistent relative to the entire original support. Thus the exact expression is

$$
G_S=-n^{-h-1-|S|}\prod_cK_{h_c,s_c}(n).
$$

Merge the kernels and increase $|S|$ to $r=a-h-1$. This gives the selected-support bound in equation (9), with the correct extra factor $1/n$ and the correct sign.

### OC4. The omitted-neighbor case

Accepted. Every neighbor of $e_*$ lies outside $T$, since consistency is defined against all requested cells of the same color. Thus $V=E\setminus(T\cup\{e_*\})$ contains at least one neighbor and $r\ge1$. This proves $h\le a-2$.

If $S$ contains no neighbor, it misses at least one member of $V$, so $|S|\le r-1$. The cells of $S$, $T$ and $e_*$ are compatible. Exact conditioning therefore leaves $h+1$ centered factors, and color merging gives $K_{h+1,|S|}$. The exact difference identity then gives

$$
K_{h+1,|S|}
\le K_{h,|S|+1}
\le K_{h,r}.
$$

All indices in this chain are at most $h+r=a-1\le n-1$. The omitted neighbor is counted only once. There is no need for $e_*$ to have exactly one neighbor.

### OC5. Arbitrary multiplicities and the general corollary

Accepted. For a binary indicator, each remaining factor is exactly $c+dM$, with $d\ge0$ for $n\ge2$. The selected-support estimate sums to

$$
n^{-a}K_{h,r}\prod_{e\in V}(d_e+n|c_e|).
$$

The factor $n^{-|S|}$ is essential here. Moving it into the product gives $d_e+n|c_e|$, with no missing power of $n$.

For a raw-containing factor, the weight is at most one. For a pure centered repeated power, the even and odd estimates in the proof give at most $1-1/n$, including $n=2$. A centered singleton has weight exactly two. Precisely $b-1$ such singletons remain in $V$, because all $h$ consistent singletons and the distinguished inconsistent singleton were removed. This proves $2^{b-1}$ for every $b\ge1$ without asserting sharpness.

The conversion

$$
n^{-a}K_{h,a-h-1}
=\frac{n^{-h-1}P_h(n,a-h-1)}{(n)_{a-1}}
$$

is correct. The comparison with the old $2^b n^{-a}K_{h,a-h}$ bound follows from monotonicity and is indeed at most one half.

### OC6. Attainment and endpoints

Accepted. Use one color with the distinguished centered cell $(1,a)$, raw diagonal cells $1,\ldots,r$ and centered diagonal cells $r+1,\ldots,a-1$, where $r=a-h-1$.

The raw cell $(1,1)$ makes the distinguished centered cell inconsistent. Column $a$ is absent from all other requested cells. All $h$ other centered cells remain consistent, so the construction has exactly the prescribed $b=1$ and $h$.

On the raw event, $M_{1a}=0$. The event probability is $1/(n)_r$, and the surviving centered moment is $n^{-h}\mu_h(n,r)$. The expectation is exactly the negative of the proposed envelope. Since $r\ge1$, this moment is positive, including $h=0$ with its empty-product convention.

At $a=n$, the raw conditioning leaves $n-r=h+1$ rows and columns. Hence there is still room for all $h$ centered cells and one unused row and column. All factorial denominators remain positive. The cases $h=0$, $h=a-2$, and the smallest case $n=a=2$ are valid.

## 3. Independent original-product checks

The owned checker evaluates the original powers directly on every permutation within each color. It then multiplies the exact rational expectations of independent colors. It does not use the author's affine expansion to compute expectations. The bound is evaluated separately from the positive block recurrence.

All checks passed.

| Independent family | $b=1$ cases | $b\ge2$ cases |
| --- | --- | --- |
| All supports of sizes $2$ through $n$ in two colors, $n=2,3$, with five raw, singleton, repeated and mixed power choices | 20,224 | 3,116 |
| All one-color supports of sizes $2$ through $4$, $n=4$, with raw or centered-singleton factors | 11,456 | 17,052 |
| Sampled three-color products, $n=5,6$, with powers through seven and raw powers through four | 299 | 20 |

The 52,167 original-product checks include 48,552 full-support cases $a=n$, 20,548 cases with repeated or mixed powers, and 14,855 cases using multiple colors. The seed and exact ranges are in the owned checker.

Further checks covered all 84 attaining triples through $n=8$, 679 kernel difference identities through $n=15$, and 161 direct depleted moments through $n=8$. These finite checks corroborate the proof rather than replace it.

Representative independent evaluations, with one-based coordinates, are:

| Pattern | Exact expectation | Proposed envelope |
| --- | --- | --- |
| $n=2$, $(M_{12}-1/2)M_{11}$ | $-1/4$ | $1/4$ |
| $n=3$, $(M_{13}-1/3)M_{11}(M_{22}-1/3)$ | $-1/54$ | $1/54$ |
| $n=4$, $(M_{14}-1/4)M_{11}(M_{22}-1/4)(M_{33}-1/4)$ | $-1/256$ | $1/256$ |
| $n=4$, $(M^A_{12}-1/4)M^A_{11}(M^B_{11}-1/4)M^B_{22}$ for independent colors | $-1/768$ | $1/192$ |
| $n=2$, $(M_{11}-1/2)(M_{12}-1/2)$, with $b=2$ | $-1/4$ | $1/2$ |

For the omitted-neighbor branch, at $n=4$ the selected product $(M_{14}-1/4)(M_{22}-1/4)$ has expectation $1/48$. Adding the selected conflicting raw factor $M_{11}$ gives $-1/192$. This verifies both signs and conditioning normalizations directly.

## 4. Handoff

No repair is requested. Record SG-E4-A as reviewed and proved for its exact $b=1$ maximum, and SG-E4-B as reviewed and proved as an upper bound for $b\ge1$. Historical priority and graph-level consequences remain outside this review. The separately prepared integration candidate requires its own comparison after this packet is frozen.
