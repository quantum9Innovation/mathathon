# Bounded priority comparison for the two-conflict extremum

Revision 1. Inspected 15 November 2026 UTC. This supplements the frozen additive audit without changing it. The target is MIX2-1 in `../mixed-two-conflict/proof-v1.md`, SHA256 `07c2aa5a4907a309546180835fe47e5a5301f352ed55bbd9e15aaf7dfa41a952`. This is a source-scope assessment, not a second independent proof review. No historical firstness claim is supported.

## Compared claim

For independent uniform permutation colors on $[n]$, take a product over $a$ distinct colored cells with arbitrary nonnegative integer powers of $M_e-1/n$ and $M_e$. Let $h$ count the consistent centered singletons and let $b$ count the inconsistent centered singletons, measured relative to the complete requested support. A centered singleton has exactly one centered factor and no raw factor. Fix

$$
n\ge2,\qquad 2\le a\le n,\qquad 0\le h\le a-2,\qquad b=2,
\qquad r=a-h-2.
$$

With

$$
P_j(n,s)=j![z^j](1-z)^{n-s}\exp\left(\frac{nz}{1-z}\right),
\qquad K_{j,s}=\frac{n^sP_j(n,s)}{(n)_{j+s}},
$$

the claim is the exact maximum

$$
\max |\mathbb EX|=n^{-a}\bigl(2K_{h,r+1}-K_{h,r}\bigr).
$$

The maximum ranges over all permitted supports, multiplicities and independent colors with those counts. It is attained by a single color with two centered cells sharing one row, with all other requested cells mutually compatible and compatible with each cell of the pair. Of those other cells, $h$ are centered singletons and $r$ are raw. Thus the claim is an extremum at fixed counts, not merely evaluation at one already fixed support. The accompanying MIX2-2 bound for $b\ge2$ multiplies this expression by $2^{b-2}$ and asserts no exact maximum when $b>2$.

## Direct classical overlap

The value on the attaining family is an elementary fixed-pattern calculation using the standard matching probabilities. Let $e,f$ share a row or column, and let $Y$ be the product of the $h$ compatible centered factors and $r$ compatible raw factors. Since $M_eM_f=0$,

$$
(M_e-1/n)(M_f-1/n)=n^{-2}-n^{-1}(M_e+M_f).
$$

The compatible-product formula gives $\mathbb EY=n^{-h-r}K_{h,r}$ and $\mathbb E(M_eY)=\mathbb E(M_fY)=n^{-h-r-1}K_{h,r+1}$. Substitution yields

$$
\mathbb E[(M_e-1/n)(M_f-1/n)Y]
=n^{-a}(K_{h,r}-2K_{h,r+1}).
$$

In particular, the covariance $-1/n^2$ at $a=2,h=0$ is elementary. Neither this pair identity nor the classical polynomial identification should be presented as a new phenomenon. What the current theorem additionally proves is that every admissible pattern and every allowed choice of powers and colors is bounded by the attained value.

There is also a closely related published example. Collins and Nagatsu, [*Weingarten calculus for centered random permutation matrices*](https://doi.org/10.5802/alco.480), Remark 7.2, printed page 478, gives

$$
\mathbb E[(M_{11}-1/n)^2(M_{12}-1/n)^2
(M_{13}-1/n)(M_{14}-1/n)]
=2/n^5-5/n^6.
$$

For $n\ge4$, this has $a=4,h=0,b=2$. It is a genuine earlier calculation in the present class, rather than an unrelated example. It is below the asserted maximum $(n+2)/(n^2(n)_3)$. Indeed its positive value is less than $2/n^5<1/n^4$, while $n(n+2)>(n-1)(n-2)$ shows that the maximum exceeds $1/n^4$.

The example can be checked without any asymptotics. Depending on the image of row one, the numerator of its expectation is

$$
\frac{2(n-1)^2-2(n-1)+(n-4)}{n^7}
=\frac{2n-5}{n^6}.
$$

The three terms correspond respectively to columns one or two, columns three or four, and the remaining columns. Exact enumeration at $n=4,5,6$ corroborated these values. This calculation is a source comparison, not evidence for the general extremal theorem.

## What the inspected primary statements provide

| Source and exact location | Comparison with MIX2-1 |
| --- | --- |
| Collins and Nagatsu, Theorem 3.1, equations (9) and (10), printed page 470, Theorem 3.6, equation (17), page 474 | Exact centered moments can be computed from these formulas. Raw factors can be expanded as centered factors plus constants, and independent colors factor. This recovers fixed-pattern values in principle. The inspected statements do not assert the maximum at fixed $a,h,b=2$. |
| Collins and Nagatsu, Lemma 5.1, equations (22) and (23), page 476, and the reduction on page 477 | Reduction of arbitrary powers is a prior ingredient. The required dominance across the selected supports and the color-merging comparison are additional steps in the local proof. |
| Collins and Nagatsu, Remark 7.2, pages 478 and 479 | Supplies the explicit two-singleton example above and discusses cancellation in its Weingarten expansion. It is not an extremal statement. |
| Bordenave and Zhu, [arXiv:2611.07104v1](https://arxiv.org/html/2611.07104v1), Lemma 2.1, equation (2.1), PDF page 7 | At $b=2$ the bound has factor $4C$, a power of $3k/\sqrt n$, and the restriction $k\le\sqrt n$. It does not retain the subtractive kernel term or state attainment over all multiplicities. |
| Han and Niles-Weed, [arXiv:2607.23836v1](https://arxiv.org/html/2607.23836v1), Theorem 1.2, and [arXiv:2408.09341v3](https://arxiv.org/pdf/2408.09341v3), Lemma 5.5 | These are centered-matrix and permanent-coefficient inequalities. The earlier audit's diagonal specializations remain valid. The inspected theorems do not keep the two specified inconsistent cells and do not state this mixed maximum. |
| *A strict four-row permanent inequality and permutation moments*, Theorem 1.1, page 2, Bristiel and Caputo, [arXiv:2109.06009v3](https://arxiv.org/pdf/2109.06009v3), Corollary 1.14, page 8, and Sra's [author version 1](https://suvrit.github.io/papers/gurvits/gurvits-v1.pdf), Theorem 5.1 and Corollary 5.2, page 10 | These control nonnegative products, permanents or matching sums. Their inspected statements do not give the signed fixed-count extremum. Applying them after absolute values discards relevant cancellation. |
| Kim, Kim, Jang and Kwon, [equation (2.22)](https://link.springer.com/article/10.1186/s13660-018-1636-8), page 9 | The identity $P_h(n,s)=(-1)^h d_h^{(n-s-h+1)}(-n)$ applies to both kernel terms. It identifies known polynomials and does not supply an optimization over supports. |

The limitation of direct absolute-value reduction is visible already for two conflicting cells and $n>2$. Their product has value $-(n-1)/n^2$ with probability $2/n$, and $1/n^2$ otherwise. Therefore its expected absolute value is $(3n-4)/n^3$, strictly larger than the absolute expectation $1/n^2$. This does not rule out a different deduction from a general permanent theorem.

## Search and limits

Eight targeted queries were issued on 15 November 2026 UTC:

1. `"permutation" "centered" "two" "inconsistent" moments`
2. `"permutation" "conflicting" "centered" entries moment`
3. `"permutation matrices" "mixed" "sharp" moment bound`
4. `"permutation" "centered" "singleton" "maximum"`
5. `"centered" "permutation" "same row" moment`
6. `"permutation" "two inconsistent" "singleton"`
7. `"permutation" "mixed moments" "attained"`
8. `"Weingarten calculus" "conflict"`

They supplied no additional inspected primary statement of the exact maximum. Secondary hits were not used as theorem evidence. The complete published Collins and Nagatsu Section 5 and Remarks 7.1 and 7.2 were reread from the previously downloaded journal PDF. A direct publisher-page request returned 403, so the local verified copy was used. The remaining comparisons reuse the primary statements inspected in the frozen additive audit. Their access and version limits remain in force. No blocked full-text request or CityU agreement route was repeated.

The supported conclusion is narrow: the inspected sources contain exact fixed-pattern machinery and a close repeated-power example, but no inspected statement asserts the full MIX2-1 extremum. The possible existence of an equivalent published theorem or a short deduction from other literature remains unverified. A suitable description is that the manuscript proves the exact two-conflict maximum by retaining the pair and controlling every selected support. It should continue to credit the polynomial and moment-calculation ingredients and avoid historical firstness language.
