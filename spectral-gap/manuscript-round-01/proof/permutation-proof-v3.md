# A sharp universal prefactor for mixed permutation products

Frozen revision: 3. Written November 14, 2026 Pacific. This proof strengthens the frozen revision 2 in this round's inputs. Revision 2 remains unchanged. The zero-depletion recurrence is due to Collins and Nagatsu, Proposition 3.3 and equation (16) of their published paper. This proof derives the conditioned recurrence, controls mixed products, and sharpens the factorial and universal prefactors. It is proposed for independent review, with priority considered separately.

## 1. The exact-factor theorem

Let $n\ge2$. For independent uniform permutations $\sigma_c$ of $[n]$, write

$$M_{cij}=\mathbf1_{\{\sigma_c(i)=j\}}.$$

Let $E$ be a set of $a$ distinct cells $(c,i,j)$, where $2\le a\le n$. Attach nonnegative integers $p_e,q_e$ with $p_e+q_e\ge1$, and put

$$P=\prod_{e\in E}(M_e-1/n)^{p_e}M_e^{q_e}.$$

Call a cell consistent if no other cell of its color shares its row or its column. Let $h$ be the number of consistent cells with $(p_e,q_e)=(1,0)$, and let $b$ be the number of inconsistent cells with $(p_e,q_e)=(1,0)$. Define

$$\beta=\frac{\sqrt{a-1}}{\sqrt n-\sqrt{a-1}},\qquad
F_n(q)=\frac{n^q}{(n)_q},\qquad F_n(0)=1,$$

where $(n)_q=n(n-1)\cdots(n-q+1)$. Then

$$\boxed{|\mathbb E P|\le 2^b n^{-a}\beta^h F_n(a-h).}\tag{V3.1}$$

For $a^2\le n$, this gives

$$\boxed{|\mathbb E P|\le\sqrt e\,2^b n^{-a}\beta^h
\le\sqrt e\,2^b n^{-a}\bigl(2\sqrt{a/n}\bigr)^h.}\tag{V3.2}$$

The constant $\sqrt e$ is the smallest universal constant in the first inequality of (V3.2) for this class of arbitrary mixed products.

For $a=1$, a centered singleton has expectation zero. Every other permitted one-cell product has expectation of absolute value at most $1/n$. This statement includes $n=1$.

## 2. Exact cancellation after compatible conditioning

First fix one color. Prescribe $r$ compatible cells to equal one. Their rows and columns are distinct, so the event has probability $1/(n)_r$. Conditional on it, the remaining permutation is uniform on $N=n-r$ rows and columns. A good centered cell never meets a prescribed row or column.

On the remaining block define $Z_{ij}=nU_{ij}-1$. Its row sums are $r$, not zero. For $0\le j\le N$, let

$$\mu_j(n,r)=\mathbb E\prod_{i=1}^j Z_{ii}.$$

Set $\mu_0=1$. For $N\ge1$, $\mu_1=r/(n-r)$. When $N=0$, only $\mu_0$ is used.

For $j\ge2$, multiply the row sum of row $j$ by $Z_{11}\cdots Z_{j-1,j-1}$ and take expectation. Each of the $N-j+1$ unused columns contributes $\mu_j$. Each used column collides with exactly one earlier diagonal cell. For distinct cells $u,v$ in the same column,

$$Z_uZ_v=-Z_u-Z_v-1,$$

because $U_uU_v=0$. The remaining factors have distinct rows and columns after either collided factor is removed. Relabeling gives $\mu_{j-1}$ for each one-factor removal and $\mu_{j-2}$ for removing both. Hence

$$\boxed{(n-r-j+1)\mu_j=(r+2j-2)\mu_{j-1}+(j-1)\mu_{j-2}.}\tag{V3.3}$$

All denominators are positive in the stated range, and every numerator coefficient is nonnegative. Therefore all $\mu_j$ are nonnegative.

## 3. A scalar supersolution with its base case

Suppose $r+j\le a\le n$, and write $s=a-1$. Direct algebra gives

$$(n-s)\beta^2=2s\beta+s.\tag{V3.4}$$

For $j\ge1$, necessarily $r\le s$. Thus

$$\frac r{n-r}\le\frac s{n-s}\le\frac{\sqrt s(\sqrt n+\sqrt s)}{n-s}=\beta.$$

This proves the first step explicitly. If $j\ge2$ and the claim holds at the two previous orders, then

$$\begin{aligned}
\mu_j
&\le\frac{2s\beta^{j-1}+s\beta^{j-2}}{n-s}\\
&=\beta^j.
\end{aligned}$$

Here $r+2j-2\le2s$, $j-1\le s$, and $n-r-j+1\ge n-s$. Consequently

$$0\le\mu_j(n,r)\le\beta^j.\tag{V3.5}$$

If $a^2\le n$, then

$$\sqrt{\frac{a-1}{n}}\le\frac{\sqrt{a-1}}a\le\frac12,$$

where the last inequality is equivalent to $(a-2)^2\ge0$. It follows directly that $\beta\le2\sqrt{(a-1)/n}\le2\sqrt{a/n}$.

## 4. Preserve the centered singletons before expanding

Let $T$ be the set of the $h$ good centered singletons. Expand only cells in $E\setminus T$. For any compatible selected set $S\subset E\setminus T$, let $r_c$ and $h_c$ count its cells and the cells of $T$ in color $c$. Independence and (V3.5) give

$$\left|\mathbb E\prod_{e\in S}M_e\prod_{e\in T}(M_e-1/n)\right|
\le n^{-h-|S|}\beta^h\prod_c F_n(r_c).\tag{V3.6}$$

A selected set with a row or column conflict contributes exactly zero. Since $S\subset E\setminus T$, its cardinality is at most $a-h$.

For $r+s\le n$,

$$(n)_r(n)_s\ge(n)_{r+s},$$

because each factor $n-j$ in the second falling factorial is at least the corresponding factor $n-r-j$ in the concatenated falling factorial. Therefore

$$F_n(r)F_n(s)\le F_n(r+s).$$

Also $F_n(q+1)/F_n(q)=n/(n-q)\ge1$. Repeated merging and monotonicity prove

$$\prod_c F_n(r_c)\le F_n(|S|)\le F_n(a-h).\tag{V3.7}$$

This is the exact factorial correction. Good singletons do not consume it.

## 5. The improved affine-factor inequality

For each cell outside $T$, write

$$(M_e-1/n)^{p_e}M_e^{q_e}=c_e+d_eM_e.$$

If $q_e\ge1$, then $c_e=0$ and $d_e=(1-1/n)^{p_e}\le1$. If $q_e=0$, then

$$c_e=(-1/n)^{p_e},\qquad d_e=(1-1/n)^{p_e}-(-1/n)^{p_e}.$$

For $n\ge2$, $0\le d_e\le1$. The affine weight is $d_e+n|c_e|$. A bad centered singleton has weight $2$.

A repeated centered cell has $p_e\ge2$. Put $x=1-1/n$ and $y=1/n$. For even $p_e$,

$$d_e+n|c_e|=x^{p_e}+(n-1)y^{p_e}
\le x^2+(n-1)y^2=1-1/n.$$

For odd $p_e\ge3$,

$$d_e+n|c_e|=x^{p_e}+(n+1)y^{p_e}
\le x^3+(n+1)y^3
=1-3/n+4/n^2\le1-1/n.$$

The last step uses $n\ge2$. Thus every nongood cell other than a bad centered singleton has affine weight at most one. In particular,

$$\prod_{e\notin T}(d_e+n|c_e|)\le2^b.\tag{V3.8}$$

Combining the expansion, (V3.6), and (V3.7), the factor $n^{-h-|S|}$ can be written as $n^{-a}$ times one factor $n$ for each unselected nongood cell. Summing all subsets therefore gives

$$|\mathbb E P|
\le n^{-a}\beta^h F_n(a-h)
\prod_{e\notin T}(d_e+n|c_e|),$$

which proves (V3.1). The proof in fact retains an additional factor $(1-1/n)^\ell$, where $\ell$ is the number of cells with $q_e=0$ and $p_e\ge2$.

## 6. The uniform prefactor and its sharpness

For $0\le q\le n$,

$$\begin{aligned}
\log F_n(q)
&=\sum_{j=0}^{q-1}-\log(1-j/n)\\
&\le\sum_{j=0}^{q-1}\frac j{n-j}\\
&\le\frac{q(q-1)}{2(n-q+1)}.
\end{aligned}\tag{V3.9}$$

At $q=0$ the sum is empty. If $a^2\le n$ and $a\ge2$, this last expression with $q=a$ is strictly below $1/2$. This proves the first inequality in (V3.2).

For sharpness, take $n=a^2$ and $a$ cells with distinct rows and columns, each with $p_e=0,q_e=1$. Then $h=b=0$ and

$$n^a\mathbb E P=F_{a^2}(a).$$

The bounds $x\le-\log(1-x)\le x+x^2/(1-x)$ for $0\le x<1$ give

$$\log F_{a^2}(a)=\frac{a(a-1)}{2a^2}+O(1/a)\longrightarrow\frac12.$$

No smaller universal prefactor can work for these mixed products. The sharpness is mathematical and does not assert literature priority.

## 7. One-cell and source boundaries

For a single Bernoulli cell $M$ with success probability $1/n$, the centered singleton has mean zero. If $q\ge1$, the absolute expectation is $(1-1/n)^p/n\le1/n$. If $q=0$ and $p\ge2$, then $|M-1/n|^p\le|M-1/n|^2$, whose expectation is $(1-1/n)/n$. At $n=1$, direct evaluation gives the same claim.

For Bordenave's Proposition 28, orient each base edge once and regard that edge as a color. Reversing a requested pair transposes its permutation entry without changing its multiplicity or consistency. The source parameters $a_1,b,a$ become $h,b,a$ here. Since $a\le k\le\sqrt n$, (V3.2) implies the source's displayed bound, with the better factor $2\sqrt a$ in place of $3k$ and a universal prefactor $\sqrt e$.

For Brito, Dumitriu, and Harris, Lemma 7, the off-diagonal block of the matching matrix is a uniform permutation of size $L=nd_1=md_2$. Same-side entries, including their centered versions, vanish. Orient every remaining requested pair from left to right and apply the theorem with permutation dimension $L$. This verifies the probabilistic input only. The later circuit enumeration, nonbacktracking estimates, and transfer to simple graphs require their own arguments.

## 8. Evidence and requested integration

The proof is a general written argument. The exact checks in `core-checks-v1.json` independently corroborate the depleted recurrence, the new affine inequality, factorial merging, and the old scaling bounds on their recorded finite ranges. They do not prove the uniform theorem.

Requested next action: independently check this revision, then replace the manuscript's old $e$ prefactor and exponential depletion correction with (V3.1) and (V3.2). Preserve the old input bytes and prior reviews. The source recurrence remains attributed to Collins and Nagatsu.
