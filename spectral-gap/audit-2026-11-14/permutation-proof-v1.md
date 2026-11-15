# A direct proof of the centered permutation product estimate

Frozen revision: 1. Mathematical status: proved by the argument below, unreviewed. No novelty claim is made. The source statements are [Bordenave Proposition 28](https://arxiv.org/abs/1502.04482v4) and [Brito, Dumitriu, and Harris Lemma 7](https://arxiv.org/abs/1804.07808v6).

## 1. Statement

Let $(\sigma_c)_{c\in C}$ be independent uniform permutations of $[n]$. Write

$$M_{cij}=\mathbf1_{\{\sigma_c(i)=j\}},\qquad \overline M_{cij}=M_{cij}-\frac1n.$$

Let $E$ be a nonempty finite set of distinct triples $e=(c,i,j)$, with $a=|E|\le\sqrt n$. For each $e$, fix integers $p_e,q_e\ge0$ with $p_e+q_e\ge1$, and put

$$P=\prod_{e\in E}\overline M_e^{p_e}M_e^{q_e}.$$

A cell $e=(c,i,j)$ is consistent if no other cell in $E$ with color $c$ shares its row $i$ or column $j$. Let $T$ be the set of consistent cells with $p_e=1$ and $q_e=0$, and write $h=|T|$. Let $b$ count the inconsistent cells with $p_e=1$ and $q_e=0$.

Then

$$\boxed{\left|\mathbb E P\right|
\le e\,2^b n^{-a}\left(2\sqrt{\frac an}\right)^h.}\tag{1}$$

There is no restriction on the multiplicities beyond the stated conditions. For Bordenave's notation, $a\le k\le\sqrt n$ and $h=a_1$. Since $2\sqrt a\le3k$ for $k\ge1$, (1) implies Proposition 28 with a universal constant. The theorem includes independent base-edge permutations with one global constant.

## 2. The only cancellation calculation

For integers $r,h\ge0$ with $r+h\le a\le\sqrt n$, define

$$\mu_h(n,r)=\sum_{j=0}^h(-1)^{h-j}{h\choose j}
\frac{n^j}{(n-r)_j},\qquad
(N)_j=N(N-1)\cdots(N-j+1).\tag{2}$$

When $n\ge4$ and $a\ge2$, all denominators are positive. We will prove

$$0\le\mu_h(n,r)\le\left(2\sqrt{\frac an}\right)^h.\tag{3}$$

The sum in (2) is a finite difference. Expanding absolute values term by term would discard its essential cancellation.

### 2.1 An elementary integral representation

Set $N=n-r$ and introduce an auxiliary positive variable $X$ with density $x^N e^{-x}/N!$. Repeated integration by parts gives

$$\mathbb E X^{-j}=\frac{(N-j)!}{N!}=\frac1{(N)_j},\qquad 0\le j\le h.$$

Consequently, for $Y=n/X$,

$$\mu_h(n,r)=\mathbb E(Y-1)^h.\tag{4}$$

This is an exact moment representation. It does not assert that the permutation entries are conditionally independent Bernoulli variables given $Y$.

### 2.2 A recurrence that displays the cancellation

Integration by parts in the density above gives

$$\mathbb E[(NY-n)f(Y)]=\mathbb E[Y^2f'(Y)].\tag{5}$$

For completeness, integrate the derivative of

$$e^{-x}x^N f(n/x).$$

The boundary terms vanish for the polynomials used below because $N-h+1\ge n-a+1>0$. Dividing by $N!$ and multiplying by $n$ gives (5).

Taking $f(Y)=(Y-1)^{h-1}$, for $h\ge1$, yields

$$\boxed{(n-r-h+1)\mu_h
=(r+2h-2)\mu_{h-1}+(h-1)\mu_{h-2}.}\tag{6}$$

Here $\mu_0=1$, $\mu_1=r/(n-r)$, and the last term in (6) is zero at $h=1$. Thus every $\mu_h$ is nonnegative.

To prove the upper bound, put $\beta=2\sqrt{a/n}$. Since $n\ge a^2$ and $a\ge2$, we have $\beta\le\sqrt2$. For any $1\le j\le h$,

$$\begin{aligned}
(r+2j-2)\beta+(j-1)
&\le(2\beta+1)(a-1)\\
&<4(a-1)\\
&<4(a-1)+\frac4a\\
&\le(n-a+1)\beta^2\\
&\le(n-r-j+1)\beta^2.
\end{aligned}\tag{7}$$

The fourth line uses

$$\frac{4a(n-a+1)}n
=4a-\frac{4a(a-1)}n
\ge4a-\frac{4(a-1)}a.$$

Equation (7) first gives $\mu_1\le\beta$. Applying (6) inductively then gives $\mu_j\le\beta^j$. This proves (3).

The mechanism is visible in (6). Removing one centered factor costs a depletion term of order $(r+h)/n$. Removing two at once costs order $h/n$. This is why one gains a factor of order $n^{-1/2}$ per isolated singleton, with a moment-order correction.

## 3. Prescribing compatible cells

Suppose $S$ is a compatible set of $r$ cells from one permutation, meaning that all its rows and columns are distinct. Suppose also that $h$ further cells have distinct rows and columns, disjoint from all rows and columns of $S$. Exactly $(n-r)!$ permutations realize the prescribed cells, so

$$\mathbb P(M_e=1\text{ for all }e\in S)=\frac1{(n)_r}.$$

Conditioned on these equalities, the remaining bijection is uniform on $n-r$ rows and columns. Expanding only the $h$ centered factors gives the exact identity

$$\mathbb E\left[\prod_{e\in S}M_e
\prod_{t=1}^h(M_t-1/n)\right]
=\frac{n^{-h}}{(n)_r}\mu_h(n,r).\tag{8}$$

If $S$ is incompatible, its product of indicators is identically zero.

For several independent colors, (8) factors by color. If $r_c$ and $h_c$ are the counts in color $c$, (3) uses the same global $\beta$ for every color, and hence

$$\left|\mathbb E\left[\prod_{e\in S}M_e
\prod_{e\in T}\overline M_e\right]\right|
\le\beta^h n^{-h-r}
\prod_c\frac{n^{r_c}}{(n)_{r_c}},\qquad r=\sum_c r_c.\tag{9}$$

The prefactor is kept before combining colors. Using $-\log(1-x)\le x/(1-x)$, we obtain

$$\begin{aligned}
\log\prod_c\frac{n^{r_c}}{(n)_{r_c}}
&\le\sum_c\frac{r_c(r_c-1)}{2(n-a+1)}\\
&\le\frac{a(a-1)}{2(n-a+1)}\\
&<\frac12.
\end{aligned}\tag{10}$$

The last inequality follows from $a^2\le n$. This avoids any constant that grows with the number of base edges.

## 4. Repeated and conflicting cells

Keep every good singleton $e\in T$ centered. For each remaining cell, the Bernoulli identity $M_e^j=M_e$ for $j\ge1$ gives

$$\overline M_e^{p_e}M_e^{q_e}=c_e+d_eM_e.\tag{11}$$

The coefficients have the following bounds for $n\ge2$.

| Cell type | $c_e$ | $d_e$ | Bound on $d_e+n|c_e|$ |
| --- | --- | --- | --- |
| $q_e\ge1$ | $0$ | $(1-1/n)^{p_e}$ | $1$ |
| $q_e=0$, $p_e=1$ | $-1/n$ | $1$ | $2$ |
| $q_e=0$, $p_e\ge2$ | $(-1/n)^{p_e}$ | $(1-1/n)^{p_e}-(-1/n)^{p_e}$ | $1+1/n$ |

In the last row, $0\le d_e\le1$. For odd $p_e$, this follows from $(1-x)^{p_e}+x^{p_e}\le1$ for $0\le x\le1$. The even case is immediate.

Expand the product of (11) over all $e\notin T$. Each term selects a set $S$ of uncentered indicators and the constant $c_e$ at every omitted cell. The cells in $T$ remain disjoint from all rows and columns in their own colors by consistency. Thus (9) applies to every compatible $S$, and incompatible sets vanish.

Taking absolute values after the singleton cancellation, summing over all subsets, and using (10), we obtain

$$\begin{aligned}
|\mathbb EP|
&\le e^{1/2}\beta^h n^{-a}
\prod_{e\notin T}(d_e+n|c_e|)\\
&\le e^{1/2}\beta^h n^{-a}\,2^b(1+1/n)^a\\
&\le e\,2^b n^{-a}\beta^h.
\end{aligned}\tag{12}$$

Here $a/n\le1/2$ for $n\ge4$. This proves (1) when $a\ge2$. When $a=1$, a centered singleton has zero expectation. Every other allowed cell factor has absolute expectation at most $1/n$, by either $M_e\in\{0,1\}$ or $|\overline M_e|^{p_e}\le|\overline M_e|^2$ for $p_e\ge2$. The case $n=1$ is immediate. Thus all stated cases are covered.

## 5. Three examples

### Two isolated centered cells

For distinct rows and columns,

$$\mathbb E[(M_{11}-1/n)(M_{22}-1/n)]
=\frac1{n(n-1)}-\frac1{n^2}
=\frac1{n^2(n-1)}.$$

The baseline for two specified cells is $n^{-2}$. Centering gains another factor of order $n^{-1}$, which is the contribution of a pair of singletons. At $n=4$, the answer is $1/48$.

### One prescribed cell and two centered cells

For three disjoint cells, $r=1$ and $h=2$. Equation (6) gives

$$\mu_2(n,1)=\frac{n+2}{(n-1)(n-2)}.$$

Therefore

$$\mathbb E[M_{11}(M_{22}-1/n)(M_{33}-1/n)]
=\frac{n+2}{n^3(n-1)(n-2)}.$$

The nonzero conditional mean caused by prescribing $M_{11}=1$ is included exactly. No assertion of conditional centering is needed.

### Why consistency matters

If two requested cells share a row, then

$$\mathbb E[(M_{11}-1/n)(M_{12}-1/n)]=-\frac1{n^2}.$$

There is no extra singleton suppression. Both cells are inconsistent, so $h=0$. Similarly, a repeated centered cell satisfies $\mathbb E(M_{11}-1/n)^2=(n-1)/n^2$, whose scale is $n^{-1}$ rather than $n^{-2}$.

## 6. The biregular input

In the bipartite configuration model, let $N=nd_1=md_2$ be the number of half-edges on either side. The matching matrix has block form

$$M=\begin{pmatrix}0&U\\U^T&0\end{pmatrix},$$

where $U$ is a uniform $N\times N$ permutation matrix. Every nonzero factor can be oriented from the left side to the right side. Reversing a factor preserves the corresponding scalar entry and its multiplicity. Consistency is exactly the condition that its left and right half-edges occur only in this requested pair.

Apply (1) with $n$ replaced by $N$. This proves the mixed centered and uncentered product estimate used as Lemma 7. It is separate from the later counting of circuits and their degree weights. The proof does not by itself repair or certify every subsequent inequality in the biregular paper.

## 7. Evidence and remaining review

The proof above is algebraic and applies for all stated parameters. Planned exact checks concern the recurrence, expansion identity, small permutation ensembles, and the source conditional counterexamples. They can catch errors but cannot replace the general proof.

The new estimate improves the factor in the two cited statements. That comparison is a mathematical statement about those displayed bounds. Whether this proof or sharper estimate is new in the wider literature remains unestablished.
