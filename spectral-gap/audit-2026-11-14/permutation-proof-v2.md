# The centered permutation estimate from a row-sum identity

Frozen revision: 2. Mathematical status: proved below, unreviewed. Revision 1 is preserved. This revision uses a simpler recurrence proof and a sharper constant suggested by the integrator.

The zero-depletion recurrence is already in Collins and Nagatsu, [Proposition 3.3 and equation (16)](https://alco.centre-mersenne.org/item/10.5802/alco.480.pdf), published in 2026. The argument below extends the recurrence to a prescribed compatible set, then handles arbitrary mixed products directly.

## 1. Statement

Let $M_{cij}=\mathbf1_{\{\sigma_c(i)=j\}}$ for independent uniform permutations $\sigma_c$ of $[n]$. Let $E$ be a nonempty set of distinct triples $(c,i,j)$, with $a=|E|\le\sqrt n$. Assign integers $p_e,q_e\ge0$ with $p_e+q_e\ge1$ and define

$$P=\prod_{e\in E}(M_e-1/n)^{p_e}M_e^{q_e}.$$

A cell is consistent when no other cell of its color shares its row or column. Let $h$ count consistent cells with $(p_e,q_e)=(1,0)$, and let $b$ count inconsistent cells with $(p_e,q_e)=(1,0)$.

For $a\ge2$, put

$$\beta_{n,a}=\frac{\sqrt{a-1}}{\sqrt n-\sqrt{a-1}}.$$

Then

$$\boxed{|\mathbb E P|\le e\,2^b n^{-a}\beta_{n,a}^{h}
\le e\,2^b n^{-a}\left(2\sqrt{a/n}\right)^h.}\tag{P1}$$

For $a=1$, a centered singleton has expectation zero, and every other allowed product has absolute expectation at most $1/n$.

The first bound also holds for $2\le a\le n$ if its prefactor $e$ is replaced by

$$\exp\left(\frac{a(a-1)}{2(n-a+1)}+\frac an\right).\tag{P2}$$

Thus the restriction $a\le\sqrt n$ is needed to keep the prefactor universally bounded, rather than for the cancellation identity itself.

## 2. Isolate the cancellation

Prescribe a compatible set of $r$ permutation cells to equal one. The remaining permutation has size $N=n-r$. Its entries $U_{ij}$ still have to be centered at $1/n$, because that is the centering in the original product.

Normalize them as

$$Z_{ij}=nU_{ij}-1.$$

Every row sum is now exactly $r$:

$$\sum_{j=1}^N Z_{ij}=n-N=r.$$

For $0\le h\le N$, put

$$\mu_h(n,r)=\mathbb E\prod_{i=1}^h Z_{ii}.$$

By symmetry this is the moment of any $h$ cells with distinct rows and columns. In particular, $\mu_0=1$ and $\mu_1=r/(n-r)$.

Multiply the last row sum by $Z_{11}\cdots Z_{h-1,h-1}$ and take expectations. Of the $N$ possible columns, $N-h+1$ are new and each gives $\mu_h$. Each of the other $h-1$ columns collides with a previous diagonal entry.

If $u,v$ are different cells in the same column, then $U_uU_v=0$, so

$$Z_uZ_v=-Z_u-Z_v-1.$$

The two shorter moments on the right both equal $\mu_{h-1}$ by relabeling rows. Therefore

$$r\mu_{h-1}=(N-h+1)\mu_h
-(h-1)(2\mu_{h-1}+\mu_{h-2}).$$

Equivalently,

$$\boxed{(n-r-h+1)\mu_h
=(r+2h-2)\mu_{h-1}+(h-1)\mu_{h-2}.}\tag{P3}$$

The last term is omitted at $h=1$. Every coefficient is nonnegative, so all $\mu_h$ are nonnegative. This is the cancellation mechanism: the row sum forces the moment of new cells to be paid for by collisions, each of which removes one or two factors.

## 3. Bound the positive recurrence

Assume $r+h\le a\le n$ and $a\ge2$. Put $s=a-1$ and $\beta=\beta_{n,a}$. Its definition gives the exact identity

$$ (n-a+1)\beta^2=2(a-1)\beta+(a-1).\tag{P4}$$

At each order $1\le j\le h$,

$$r+2j-2\le2(a-1),\qquad j-1\le a-1,\qquad
n-r-j+1\ge n-a+1.$$

Consequently (P3) and (P4) give, by induction from $\mu_0=1$,

$$0\le\mu_h(n,r)\le\beta^h.\tag{P5}$$

For the first induction step, (P4) implies $r\le(n-r)\beta$, which bounds $\mu_1$. If $a\le\sqrt n$, this $\beta$ is no larger than $2\sqrt{a/n}$, as can also be checked using the supersolution inequality in revision 1, equation (7).

## 4. Return to prescribed indicators

Let $S$ be a compatible prescribed set, with $r_c$ cells of each color. Let $T$ be the set of good centered singletons, with $h_c$ cells of each color. Its rows and columns avoid every other requested cell in that color.

Conditioning on $M_e=1$ for $e\in S$ has probability $\prod_c(n)_{r_c}^{-1}$. Applying (P5) in each remaining permutation gives

$$\left|\mathbb E\left[\prod_{e\in S}M_e\prod_{e\in T}(M_e-1/n)\right]\right|
\le\beta^h n^{-h-r}\prod_c\frac{n^{r_c}}{(n)_{r_c}},\qquad r=\sum_c r_c.$$

Incompatible prescribed sets contribute zero. We bound the global factorial correction before combining colors:

$$\log\prod_c\frac{n^{r_c}}{(n)_{r_c}}
\le\frac{\sum_c r_c(r_c-1)}{2(n-a+1)}
\le\frac{a(a-1)}{2(n-a+1)}.\tag{P6}$$

Here $-\log(1-x)\le x/(1-x)$ proves the first inequality. When $a^2\le n$, the last expression is less than $1/2$.

## 5. Expand the other cells

For every cell outside $T$, write

$$ (M_e-1/n)^{p_e}M_e^{q_e}=c_e+d_eM_e.$$

If $q_e\ge1$, then $c_e=0$ and $d_e=(1-1/n)^{p_e}\le1$. If $q_e=0$, then

$$c_e=(-1/n)^{p_e},\qquad
d_e=(1-1/n)^{p_e}-(-1/n)^{p_e},\qquad0\le d_e\le1.$$

For an inconsistent centered singleton, $d_e+n|c_e|=2$. For a repeated centered cell, $d_e+n|c_e|\le1+1/n$. All remaining cells have $d_e+n|c_e|\le1$.

Expand only these affine factors, leaving the good singletons together until their cancellation has been evaluated. Each term selects compatible indicators or vanishes. The preceding estimate yields

$$\begin{aligned}
|\mathbb E P|
&\le\exp\left(\frac{a(a-1)}{2(n-a+1)}\right)
n^{-a}\beta^h\prod_{e\notin T}(d_e+n|c_e|)\\
&\le\exp\left(\frac{a(a-1)}{2(n-a+1)}+\frac an\right)
2^b n^{-a}\beta^h.
\end{aligned}$$

This proves (P2). For $a^2\le n$ and $a\ge2$, we have $a/n\le1/2$, so the prefactor is at most $e$, proving (P1). When $a=1$, a direct Bernoulli calculation gives the stated boundary case.

## 6. The exact connection to the requested papers

In [Bordenave Proposition 28](https://arxiv.org/abs/1502.04482v4), orient each base edge once. Every lift-matching factor is an entry of the independent uniform permutation attached to that base edge, after reversing factors where necessary. This leaves distinct-cell counts and multiplicities unchanged. The parameter $h$ here is $a_1$ there, and $a\le k\le\sqrt n$ gives $2\sqrt a\le3k$. Thus (P1) proves the displayed proposition.

In [Brito, Dumitriu, and Harris Lemma 7](https://arxiv.org/abs/1804.07808v6), let $L=nd_1=md_2$ be the number of half-edges on each side. The matching matrix is

$$\begin{pmatrix}0&U\\U^T&0\end{pmatrix},$$

where $U$ is a uniform $L\times L$ permutation matrix. Orient each nonzero entry from left to right and apply (P1) with $n=L$. This identifies the probabilistic input precisely. The subsequent enumeration of circuits and their degree weights is a separate argument.

## 7. Worked cases and limitation

Two disjoint centered cells satisfy

$$\mathbb E[(M_{11}-1/n)(M_{22}-1/n)]
=\frac1{n^2(n-1)}.$$

This is the ordinary two-cell probability scale $n^{-2}$ with one extra factor of order $n^{-1}$ caused by centering. Two conflicting cells instead satisfy

$$\mathbb E[(M_{11}-1/n)(M_{12}-1/n)]=-n^{-2}.$$

They are not counted in $h$, which is essential. For one prescribed cell and two disjoint centered cells, the recurrence gives

$$\mathbb E[M_{11}(M_{22}-1/n)(M_{33}-1/n)]
=\frac{n+2}{n^3(n-1)(n-2)}.$$

This example shows why conditional means cannot simply be declared zero. The depletion parameter $r$ in (P3) accounts for their shift exactly.

The proof is a direct replacement for the product estimate. It does not certify every later circuit-counting step or constitute a literature-wide novelty claim. The known recurrence and source attribution are explicit, while the complete mixed-product estimate and its constants are proved here.
