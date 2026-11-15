# An attainable envelope with one inconsistent centered singleton

Revision 1. Written 15 November 2026 UTC. Status: proved in this note, awaiting independent review. This extends the frozen mixed envelope and leaves that evidence unchanged. Historical priority is not established.

The mechanism is to distinguish one inconsistent centered factor before expanding the other factors. Every surviving selected support either forces that indicator to zero or omits a cell that conflicts with it. In the second case, an exact kernel difference identity exchanges the remaining centered factor for one unused exposure.

## 1. Definitions and theorem

Fix $n\ge2$. Let $\sigma_c$ be independent uniform permutations of $[n]$ and write

\[
M_{cij}=\mathbf1_{\{\sigma_c(i)=j\}},\qquad
X=\prod_{e\in E}(M_e-n^{-1})^{p_e}M_e^{q_e}.
\]

The support $E$ has $a$ distinct colored cells, with $2\le a\le n$. The powers are nonnegative integers with $p_e+q_e\ge1$. A requested cell is consistent if no other requested cell of its color shares its row or column. A centered singleton has $(p_e,q_e)=(1,0)$. Let $h$ and $b$ count the consistent and inconsistent centered singletons, respectively.

Write

\[
P_j(n,s)=j!\,[z^j](1-z)^{n-s}
\exp\left(\frac{nz}{1-z}\right),
\qquad j,s\ge0,\quad j+s\le n.
\tag{1}
\]

This is $D_j(n,s)$ in the frozen mixed proof. The notation $P_j$ avoids confusion with the diagonal factorial factor. Its classical Laguerre identification and positive representation are inherited from that proof, not asserted as new identities here.

**Theorem SG-E4-A.** Suppose $b=1$. Necessarily $0\le h\le a-2$, and

\[
\boxed{
|\mathbb EX|
\le
\frac{n^{-h-1}P_h(n,a-h-1)}{(n)_{a-1}}.
}
\tag{2}
\]

For every $n,a,h$ with $n\ge2$, $2\le a\le n$ and $0\le h\le a-2$, the right side is the exact maximum of $|\mathbb EX|$ among all permitted patterns, powers and independent colors with those $a,h$ and $b=1$.

**Corollary SG-E4-B.** For every $b\ge1$, the same argument gives

\[
\boxed{
|\mathbb EX|
\le
2^{b-1}\frac{n^{-h-1}P_h(n,a-h-1)}{(n)_{a-1}}.
}
\tag{3}
\]

No exact-maximum assertion is made for $b>1$.

## 2. The kernel and its exact difference identity

For $s+j\le n$, define

\[
F_n(s)=\frac{n^s}{(n)_s},\qquad
\mu_j(n,s)=\frac{P_j(n,s)}{(n-s)_j},\qquad
K_{j,s}(n)=F_n(s)\mu_j(n,s).
\tag{4}
\]

The frozen mixed proof establishes the following facts in Sections 2 and 3.

1. If $U$ is a uniform permutation on $n-s$ remaining rows and columns, then

   \[
   \mu_j(n,s)=\mathbb E\prod_{i=1}^j(nU_{ii}-1).
   \]

2. The positive partition representation is

   \[
   P_j(n,s)=\sum_{\pi\in\mathcal P([j])}
   \prod_{B\in\pi}\bigl((|B|-1)n+s\bigr)(|B|-1)!.
   \tag{5}
   \]

3. The kernel $K_{j,s}$ is nonnegative and nondecreasing in $s$. If $j_1+s_1+j_2+s_2\le n$, then

   \[
   K_{j_1,s_1}(n)K_{j_2,s_2}(n)
   \le K_{j_1+j_2,s_1+s_2}(n).
   \tag{6}
   \]

The last assertions also follow directly from (5). Increasing $s$ increases every block weight and the factor $n^s/(n)_{j+s}$. The union of partitions on disjoint labeled sets embeds their product sum into the sum for the union, with every block weight increased to parameter $s_1+s_2$. Finally, $(n)_u(n)_v\ge(n)_{u+v}$ for $u+v\le n$, by comparing the $v$ factors after the first $u$ factors. These observations prove (6) and monotonicity.

**Lemma 2.1.** If $j+s+1\le n$, then

\[
\boxed{K_{j+1,s}(n)=K_{j,s+1}(n)-K_{j,s}(n).}
\tag{7}
\]

In particular,

\[
K_{j+1,s}(n)\le K_{j,s+1}(n).
\tag{8}
\]

**Proof.** In the moment representation, condition on the last requested diagonal indicator. Its probability of being one is $1/(n-s)$. Given that event, the remaining permutation is uniform on $n-s-1$ rows and columns, while the centering parameter remains $n$. Therefore

\[
\mu_{j+1}(n,s)
=\frac{n}{n-s}\mu_j(n,s+1)-\mu_j(n,s).
\]

Multiplying by $F_n(s)$ and using

\[
F_n(s)\frac n{n-s}=F_n(s+1)
\]

proves (7). Nonnegativity of $K_{j,s}$ proves (8). The argument includes $j=0$, where $\mu_0=1$. $\square$

## 3. A bound for each selected support

Choose one inconsistent centered singleton $e_*$ and let $T$ be the set of the $h$ consistent centered singletons. Put

\[
V=E\setminus(T\cup\{e_*\}),\qquad
r=|V|=a-h-1.
\]

Since $e_*$ is inconsistent, it has a conflicting requested neighbor. No such neighbor belongs to $T$, because every member of $T$ is consistent relative to all of $E$. Thus $V$ contains a neighbor of $e_*$, and $r\ge1$. This also proves $h\le a-2$.

For $S\subseteq V$, define

\[
G_S=\mathbb E\left[
(M_{e_*}-n^{-1})
\prod_{e\in T}(M_e-n^{-1})
\prod_{e\in S}M_e
\right].
\]

We claim that every $S$ satisfies

\[
|G_S|\le n^{-h-1-|S|}K_{h,r}(n).
\tag{9}
\]

If $S$ contains a row or column conflict within one color, its indicator product vanishes identically, so $G_S=0$. We may assume $S$ is compatible. Let $s_c$ count its cells of color $c$, and let $h_c$ count the members of $T$ of that color.

First suppose $S$ contains a cell conflicting with $e_*$. Then $M_{e_*}\prod_{e\in S}M_e=0$. Exact conditioning and independence give

\[
G_S=-n^{-h-1-|S|}\prod_cK_{h_c,s_c}(n).
\tag{10}
\]

Repeated application of (6), then monotonicity in the exposure parameter, yields

\[
\prod_cK_{h_c,s_c}(n)
\le K_{h,|S|}(n)\le K_{h,r}(n).
\]

All total indices are at most $h+r=a-1\le n-1$, so the cited domains hold. This proves (9) in this case.

Now suppose $S$ contains no conflicting neighbor of $e_*$. Then $e_*$, $T$ and $S$ are mutually compatible. After conditioning on $S$, the factor at $e_*$ is an additional centered singleton. Also $|S|\le r-1$, because $V$ contains a neighbor that was not selected. If $c_*$ is the color of $e_*$, conditioning gives

\[
G_S=n^{-h-1-|S|}
K_{h_{c_*}+1,s_{c_*}}(n)
\prod_{c\ne c_*}K_{h_c,s_c}(n).
\tag{11}
\]

Merge the color kernels using (6), apply (8), and then increase the exposure parameter to $r$:

\[
K_{h_{c_*}+1,s_{c_*}}(n)
\prod_{c\ne c_*}K_{h_c,s_c}(n)
\le K_{h+1,|S|}(n)
\le K_{h,|S|+1}(n)
\le K_{h,r}(n).
\tag{12}
\]

Here $h+|S|+1\le h+r=a-1$, so the difference identity and every merging step are used within their domains. Equations (11) and (12) prove (9) in the second case.

For completeness, the conditioning factors in (10) and (11) follow from

\[
\frac{1}{(n)_{s_c}}n^{-j_c}\mu_{j_c}(n,s_c)
=n^{-j_c-s_c}K_{j_c,s_c}(n)
\]

for each color. In (10), the extra factor is $-1/n$. In (11), the total number of remaining centered factors is $h+1$.

## 4. Summing arbitrary powers

For $e\in V$, write

\[
(M_e-n^{-1})^{p_e}M_e^{q_e}=c_e+d_eM_e.
\tag{13}
\]

If $q_e\ge1$, then $c_e=0$ and $d_e=(1-1/n)^{p_e}$. If $q_e=0$, then

\[
c_e=(-1/n)^{p_e},\qquad
d_e=(1-1/n)^{p_e}-(-1/n)^{p_e}\ge0.
\]

Define $W_e=d_e+n|c_e|$. The bounds used in the frozen mixed proof are

\[
W_e=2\quad\text{for a centered singleton},
\qquad
W_e\le1\quad\text{for every other permitted factor}.
\tag{14}
\]

Here is the verification for arbitrary powers. When $q_e\ge1$, $W_e\le1$ immediately. For a repeated centered power, put $x=1-1/n$ and $y=1/n$. If $p\ge2$ is even, then

\[
W_e=x^p+(n-1)y^p\le x^2+(n-1)y^2=1-1/n.
\]

If $p\ge3$ is odd, then

\[
W_e=x^p+(n+1)y^p\le x^3+(n+1)y^3
=1-3/n+4/n^2\le1-1/n.
\]

The last inequality uses $n\ge2$. The remaining case $p=1,q=0$ gives $W_e=2$.

Expand (13) over all subsets $S\subseteq V$. By (9),

\[
\begin{aligned}
|\mathbb EX|
&\le\sum_{S\subseteq V}
\left(\prod_{e\in S}d_e\right)
\left(\prod_{e\in V\setminus S}|c_e|\right)
n^{-h-1-|S|}K_{h,r}(n)\\
&=n^{-a}K_{h,r}(n)\prod_{e\in V}(d_e+n|c_e|).
\end{aligned}
\tag{15}
\]

Exactly $b-1$ of the cells in $V$ are inconsistent centered singletons. No consistent centered singleton remains there. Thus (14) bounds the product by $2^{b-1}$. Since

\[
n^{-a}K_{h,r}(n)
=\frac{n^{-h-1}P_h(n,r)}{(n)_{h+r}}
=\frac{n^{-h-1}P_h(n,a-h-1)}{(n)_{a-1}},
\]

equation (15) proves (3), including (2) when $b=1$.

The earlier mixed envelope is $2^b n^{-a}K_{h,r+1}(n)$. Monotonicity of $K$ shows that (3) is at most half that bound. This is a comparison of two bounds, not a claim of optimality for $b>1$.

## 5. Exact attainment when $b=1$

Fix $2\le a\le n$ and $0\le h\le a-2$, and put $r=a-h-1\ge1$. Use one color. Take the distinguished cell

\[
e_*=(1,a),
\]

the $r$ raw diagonal cells $(i,i)$ for $1\le i\le r$, and the $h$ centered diagonal cells $(i,i)$ for $r+1\le i\le a-1$. All columns lie in $[n]$, including at $a=n$.

The distinguished cell conflicts with the raw cell $(1,1)$ and with no centered diagonal cell. Every centered diagonal cell is consistent. Consequently the support has exactly the prescribed $a,h$ and $b=1$.

On the event that all raw diagonal cells equal one, $M_{e_*}=0$. The raw event has probability $1/(n)_r$, and the conditional centered moment is $n^{-h}\mu_h(n,r)$. Therefore

\[
\mathbb EX
=-\frac{n^{-h-1}\mu_h(n,r)}{(n)_r}
=-\frac{n^{-h-1}P_h(n,r)}{(n)_{a-1}}.
\tag{16}
\]

This attains (2) in absolute value. It proves the exact-maximum assertion for every admissible triple. $\square$

## 6. Dependencies and scope

The only earlier mathematical packet used is `../mixed/sharp-mixed-envelope-v1.md`, SHA256 `878a139aee3caf6040debcc0f9b476e5fa0dd283c70c2a75a48ceaaea38d6b4d`. Equations (4) through (6) and (14) were already proved there. The new argument is the uniform selected-support estimate (9), using the missing conflicting neighbor and the exact difference identity (7). The formulas for the affine weights and the color merger are reproduced to make the extension reviewable.

The theorem concerns exactly one inconsistent centered singleton, not exactly one pair of conflicting requested cells. The distinguished singleton may have several conflicting neighbors. The proof also establishes the stated general corollary with $b\ge1$. No sharpness claim beyond $b=1$, no improvement of the spectral application, and no historical-priority conclusion is part of this packet.

Finite exact checks are recorded separately. They are not premises of the proof.
