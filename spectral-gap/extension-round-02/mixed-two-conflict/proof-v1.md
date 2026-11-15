# The exact mixed envelope with two inconsistent centered singletons

Revision 1. November 15, 2026 UTC. Status: written proof complete, awaiting independent review. No historical firstness claim is made.

The extremizer has two centered cells sharing a row and no further conflicts. Keeping both cells unexpanded captures their negative correlation exactly. Other patterns either force at least one of these indicators to zero or leave an unused conflicting neighbor, which the kernel difference identity absorbs.

## 1. Definitions and statement

Let $n\ge2$, let $(\sigma_c)_c$ be independent uniform permutations of $[n]$, and write $M_{cij}=\mathbf1_{\{\sigma_c(i)=j\}}$. For a set $E$ of $a$ distinct colored cells, consider

\[
X=\prod_{e\in E}(M_e-n^{-1})^{p_e}M_e^{q_e},
\qquad p_e,q_e\in\mathbb Z_{\ge0},\qquad p_e+q_e\ge1.
\tag{1}
\]

Assume $2\le a\le n$. A cell is consistent if no other requested cell of the same color shares its row or column. A centered singleton has $(p_e,q_e)=(1,0)$. Let $h$ and $b$ count the consistent and inconsistent centered singletons. Consistency is measured relative to all of $E$, not relative to the selected terms of an expansion.

For $j,s\ge0$ with $j+s\le n$, define

\[
\mathcal P_j(n,s)
=j![z^j]\exp\left(\sum_{\ell\ge1}
\frac{(\ell-1)n+s}{\ell}z^\ell\right),
\qquad
K_{j,s}=\frac{n^s\mathcal P_j(n,s)}{(n)_{j+s}}.
\tag{2}
\]

The empty coefficient is $\mathcal P_0=1$, and $(n)_0=1$.

**Theorem MIX2-1.** Suppose $b=2$ and put $r=a-h-2\ge0$. Then

\[
\boxed{
|\mathbb EX|\le n^{-a}\bigl(2K_{h,r+1}-K_{h,r}\bigr).
}
\tag{3}
\]

For every $n,a,h$ with $n\ge2$, $2\le a\le n$ and $0\le h\le a-2$, the right side is the exact maximum over all permitted patterns, powers and independent colors with those counts and $b=2$. Equivalently, that maximum is

\[
\boxed{
\frac{2n^{-h-1}\mathcal P_h(n,a-h-1)}{(n)_{a-1}}
-\frac{n^{-h-2}\mathcal P_h(n,a-h-2)}{(n)_{a-2}}.
}
\tag{4}
\]

An attaining pattern uses one color, two centered cells sharing a row, and $a-2$ further cells mutually compatible and compatible with both members of the pair. Of the latter cells, $h$ are centered and the others are raw.

The proof also gives the following immediate bound, without claiming sharpness for $b>2$.

**Corollary MIX2-2.** If $b\ge2$, put $r=a-h-2$. Then

\[
|\mathbb EX|\le
2^{b-2}n^{-a}\bigl(2K_{h,r+1}-K_{h,r}\bigr).
\tag{5}
\]

Compared with the previous $b\ge1$ bound, this subtracts the nonnegative term $2^{b-2}n^{-a}K_{h,r}$. The subtraction can vanish, for example when $h=1$ and $r=0$, so no strict improvement is asserted in every admissible case.

## 2. Exact kernel facts

We use three facts from the frozen mixed and one-conflict proofs. Their short derivations are included to fix the domains.

**2.1. Conditioning.** After prescribing $s$ compatible matches of one color, the remaining permutation is uniform on $n-s$ symbols. If $j$ other cells are compatible with each other and with those matches, their centered product, retaining centering by $1/n$, has conditional expectation

\[
n^{-j}\mu_j(n,s),\qquad
\mu_j(n,s)=\frac{\mathcal P_j(n,s)}{(n-s)_j}.
\tag{6}
\]

Including the probability $1/(n)_s$ of the prescribed matches gives

\[
\mathbb E\left[\prod_{e\in S}M_e
\prod_{e\in T}(M_e-n^{-1})\right]
=n^{-j-s}K_{j,s}.
\tag{7}
\]

For several independent colors, the right side becomes $n^{-j-s}\prod_cK_{j_c,s_c}$. The polynomial identity follows either from expanding the indicators in (6) or from the positive partition expression

\[
\mathcal P_j(n,s)
=\sum_{\pi\in\Pi_j}\prod_{B\in\pi}
\bigl((|B|-1)n+s\bigr)(|B|-1)!.
\tag{8}
\]

**2.2. Positivity, monotonicity and merging.** The kernels are nonnegative and nondecreasing in $s$. Whenever the total index is at most $n$,

\[
K_{j_1,s_1}K_{j_2,s_2}
\le K_{j_1+j_2,s_1+s_2}.
\tag{9}
\]

In (8), increasing $s$ increases every block weight. The union of two partitions embeds into the partitions of their union, and increasing both parameters to $s_1+s_2$ increases every weight. Finally, $(n)_u(n)_v\ge(n)_{u+v}$ for $u+v\le n$. These observations prove (9) and the monotonicity of (2).

**2.3. Kernel difference.** For $j+s+1\le n$,

\[
K_{j+1,s}=K_{j,s+1}-K_{j,s}\le K_{j,s+1}.
\tag{10}
\]

Indeed, conditioning the last indicator in $\mu_{j+1}(n,s)$ gives

\[
\mu_{j+1}(n,s)=\frac n{n-s}\mu_j(n,s+1)-\mu_j(n,s).
\]

Multiply by $n^s/(n)_s$ and use nonnegativity. In particular, define

\[
B_{h,r}=K_{h,r}+2K_{h+1,r}
=2K_{h,r+1}-K_{h,r}.
\tag{11}
\]

Its first expression shows that it is nonnegative and nondecreasing in $r$. Also both $K_{h,r}$ and $K_{h+1,r}$ are at most $B_{h,r}$.

## 3. Retain two inconsistent centered cells

Choose two distinct inconsistent centered singletons $e,f$. Let $T$ be the $h$ consistent centered singletons and put

\[
V=E\setminus(T\cup\{e,f\}),\qquad |V|=r=a-h-2.
\]

For each $S\subseteq V$, write $s=|S|$ and

\[
G_S=\mathbb E\left[
(M_e-n^{-1})(M_f-n^{-1})
\prod_{t\in T}(M_t-n^{-1})\prod_{v\in S}M_v
\right].
\tag{12}
\]

We prove the uniform selected-support estimate

\[
\boxed{|G_S|\le n^{-h-2-s}B_{h,r}.}
\tag{13}
\]

If $S$ is incompatible within a color, its indicator product is identically zero, so (13) holds. Assume from now on that $S$ is compatible. Say that a retained cell is forced when some cell of $S$ shares its row or column in its color. On the prescribed event, its indicator is then zero. Every cell of $T$ avoids all of $E$, and hence every conditioning below leaves the cells of $T$ in unused rows and columns.

**3.1. Both retained cells are forced.** Their two centered factors contribute $n^{-2}$. Equation (7), independence and merging give

\[
0\le G_S\le n^{-h-2-s}K_{h,s}
\le n^{-h-2-s}K_{h,r}
\le n^{-h-2-s}B_{h,r}.
\tag{14}
\]

**3.2. Exactly one retained cell is forced.** Its factor contributes $-n^{-1}$. The other retained cell is compatible with $S$ and $T$, so it is one additional centered singleton after conditioning. By (7) and (9),

\[
|G_S|\le n^{-h-2-s}K_{h+1,s}
\le n^{-h-2-s}K_{h+1,r}
\le n^{-h-2-s}B_{h,r}.
\tag{15}
\]

The retained cells may themselves conflict in this case. This does not affect (15), because the forced indicator has already been replaced by zero.

**3.3. Neither is forced and the retained cells conflict with each other.** They have the same color, say $c_0$, and $M_eM_f=0$. For that color, let $j$ count the cells of $T$ and let $s_0$ count the cells of $S$. Since both retained cells avoid $S$ and $T$, either can separately be added as a prescribed match. Expanding only this pair gives the exact expression

\[
G_S=n^{-h-2-s}
\bigl(K_{j,s_0}-2K_{j,s_0+1}\bigr)
\prod_{c\ne c_0}K_{h_c,s_c}.
\tag{16}
\]

The bracket equals $-K_{j,s_0}-2K_{j+1,s_0}$ by (10). It is nonpositive. Merge the two positive terms separately with the other colors, using (9). Then

\[
|G_S|\le n^{-h-2-s}
\bigl(K_{h,s}+2K_{h+1,s}\bigr)
\le n^{-h-2-s}B_{h,r}.
\tag{17}
\]

This is the case that attains the final envelope.

**3.4. Neither is forced and the retained cells are compatible.** This includes different colors. Both retained cells are inconsistent in the original support. A conflicting neighbor of $e$ belongs neither to $T$ nor to $\{f\}$, so it belongs to $V$. It was not selected, since $e$ is unforced. Thus $r\ge1$ and $s\le r-1$. No distinct-neighbor assumption is needed. The two retained cells may share a single omitted conflicting neighbor.

All remaining centered cells are compatible after conditioning, so (7) and (9) give

\[
0\le G_S\le n^{-h-2-s}K_{h+2,s}.
\]

The missing exposure and (10) yield

\[
K_{h+2,s}\le K_{h+1,s+1}
\le K_{h+1,r}\le B_{h,r}.
\tag{18}
\]

This proves (13) in the last case. The four cases cover every compatible selected support.

**3.5. Domain check.** Since $h+r=a-2$, every kernel on the right side of (14) through (18) has total index at most $a-1$. In (18), $h+2+s\le a-1$ because $s\le r-1$. The kernel difference in (16) also has total index at most $h+s+1\le a-1$. Thus all conditioning, merging and difference identities remain inside their stated domains even when $a=n$. If $r=0$, case 3.4 is impossible, as its argument explicitly shows.

## 4. Arbitrary multiplicities and colors

For each $v\in V$, use the Bernoulli identity $M_v^2=M_v$ to write

\[
(M_v-n^{-1})^{p_v}M_v^{q_v}=c_v+d_vM_v.
\tag{19}
\]

If $q_v\ge1$, then $c_v=0$ and $d_v=(1-1/n)^{p_v}\le1$. If $q_v=0$, then

\[
c_v=(-1/n)^{p_v},\qquad
d_v=(1-1/n)^{p_v}-(-1/n)^{p_v}\ge0.
\]

The weights obey

\[
d_v+n|c_v|\le
\begin{cases}
2,&(p_v,q_v)=(1,0),\\
1,&\text{otherwise}.
\end{cases}
\tag{20}
\]

For completeness, if $p\ge2$ is even and $q=0$, this weight is at most

\[
(1-1/n)^2+(n-1)n^{-2}=1-1/n.
\]

If $p\ge3$ is odd, it is at most

\[
(1-1/n)^3+(n+1)n^{-3}
=1-3/n+4/n^2\le1-1/n,
\]

where $n\ge2$. The centered singleton has weight exactly two.

Expand (19) over $S\subseteq V$. Apply (13) before taking the coefficient sum. Since $a=h+2+r$,

\[
\begin{aligned}
|\mathbb EX|
&\le B_{h,r}\sum_{S\subseteq V}
n^{-h-2-|S|}
\prod_{v\in S}d_v\prod_{v\in V\setminus S}|c_v|\\
&=n^{-a}B_{h,r}\prod_{v\in V}(d_v+n|c_v|).
\end{aligned}
\tag{21}
\]

Exactly $b-2$ centered singletons remain in $V$, all inconsistent. Thus (20) proves (5), and it proves (3) when $b=2$. Identity (11) and definition (2) give the polynomial form (4). No restriction on the multiplicities or on the number of independent colors was used.

## 5. Exact attainment and examples

Fix any admissible $n,a,h$ and set $r=a-h-2$. Use one color. Take

\[
e=(1,1),\qquad f=(1,2),
\]

both centered. Add the cells

\[
(i,i+1),\qquad 2\le i\le a-1.
\]

Declare the first $r$ of those cells raw and the last $h$ centered. The added cells have pairwise distinct rows and columns, avoid row one, and avoid columns one and two. Thus precisely $e,f$ are inconsistent centered singletons, and all $h$ other centered cells are consistent. All indices lie in $[n]$, including at $a=n$.

Here the raw factors force the selected set $S$ to be all $r$ raw cells. Case 3.3 has only one color, so (16) is exact with $j=h$ and $s_0=r$:

\[
\mathbb EX=n^{-a}\bigl(K_{h,r}-2K_{h,r+1}\bigr)
=-n^{-a}B_{h,r}.
\tag{22}
\]

This proves attainment for every admissible triple, and hence the exact-maximum assertion. The maximum is positive, since $B_{0,r}\ge1$, $B_{1,0}=2/(n-1)>0$, and the positive partition formula supplies the remaining cases.

**5.1. The smallest case.** If $a=2$ and $h=0$, then $r=0$ and $K_{0,0}=K_{0,1}=1$. Thus the maximum is exactly $1/n^2$. It is attained by any two centered cells sharing a row or column.

**5.2. No consistent centered singletons.** For $h=0$ and any $2\le a\le n$, formula (4) simplifies to

\[
\max|\mathbb EX|=\frac{n+a-2}{n^2(n)_{a-1}}.
\tag{23}
\]

For example, $n=a=3$ gives $2/27$.

**5.3. One consistent centered singleton and no other cells.** For $a=3,h=1,r=0$, $K_{1,0}=0$ and $K_{1,1}=1/(n-1)$. Therefore

\[
\max|\mathbb EX|=\frac{2}{n^3(n-1)}.
\tag{24}
\]

Here the earlier one-conflict general bound was already exact. This illustrates why the improvement in (5) need not be strict.

## 6. Dependencies, checks and limitations

The positive kernel, conditioned moments and merging inequality are taken from `../mixed/sharp-mixed-envelope-v1.md`, SHA256 `878a139aee3caf6040debcc0f9b476e5fa0dd283c70c2a75a48ceaaea38d6b4d`. The kernel difference and affine weight argument also occur in `../mixed-one-conflict/proof-v1.md`, SHA256 `4ed2c2cbe44c453eb401ebbf20eae09b35a9365d018f86abee262fc38dca83f4`. The new conclusion is the exact two-conflict envelope, proved by the selected-support classification in Section 3 and the attaining family in Section 5.

Finite checks are recorded in `checks-v1.json` with their source. They corroborate finite cases only and are not premises of the proof. The result concerns the count of inconsistent centered singletons, not the number of conflicting pairs in the whole support. No classification of all equality patterns, no exact maximum for $b>2$, no improvement of the spectral application, and no historical-priority claim is made.
