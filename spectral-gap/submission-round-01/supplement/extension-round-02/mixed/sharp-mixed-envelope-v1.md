# An attainable envelope for mixed permutation moments

Task SG-E3. Proposed revision 1, written 15 November 2026 UTC. Mathematical status: proved in this note, not independently reviewed. Historical priority is not established. No rate or saddle attempt was read before this revision.

The accepted mixed bound controls every conditioned centered moment by the same geometric factor. Retaining that moment gives an exact extremal answer when there are no inconsistent centered singletons. The proof requires a positive representation and a merging argument across colors. A scalar corollary then gives a simple replacement for the accepted factor that depends on the singleton count.

The conditioned recurrence is taken from the accepted permutation proof revision 3 and frozen manuscript revision 5. Its zero-depletion case is due to Collins and Nagatsu, Proposition 3.3, equation (16). The generating identity below is a specialization of the classical [Laguerre generating function, DLMF 18.12.13](https://dlmf.nist.gov/18.12.E13), not a proposed new identity. A direct derivation is included.

## 1. Definitions and conclusions

Let $n\ge2$. For independent uniform permutations of $[n]$, let

\[
M_{cij}=\mathbf1_{\{\sigma_c(i)=j\}},\qquad
P=\prod_{e\in E}(M_e-n^{-1})^{p_e}M_e^{q_e},
\]

where $E$ contains $a$ distinct cells, $1\le a\le n$, and $p_e,q_e$ are nonnegative integers with $p_e+q_e\ge1$.

A cell is consistent if no other requested cell of its color shares its row or column. Let $h$ count the consistent cells with $(p_e,q_e)=(1,0)$, and let $b$ count the inconsistent cells with those exponents. Put $r=a-h$.

For nonnegative integers $j,s$ with $j+s\le n$, define

\[
D_j(n,s)=
j!\,[z^j]\exp\left(
\sum_{\ell\ge1}\frac{(\ell-1)n+s}{\ell}z^\ell
\right).
\tag{1.1}
\]

This is a finite coefficient formula with nonnegative terms. In particular,

\[
\begin{aligned}
D_0(n,s)&=1,\\
D_1(n,s)&=s,\\
D_2(n,s)&=s^2+s+n,\\
D_3(n,s)&=s(s+1)(s+2)+n(3s+4).
\end{aligned}
\tag{1.2}
\]

**Theorem SG-E3-A, sharp envelope.** Under the stated hypotheses,

\[
\boxed{
|\mathbb EP|
\le
2^b\,\frac{n^{-h}D_h(n,a-h)}{(n)_a}.
}
\tag{1.3}
\]

For every fixed $n,a,h$, the right side with $b=0$ is the exact maximum of $|\mathbb EP|$ over all permitted cell patterns, colors and exponents having these $a,h$ and no inconsistent centered singleton. It is attained by $a$ compatible cells in one color, with $h$ centered singletons and $a-h$ raw factors.

Write

\[
F_n(s)=\frac{n^s}{(n)_s},\qquad
\mu_j(n,s)=\frac{D_j(n,s)}{(n-s)_j}.
\tag{1.4}
\]

Then (1.3) is equivalently

\[
|\mathbb EP|
\le 2^b n^{-a}F_n(a-h)\mu_h(n,a-h).
\tag{1.5}
\]

Thus the factorial factor in the accepted estimate is unchanged. The replacement concerns the singleton factor itself.

**Corollary SG-E3-B, explicit scalar factor.** For $h\ge1$, put

\[
\Gamma_{n,a,h}
=
\frac{a+h-2+
\sqrt{(a+h-2)^2+4(h-1)(n-a+1)}}
{2(n-a+1)}.
\tag{1.6}
\]

Then

\[
|\mathbb EP|
\le
2^b n^{-a}F_n(a-h)\Gamma_{n,a,h}^{\,h}.
\tag{1.7}
\]

For $a\ge2$ this factor is at most

\[
\beta_{n,a}=\frac{\sqrt{a-1}}{\sqrt n-\sqrt{a-1}},
\]

and is strictly smaller when $1\le h<a$. At $h=a$ it equals $\beta_{n,a}$. At $h=1$ it equals $(a-1)/(n-a+1)$, and the scalar bound on the conditioned moment is exact. For $h=0$, use (1.3) directly without defining $\Gamma$.

These are finite statements for the complete mixed product, with no restriction on the multiplicities.

## 2. The positive depleted polynomial

Prescribe $s$ compatible cells of one permutation to equal one. The event has probability $1/(n)_s$. The remaining permutation $U$ is uniform on $N=n-s$ rows and columns.

Retain the original centering and set

\[
\mu_j(n,s)=
\mathbb E\prod_{i=1}^j(nU_{ii}-1),
\qquad 0\le j\le N.
\tag{2.1}
\]

For $N=0$ only the empty moment $\mu_0=1$ is used. Distinct rows and columns can always be relabeled to the diagonal.

Expanding the product in (2.1), every chosen set of $\ell$ indicators has expectation $1/(N)_\ell$. Therefore

\[
\mu_j(n,s)
=\sum_{\ell=0}^j
\binom j\ell(-1)^{j-\ell}\frac{n^\ell}{(N)_\ell}.
\tag{2.2}
\]

Multiplication by $(N)_j/j!$ gives

\[
\frac{(N)_j\mu_j(n,s)}{j!}
=\sum_{\ell=0}^j
\frac{n^\ell}{\ell!}
(-1)^{j-\ell}\binom{N-\ell}{j-\ell}.
\tag{2.3}
\]

The right side is the coefficient of $z^j$ in

\[
(1-z)^N
\exp\left(\frac{nz}{1-z}\right)
=
\exp\left(
\sum_{\ell\ge1}\frac{(\ell-1)n+s}{\ell}z^\ell
\right).
\tag{2.4}
\]

Indeed, expand the exponential on the left in powers of $nz/(1-z)$ and then use the binomial theorem. Only indices at most $j$ contribute. This proves (1.4) and (1.1) throughout the moment range $j+s\le n$.

The coefficient on the right of (2.4) can be defined beyond that range as a formal polynomial. Such coefficients are not interpreted here as permutation moments.

For a set partition $\pi$ of $[j]$, assign to each block $B$ the weight

\[
w_{|B|}(n,s)=
\bigl((|B|-1)n+s\bigr)(|B|-1)!.
\]

Expanding the exponential in (2.4) gives

\[
D_j(n,s)
=\sum_{\pi\in\mathcal P([j])}
\prod_{B\in\pi}w_{|B|}(n,s).
\tag{2.5}
\]

To verify the coefficient count explicitly, if there are $m_\ell$ blocks of size $\ell$, then their number is

\[
\frac{j!}{\prod_\ell(\ell!)^{m_\ell}m_\ell!}.
\]

Multiplication by the block weights gives exactly the corresponding term in (1.1). All terms are nonnegative for $n,s\ge0$.

Formula (2.4) also yields

\[
D_j(n,s)=j!L_j^{(-n+s-1)}(-n)
\]

by the classical Laguerre generating identity. No novelty is claimed for this special-function identification. The proof above makes the subsequent inequalities independent of it.

## 3. Monotonicity and merging

Define

\[
K_{j,s}(n)
=F_n(s)\mu_j(n,s)
=\frac{n^sD_j(n,s)}{(n)_{j+s}},
\qquad j+s\le n.
\tag{3.1}
\]

**Lemma 3.1.** For fixed $n,j$, both $\mu_j(n,s)$ and $K_{j,s}(n)$ are nondecreasing in $s$ over their permitted integer ranges.

**Proof.** Every block weight in (2.5) is nondecreasing in $s$, so $D_j(n,s)$ is nondecreasing. The positive denominator $(n-s)_j$ is nonincreasing in $s$, which proves the claim for $\mu_j$. For $K$, the scalar factor $n^s/(n)_{j+s}$ has successive ratio $n/(n-j-s)\ge1$ whenever the next index is permitted. Combine this with the monotonicity of $D_j$. The case $j=0$ follows from the same argument. $\square$

In particular, among all depletion parameters $0\le s\le a-j$, the exact maximum of the nonnegative moment $\mu_j(n,s)$ is $\mu_j(n,a-j)$.

**Lemma 3.2.** If $j_1+s_1+j_2+s_2\le n$, then

\[
K_{j_1,s_1}(n)K_{j_2,s_2}(n)
\le
K_{j_1+j_2,s_1+s_2}(n).
\tag{3.2}
\]

**Proof.** Put $J=j_1+j_2$ and $S=s_1+s_2$. Take partitions of two disjoint labeled sets of sizes $j_1,j_2$. Their union is a partition of the union with no block meeting both sets. Each block weight at parameter $s_1$ or $s_2$ is at most its weight at parameter $S$. Thus positivity in (2.5) gives

\[
D_{j_1}(n,s_1)D_{j_2}(n,s_2)
\le D_J(n,S).
\tag{3.3}
\]

For $u+v\le n$, the product definitions imply

\[
(n)_u(n)_v\ge(n)_{u+v}.
\]

Apply this with $u=j_1+s_1$, $v=j_2+s_2$ and use (3.1). The powers of $n$ multiply to $n^S$, proving (3.2). $\square$

The merging lemma is what permits a global sharp envelope without a separate constant for each color.

## 4. Proof of the mixed envelope and its attainment

Let $T$ be the $h$ consistent centered singletons. For $e\notin T$, write

\[
(M_e-n^{-1})^{p_e}M_e^{q_e}=c_e+d_eM_e.
\tag{4.1}
\]

If $q_e\ge1$, then $c_e=0$ and $d_e=(1-1/n)^{p_e}\in[0,1]$. If $q_e=0$, then

\[
c_e=(-1/n)^{p_e},
\qquad
d_e=(1-1/n)^{p_e}-(-1/n)^{p_e}\ge0.
\]

Put $W_e=d_e+n|c_e|$. An inconsistent centered singleton has $W_e=2$. Every other cell outside $T$ has $W_e\le1$. Here is the check for a repeated centered cell. Put $x=1-1/n$ and $y=1/n$. For even $p\ge2$,

\[
W_e=x^p+(n-1)y^p
\le x^2+(n-1)y^2=1-1/n.
\]

For odd $p\ge3$,

\[
W_e=x^p+(n+1)y^p
\le x^3+(n+1)y^3
=1-3/n+4/n^2\le1-1/n.
\]

This uses $n\ge2$. Consequently

\[
\prod_{e\notin T}W_e\le2^b.
\tag{4.2}
\]

Expand only the factors outside $T$. A selected set $S$ of indicators that contains a row or column conflict contributes zero. For a compatible selection, let $s_c$ count its cells of color $c$, and let $h_c$ count the members of $T$ of that color. The consistency of $T$ ensures that its cells remain on the unexposed block. Exact compatible conditioning gives

\[
\mathbb E\left[
\prod_{e\in S}M_e
\prod_{e\in T}(M_e-n^{-1})
\right]
=
n^{-h-|S|}\prod_c K_{h_c,s_c}(n).
\tag{4.3}
\]

These quantities are nonnegative by (2.5). Repeated application of Lemma 3.2, followed by Lemma 3.1, gives

\[
\prod_c K_{h_c,s_c}(n)
\le K_{h,|S|}(n)
\le K_{h,a-h}(n).
\tag{4.4}
\]

The total index in each merging step is at most $h+|S|\le a\le n$.

Take absolute values of the affine coefficients and use (4.3) and (4.4). Summing over all subsets, including any incompatible subsets that were previously discarded, yields

\[
\begin{aligned}
|\mathbb EP|
&\le
n^{-a}K_{h,a-h}(n)
\prod_{e\notin T}(d_e+n|c_e|)\\
&\le
2^b n^{-a}K_{h,a-h}(n).
\end{aligned}
\tag{4.5}
\]

The last expression is (1.3). The first line also retains the exact affine weights if they are useful.

For attainment, use one permutation and the $a$ cells $(i,i)$, $1\le i\le a$. Center the first $h$ factors and take the remaining $r=a-h$ factors raw. All these cells are compatible. Conditional on the $r$ raw matches, the remaining $h$ factors have moment $n^{-h}\mu_h(n,r)$. Hence

\[
\mathbb EP
=\frac{n^{-h}\mu_h(n,r)}{(n)_r}
=\frac{n^{-h}D_h(n,r)}{(n)_a}.
\tag{4.6}
\]

This is nonnegative and equals the upper bound for $b=0$. The extremal assertion in Theorem SG-E3-A follows. It includes $h=0$, and also $a=h=1$, when both sides are zero. $\square$

## 5. Proof of the scalar corollary

The accepted depleted recurrence is

\[
(n-s-j+1)\mu_j
=(s+2j-2)\mu_{j-1}+(j-1)\mu_{j-2},
\tag{5.1}
\]

with $\mu_0=1$, $\mu_1=s/(n-s)$, and the last term omitted for $j=1$.

For completeness, multiply the last row sum of $nU-1$, which is $s$, by the preceding diagonal factors. An unused column contributes $\mu_j$. A used column collides with one diagonal cell. For the two conflicting entries,

\[
(nU_u-1)(nU_v-1)=-(nU_u-1)-(nU_v-1)-1.
\]

The resulting expectations are two copies of $-\mu_{j-1}$ and one copy of $-\mu_{j-2}$. There are $j-1$ used columns and $n-s-j+1$ unused ones. This proves (5.1).

Fix $s+h\le n$ and $h\ge1$. Set

\[
d=n-s-h+1,\qquad v=h-1,\qquad A=s+2h-2,
\]

and let

\[
\gamma=
\frac{A+\sqrt{A^2+4vd}}{2d}.
\tag{5.2}
\]

It satisfies $d\gamma^2=A\gamma+v$. If $\gamma=0$, then $s=0$ and $h=1$, and the desired bound $\mu_h=0$ is exact. Otherwise, dividing that identity by $\gamma$ gives $\gamma\ge A/d\ge s/(n-s)$.

Inductively, for $2\le j\le h$, equation (5.1) gives

\[
\mu_j
\le\frac{A\gamma^{j-1}+v\gamma^{j-2}}d
=\gamma^j.
\tag{5.3}
\]

The base cases are $\mu_0=1$ and the preceding bound on $\mu_1$. Thus $\mu_h(n,s)\le\gamma^h$.

Use $s=a-h$ to obtain exactly $\Gamma_{n,a,h}$ and (1.7). When $a\ge2$, the accepted $\beta_{n,a}$ is the positive root of

\[
(n-a+1)x^2=2(a-1)x+(a-1).
\]

The corresponding coefficients for $\Gamma$ are $a+h-2$ and $h-1$. They are no larger, and both are strictly smaller if $h<a$. The positive root of $dx^2=Ax+v$ is nondecreasing in $A,v$, and is strictly increasing in either coefficient when the root is positive. This proves the comparison with $\beta$. For $h=a$ the two equations coincide. For $h=1$ equation (5.2) reduces to $(a-1)/(n-a+1)$, which is the exact depleted first moment. $\square$

## 6. When the improvement changes the full bound

**Proposition SG-E3-C, fixed singleton count.** Fix $h\ge1$. Suppose $n\to\infty$ and $s/\sqrt n\to\rho\ge0$. Then

\[
n^{h/2}\mu_h(n,s)\longrightarrow
G_h(\rho),
\]

where the explicit shifted Gaussian moment polynomial is

\[
G_h(\rho)=
h!\sum_{q=0}^{\lfloor h/2\rfloor}
\frac{\rho^{h-2q}}{(h-2q)!\,2^q q!}.
\tag{6.1}
\]

**Proof.** In the finite coefficient expansion (1.1), a singleton block contributes $s$, of order $\sqrt n$, and a two-element block contributes $n+s$, of order $n$. A block of size $\ell\ge3$ contributes $((\ell-1)n+s)(\ell-1)!=O(n)$. After division by $n^{h/2}$, a term with any such block tends to zero, since that block contributes a factor $O(n^{1-\ell/2})$.

The surviving terms have $h-2q$ singleton blocks and $q$ two-element blocks. Their limits are precisely the terms in (6.1), by the partition count in Section 2. Finally, $(n-s)_h/n^h\to1$, since $h$ is fixed and $s=O(\sqrt n)$. Combine this with (1.4). $\square$

The name in (6.1) is consistent with the coefficient identity

\[
G_h(\rho)=h!\,[z^h]\exp(\rho z+z^2/2).
\]

Take $n=a^2$, $s=a-h$, and let $a\to\infty$ with $h$ fixed. Then

\[
\mu_h(a^2,a-h)
\sim G_h(1)a^{-h},
\qquad
\beta_{a^2,a}^{\,h}\sim a^{-h/2}.
\tag{6.2}
\]

The first equivalence follows from Proposition SG-E3-C and $G_h(1)>0$. The second follows directly from the formula for $\beta$. Therefore the ratio of the sharp envelope (1.5) to the accepted exact-factor bound is

\[
\frac{\mu_h(a^2,a-h)}{\beta_{a^2,a}^{\,h}}
\sim G_h(1)a^{-h/2}.
\tag{6.3}
\]

This compares the full product bounds because their remaining factors are identical. The attaining family (4.6) shows that the improved scale describes actual mixed moments. For $h=1$, the gain is asymptotic to $\sqrt a$.

The explicit scalar factor also captures this improved order. Dividing the numerator and denominator in (1.6) by the appropriate powers of $a$ gives

\[
\Gamma_{a^2,a,h}
\sim\frac{1+\sqrt{4h-3}}{2a}.
\tag{6.4}
\]

Thus the simple corollary has the correct power of $a$ for every fixed $h$, without evaluating the polynomial.

## 7. Obstruction to a uniform improvement of the square-root scale

Let $h=a=2m$ and $s=0$. In (2.5), partitions consisting only of pairs contribute

\[
D_a(n,0)\ge(a-1)!!\,n^{a/2}.
\]

Since $(n)_a\le n^a$, it follows that

\[
\mu_a(n,0)\ge(a-1)!!\,n^{-a/2}.
\tag{7.1}
\]

For each integer $m\ge1$, concavity of the logarithm on each unit interval gives

\[
\sum_{j=1}^m\log(2j-1)
\ge\int_0^m\log(2x)\,dx
=m\log(2m)-m.
\]

The integral at zero is finite. Consequently

\[
(a-1)!!\ge(a/e)^{a/2},
\qquad
\mu_a(n,0)^{1/a}\ge\sqrt{\frac{a}{en}}.
\tag{7.2}
\]

For the all-centered compatible product, this is a lower bound on its singleton factor. Along any even $a\to\infty$ with $a^2\le n$, a bound with a fixed universal prefactor cannot replace the singleton scale by $o(\sqrt{a/n})$. The prefactor contributes only its $a$th root, which tends to one.

There is also a finite-order obstruction to reducing the accepted factor by a universal constant below one while keeping the exact prefactor unchanged. For $a=h=2$,

\[
\mu_2(n,0)=\frac1{n-1},
\qquad
\beta_{n,2}^2=\frac1{(\sqrt n-1)^2},
\]

so $\mu_2(n,0)/\beta_{n,2}^2\to1$. No fixed multiplier smaller than one can replace $\beta$ in every such bound. This does not contradict the improvement when $h<a$.

## 8. Independent colors with separate dimensions

The local envelope gives an immediate but useful corollary. Let color $c$ have permutation dimension $n_c\ge2$, centering $1/n_c$, and local counts $a_c,h_c,b_c$, with $a_c\le n_c$. Colors with no requested cells are omitted. Put $r_c=a_c-h_c$. Independence and Theorem SG-E3-A give

\[
|\mathbb EP|
\le
\prod_c
\left[
2^{b_c}
\frac{n_c^{-h_c}D_{h_c}(n_c,r_c)}
{(n_c)_{a_c}}
\right].
\tag{8.1}
\]

There is no restriction on the sum of the $a_c$. If every $b_c=0$, the bound is attained by choosing compatible cells within each color, with the indicated centered and raw factors. Thus it is also the exact maximum for fixed local counts in that class.

The proof is simply factorization over independent colors followed by (1.3), and the attaining choices can be made simultaneously. This corollary is not presented as a separate method or as an independent novelty claim.

## 9. Contribution and review boundaries

The substantive finite conclusion is the attained extremal envelope (1.3), including its validity across colors. The classical positive polynomial and the accepted affine reduction are ingredients. The scalar factor (1.6) is a usable corollary, and the fixed-count asymptotic explains a regime in which the improvement affects the full estimate.

The obstruction in Section 7 rules out a uniform improvement of the square-root order when the centered singleton count grows with the support size. The new theorem is therefore a refinement by composition of the requested product, not a claim that the accepted scale is uniformly wrong.

The factor $2^b$ is retained from the accepted argument. No optimality claim is made for that factor or for the envelope when $b>0$. The exact maximum statement concerns $b=0$.

This note does not improve spectral graph counting, identify a new spectral-gap theorem, or settle historical priority. The next requested action is independent review of the exact polynomial representation, color merging, and the claimed attainment.

## 10. Finite corroboration

The exact rational checker in check_envelope.py passed 6,541 polynomial identity checks, 5,983 moment monotonicity checks, 5,983 kernel monotonicity checks, and 20,343 merging checks. It also passed 32,389 exhaustive mixed-pattern checks on the stated small spaces, 3,000 sampled mixed-pattern checks, and 110 direct attainment checks.

The full ranges, exponent choices, and limitations are recorded in envelope-checks-v1.json. The product expectations in the mixed-pattern checks were evaluated by enumerating permutations and evaluating the original factors. These finite checks corroborate the theorem and the attaining examples. The general inequalities and asymptotic statements rest on the written proofs above.
