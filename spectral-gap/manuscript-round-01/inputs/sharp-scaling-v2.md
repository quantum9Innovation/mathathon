# The cubic scale for centered permutation moments is necessary

Frozen revision: 2. Revision 1 is preserved. Mathematical status: proved below. The integrator independently reconstructed the proof of revision 1 with no gap found. This revision adds the bounded-comparability corollary and makes the attribution of the normalized recurrences explicit. These additions have not yet received a separate review.

## Source and exact question

Collins and Nagatsu, *Weingarten calculus for centered random permutation matrices*, Algebraic Combinatorics 9(2) (2026), 465 to 479, [published PDF](https://alco.centre-mersenne.org/item/10.5802/alco.480.pdf), Proposition 3.3 and Remark 3.4. The remark remains in the final published paper on page 473. It asks whether the cubic moment-order scale used for the leading asymptotic is optimal.

Published PDF SHA-256: `c5b124655a495c03017b3866542ebd1f3289921cc4ed053244cc885cb8db017e`.

The corresponding preprint is [arXiv:2503.18453v1](https://arxiv.org/abs/2503.18453v1), with recurrence (3.8). The final published recurrence is equation (16), page 472. Preprint PDF SHA-256: `078807c292cbb71ecda6b6944fde30fcb3deb8aee764d974b911592b34c6954c`.

## 1. Precise theorem

Let $M$ be the matrix of a uniform permutation of $[N]$. For $0\le k\le N$, define

$$a_k(N)=\mathbb E\prod_{i=1}^k(M_{ii}-1/N).$$

For $k\ge2$, use the leading terms from Collins and Nagatsu:

$$\widetilde a_{2m}(N)=(2m-1)!!\,N^{-3m},\qquad m\ge1,$$

$$\widetilde a_{2m+1}(N)=\frac{4m}{3}(2m+1)!!\,N^{-3m-2},\qquad m\ge1.$$

Put $R_k(N)=a_k(N)/\widetilde a_k(N)$ for $k\ge2$. Then, for every $2\le k\le N$,

$$\boxed{R_k(N)-1\ge\frac{2k^3}{27N}.}\tag{S1}$$

More precisely,

$$R_{2m}(N)-1\ge\frac{m(16m^2-3m-4)}{9N},\tag{S2}$$

and

$$R_{2m+1}(N)-1\ge
\frac{80m^3+195m^2+124m+6}{135N}.\tag{S3}$$

For $2k\le N$, an elementary upper bound is

$$\boxed{R_k(N)\le\exp(3k^3/N).}\tag{S4}$$

Consequently, for any integer sequence $2\le k_N\le N$ as $N\to\infty$,

$$\boxed{\frac{a_{k_N}(N)}{\widetilde a_{k_N}(N)}\longrightarrow1
\quad\Longleftrightarrow\quad\frac{k_N^3}{N}\longrightarrow0.}\tag{S5}$$

This characterizes the scale for relative accuracy of the specific leading terms above. It does not assert that all useful upper bounds on centered moments fail outside that scale.

The same inequalities also show that

$$\boxed{R_{k_N}(N)=O(1)
\quad\Longleftrightarrow\quad k_N^3/N=O(1).}\tag{S5a}$$

Since $R_k\ge1$, this is bounded two-sided comparability of $a_k$ and its leading term. If $k_N^3/N$ stays bounded, then $k_N=O(N^{1/3})$, so (S4) applies eventually. The converse follows from (S1). Thus the theorem also covers the fixed-constant interpretation of the scaling question.

## 2. The known positive recurrence

The row sums of $M-I_{\rm all}/N$ are zero, where $I_{\rm all}$ is the all-ones matrix. Summing the last row against the first $k-1$ centered diagonal entries gives two kinds of terms. There are $N-k+1$ terms involving a new column, each equal to $a_k$. The other $k-1$ terms share a column with a previous diagonal entry.

For two different cells $u,v$ in one column, $M_uM_v=0$, and therefore

$$ (M_u-1/N)(M_v-1/N)
=-\frac1N(M_u-1/N)-\frac1N(M_v-1/N)-\frac1{N^2}.$$

Relabeling rows makes the two resulting shorter moments equal. Thus

$$a_k=
\frac{2(k-1)}{N(N-k+1)}a_{k-1}
+\frac{k-1}{N^2(N-k+1)}a_{k-2}.\tag{S6}$$

This is Collins and Nagatsu's recurrence, reproduced here for a self-contained argument. We have $a_0=1$, $a_1=0$, and all $a_k>0$ for $2\le k\le N$.

## 3. Normalize before estimating

Write $E_k=R_k-1$. The normalized error recurrences below already appear in the proof of Collins and Nagatsu's Proposition 3.3, page 472 of the published paper. Direct substitution of the two leading terms into (S6) reproduces, for $m\ge2$,

$$\begin{aligned}
E_{2m}={}&\frac{N}{N-2m+1}E_{2m-2}\\
&+\frac{4(2m-1)(2m-2)}{3(N-2m+1)}E_{2m-1}\\
&+\frac{(2m-1)(8m-5)}{3(N-2m+1)}.
\end{aligned}\tag{S7}$$

For $m\ge1$, with the term involving $E_1$ omitted at $m=1$,

$$\begin{aligned}
E_{2m+1}={}&\frac{3N}{(N-2m)(2m+1)}E_{2m}\\
&+\frac{(2m-2)N}{(N-2m)(2m+1)}E_{2m-1}\\
&+\frac{2m}{N-2m}.
\end{aligned}\tag{S8}$$

The initial value is $E_2=1/(N-1)$. Every coefficient in these formulas is nonnegative. Induction gives $E_k\ge0$ for all $2\le k\le N$.

## 4. The even lower bound

Since the second term of (S7) is nonnegative, its first coefficient is at least one, and $N-2m+1\le N$,

$$E_{2m}\ge E_{2m-2}
+\frac{(2m-1)(8m-5)}{3N}.$$

The same inequality at $m=1$ means $E_2\ge1/N$, with $E_0=0$ used only for this summation. Hence

$$\begin{aligned}
E_{2m}
&\ge\frac1N\sum_{j=1}^m\frac{(2j-1)(8j-5)}3\\
&=\frac{m(16m^2-3m-4)}{9N}.
\end{aligned}$$

This is (S2). The polynomial is at least $(2m)^3/8$ for $m\ge1$, since

$$\frac{m(16m^2-3m-4)}9-m^3
=\frac{m(m-1)(7m+4)}9\ge0.$$

## 5. The odd lower bound

Let

$$C_{m even}(m)=\frac{m(16m^2-3m-4)}9,$$

$$C_{m odd}(m)=\frac{80m^3+195m^2+124m+6}{135}.$$

These polynomials satisfy $C_{m odd}(1)=3$ and the exact identity

$$C_{m odd}(m)=
\frac{3C_{m even}(m)+(2m-2)C_{m odd}(m-1)}{2m+1}+2m.\tag{S9}$$

From (S8), using $N/(N-2m)\ge1$, we have

$$E_{2m+1}\ge
\frac{3E_{2m}+(2m-2)E_{2m-1}}{2m+1}+\frac{2m}{N}.$$

Together with the even lower bound and (S9), this proves (S3) inductively. The base $m=1$ follows from $E_3\ge E_2+2/N\ge3/N$.

Finally,

$$C_{m odd}(m)-\frac{2(2m+1)^3}{27}
=\frac{75m^2+64m-4}{135}>0\qquad(m\ge1).$$

Combining this with the even bound proves (S1).

## 6. A self-contained upper bound

For this section assume $2k\le N$. Write (S7) and (S8) as recurrences for $R_j$ rather than $E_j$. For even $j=2m$, the sum of the two coefficients is

$$1+\frac{(2m-1)(8m-5)}{3(N-2m+1)}
\le1+\frac{3j^2}{N}.$$

For odd $j=2m+1$, the coefficient sum is

$$\frac{N}{N-2m}\le1+\frac{3j^2}{N}.$$

The denominator bound uses $N-j+1\ge N/2$. The same estimate holds for the initial ratio $R_2=N/(N-1)$. Since the coefficients are nonnegative,

$$\max(1,R_2,\ldots,R_k)
\le\prod_{j=2}^k\left(1+\frac{3j^2}{N}\right)
\le\exp\left(\frac3N\sum_{j=2}^k j^2\right)
\le\exp(3k^3/N).$$

This proves (S4). Necessity in (S5) follows from (S1). For sufficiency, $k_N^3/N\to0$ implies $2k_N\le N$ eventually, and (S4) then gives $R_{k_N}\to1$.

## 7. What this contributes

The moment recurrence, normalized error recurrences, and leading terms are prior results. The argument above supplies a positive, explicit lower bound that forces the cubic scale. The new inference is to retain the positive inhomogeneous term of the normalized recurrence and sum it, rather than estimate its absolute size from above.

At $k$ of order $N^{1/3}$, the relative error stays bounded away from zero by (S1). If $k^3/N\to\infty$, the ratio diverges by the same bound. These statements directly address the relative-accuracy interpretation of Remark 3.4.

No critical-scale limit is claimed in this revision. No comparison with every later citation has been completed. Exact finite checks and independent review remain separate evidence records.
