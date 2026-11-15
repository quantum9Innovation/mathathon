# Positive partitions and the square-root transition

Frozen revision: 1. Task SG-M3. Written November 14, 2026 Pacific.

Mathematical status: proved by the arguments below, awaiting independent review. The two principal claims are EXT-A, a finite relative comparison on a wider window, and EXT-B, the first correction at its square-root boundary. They are separately auditable. No historical priority claim is made.

## 1. Inputs, attribution and precise claims

Let $M$ be a uniform permutation matrix of size $N$. For $0\le k\le N$, set

$$
a_k(N)=\mathbb E\prod_{i=1}^k(M_{ii}-1/N).
$$

The empty product is one. For $m\ge1$, use the known leading terms

$$
\widetilde a_{2m}(N)=(2m-1)!!N^{-3m},
\qquad
\widetilde a_{2m+1}(N)=\frac{4m}{3}(2m+1)!!N^{-3m-2}.
\tag{1}
$$

Write $R_k=a_k/\widetilde a_k$ for $k\ge2$. The leading terms and the recurrence used below are due to Collins and Nagatsu, *Weingarten calculus for centered random permutation matrices*, Algebraic Combinatorics 9(2) (2026), Proposition 3.3. Their Remark 3.5 identifies the moment with a terminating confluent hypergeometric function. The positive generating function below is a classical Laguerre reformulation of that identity, derived explicitly here rather than claimed as a new special-function identity. The source investigator is independently verifying the attribution and neighboring asymptotic literature.

For each $k\ge2$, define

$$
m=\lfloor k/2\rfloor,\qquad K=2m,\qquad
\lambda=\frac23\sqrt{K^3/N},
\qquad
H_k(N)=
\begin{cases}
\cosh\lambda,&k\text{ even},\\
\sinh\lambda/\lambda,&k\text{ odd}.
\end{cases}
\tag{2}
$$

The distinction between $K=k$ and $K=k-1$ is intentional. It agrees exactly with the pair and triple counting below.

**EXT-A, finite relative comparison.** For integers $N,k$ with $2\le k\le N/4$,

$$
\boxed{
\left(1-\frac{4k^2}{3N}\right)H_k(N)
\le R_k(N)
\le \exp(4k^2/N)H_k(N).
}
\tag{3}
$$

The lower bound remains valid when its displayed factor is negative. In the more informative range $4k^2\le N$,

$$
\boxed{
-\frac{2k^2}{N}
\le\log\frac{R_k(N)}{H_k(N)}
\le\frac{4k^2}{N}.
}
\tag{4}
$$

Consequently, $R_k/H_k\to1$ for every sequence $2\le k=k_N=o(\sqrt N)$. The cubic parameter $k^3/N$ can tend to infinity. This is a relative extension of the bounded-critical-parameter statement in the frozen input `critical-scale-v1.md`.

**EXT-B, square-root boundary.** If $2\le k=k_N\le N$ and $k^2/N\to d\in(0,\infty)$, then

$$
\boxed{\frac{R_k(N)}{H_k(N)}\longrightarrow e^{d/4}.}
\tag{5}
$$

The same limit is one when $d=0$, by EXT-A. Both parities have the same correction after their respective hyperbolic normalizations. In particular, uncorrected relative hyperbolic accuracy does not extend to a positive square-root scale.

An equivalent useful uniform consequence is that, for each fixed $C>0$,

$$
\boxed{
\sup_{2\le k\le C\sqrt N}
\left|
\frac{R_k(N)}{\exp(k^2/(4N))H_k(N)}-1
\right|\longrightarrow0.
}
\tag{6}
$$

The supremum is over integers, and all its moments are defined for sufficiently large $N$. No convergence rate for (5) or (6) is asserted here. No result for unbounded $k/\sqrt N$ is asserted.

## 2. Exact positive representation

Here $(N)_k=N(N-1)\cdots(N-k+1)$ denotes a falling factorial. Put

$$
Q_k(N)=(N)_kN^ka_k(N),\qquad Q_0=1,\qquad Q_1=0.
$$

The source recurrence, reproduced in the frozen inputs, is

$$
(N-k+1)a_k
=\frac{2(k-1)}{N}a_{k-1}
+\frac{k-1}{N^2}a_{k-2}.
$$

Clearing the denominators gives

$$
Q_k=2(k-1)Q_{k-1}+(k-1)(N-k+2)Q_{k-2}.
\tag{7}
$$

To derive a formal generating function, extend the polynomial recurrence (7) to every nonnegative $k$. This extension is only an algebraic convenience. It does not define additional permutation moments beyond $k=N$. With

$$
F_N(z)=\sum_{k\ge0}Q_k(N)\frac{z^k}{k!},
$$

equation (7) gives

$$
(1-z)^2F_N'(z)=NzF_N(z),\qquad F_N(0)=1.
$$

Therefore

$$
\boxed{
F_N(z)=\exp\left(N\left[\frac{z}{1-z}+\log(1-z)\right]\right)
=\exp\left(N\sum_{j\ge2}\frac{j-1}{j}z^j\right).
}
\tag{8}
$$

This has the equivalent exact coefficient formula

$$
\boxed{
Q_k(N)=k!
\sum_{\substack{c_2,c_3,\ldots\ge0\\\sum_{j\ge2}jc_j=k}}
\prod_{j\ge2}\frac{(N(j-1)/j)^{c_j}}{c_j!}.
}
\tag{9}
$$

Thus $Q_k$ counts labeled set partitions with no singleton blocks, where a block of size $j$ carries weight $N(j-1)(j-1)!$. Every term is nonnegative. The factors for a pair and a triple are respectively $N$ and $4N$.

For comparison with the classical notation, the Laguerre generating function

$$
\sum_{k\ge0}L_k^{(\alpha)}(x)z^k
=(1-z)^{-\alpha-1}\exp\left(-\frac{xz}{1-z}\right)
$$

at $\alpha=-N-1$ and $x=-N$ gives $Q_k=k!L_k^{(-N-1)}(-N)$. This is the promised derivation of the attribution, not a dependence on an unproved asymptotic formula.

## 3. Normalize by pairs and one triple

Write

$$
D_k=\frac{N^k}{(N)_k},\qquad
L_{2m}=(2m-1)!!N^m,\qquad
L_{2m+1}=\frac{4m}{3}(2m+1)!!N^m.
$$

Then, exactly,

$$
R_k=D_k\frac{Q_k}{L_k}.
\tag{10}
$$

The polynomial $L_{2m}$ is the contribution of partitions consisting only of pairs. The polynomial $L_{2m+1}$ is the contribution of partitions consisting of one triple and $m-1$ pairs. Direct counting gives the odd coefficient

$$
\binom{2m+1}{3}4(2m-3)!!
=\frac{4m}{3}(2m+1)!!.
$$

For nonpair blocks with counts $c_j$, $j\ge3$, write

$$
S=\sum_{j\ge3}jc_j,\qquad
x=\sqrt{K/N},\qquad
\lambda_j=N\frac{j-1}{j}x^j.
\tag{11}
$$

In particular, $\lambda_3=\lambda$ from (2). For an even order, $S$ must be even. Its normalized contribution in $Q_k/L_k$ is

$$
\frac{(m)_{S/2}}{m^{S/2}}
\prod_{j\ge3}\frac{\lambda_j^{c_j}}{c_j!},
\qquad S\le2m.
\tag{12}
$$

For an odd order, $S$ must be odd and at least three. Its normalized contribution is

$$
\frac{(m-1)_{(S-3)/2}}{m^{(S-3)/2}}
\frac1\lambda
\prod_{j\ge3}\frac{\lambda_j^{c_j}}{c_j!},
\qquad S\le2m+1.
\tag{13}
$$

Equations (12) and (13) follow by cancelling the pair factorial in (9) against the pair factorial in $L_k$. A falling factorial with too many factors is assigned value zero. All resulting availability factors lie in $[0,1]$.

## 4. EXT-A upper bound

Assume $2\le k\le N/4$. Thus $0<x\le1/2$. Define

$$
A=\sum_{\substack{j\ge4\\j\text{ even}}}\lambda_j,
\qquad
B=\sum_{\substack{j\ge3\\j\text{ odd}}}\lambda_j.
$$

Remove the availability factors and the restriction $S\le k$ from (12) and (13). The parity projection of the exponential series gives

$$
\frac{Q_{2m}}{L_{2m}}\le e^A\cosh B,
\qquad
\frac{Q_{2m+1}}{L_{2m+1}}\le e^A\frac{\sinh B}{\lambda}.
\tag{14}
$$

The total weight beyond triples satisfies

$$
A+B-\lambda
\le N\sum_{j\ge4}x^j
=\frac{K^2}{N(1-x)}
\le\frac{2K^2}{N}.
\tag{15}
$$

Also,

$$
\frac{B}{\lambda}
\le1+\frac32\frac{x^2}{1-x^2}
\le1+\frac{2K}{N}
\le\exp(K^2/N),
\tag{16}
$$

where the last inequality uses $K\ge2$.

For $t>0$, the logarithmic derivatives of $\cosh t$ and $\sinh(t)/t$ are respectively $\tanh t$ and $\coth t-1/t$. Both lie in $[0,1]$. For the second upper bound, $e^{2t}-1\ge2t$ gives $\coth t\le1+1/t$. Therefore (14) through (16) imply

$$
\frac{Q_k}{L_k}\le\exp(3K^2/N)H_k.
\tag{17}
$$

The odd case uses $\sinh B/\lambda=(B/\lambda)(\sinh B/B)$. The even case needs only the smaller exponential factor from (15).

Finally,

$$
\log D_k
=\sum_{r=0}^{k-1}-\log(1-r/N)
\le\frac{k(k-1)}{2(N-k+1)}
\le\frac{k^2}{N}.
\tag{18}
$$

Here $-\log(1-u)\le u/(1-u)$, and $k\le N/4$. Equations (10), (17), and (18) prove the upper half of (3).

## 5. EXT-A lower bound

Keep only pair and triple partitions in (9). For even $k=2m$, the number of triples is $J=2\ell$, and their contribution is

$$
\frac{Q_{2m}}{L_{2m}}
\ge\sum_{\ell\ge0}\frac{\lambda^{2\ell}}{(2\ell)!}
\frac{(m)_{3\ell}}{m^{3\ell}}.
\tag{19}
$$

For an integer $s\ge0$, the product inequality $\prod_i(1-u_i)\ge1-\sum_i u_i$, valid for $u_i\in[0,1]$, gives

$$
\frac{(m)_s}{m^s}\ge1-\frac{s(s-1)}{2m}.
\tag{20}
$$

For $s>m$, the left side is assigned zero and the right side is nonpositive, so the same inequality still holds.

Normalize the weights $\lambda^{J}/J!$ over even $J$ by $\cosh\lambda$. They define a probability distribution with

$$
\mathbb E J=\lambda\tanh\lambda,
\qquad
\mathbb E J^2=\lambda^2+\lambda\tanh\lambda.
$$

Using $s=3J/2$ in (20), the loss in (19) relative to $\cosh\lambda$ is at most

$$
\frac{9\lambda^2+3\lambda\tanh\lambda}{8m}
\le\frac{3\lambda^2}{2m}
=\frac{4K^2}{3N}.
\tag{21}
$$

For odd $k=2m+1$, the number of triples is $J=2\ell+1$, and the corresponding contribution is

$$
\frac{Q_{2m+1}}{L_{2m+1}}
\ge\sum_{\ell\ge0}\frac{\lambda^{2\ell}}{(2\ell+1)!}
\frac{(m-1)_{3\ell}}{m^{3\ell}}.
\tag{22}
$$

The product bound now is

$$
\frac{(m-1)_s}{m^s}\ge1-\frac{s(s+1)}{2m}.
\tag{23}
$$

It remains valid with a zero left side when $s\ge m$. Normalize $\lambda^J/J!$ over odd $J$ by $\sinh\lambda$. Then

$$
\mathbb E J=\lambda\coth\lambda,
\qquad
\mathbb E J^2=\lambda^2+\lambda\coth\lambda.
$$

With $s=3(J-1)/2$, the relative loss in (22) is at most

$$
\frac{9\lambda^2-3\lambda\coth\lambda+3}{8m}
\le\frac{9\lambda^2}{8m}
=\frac{K^2}{N}.
\tag{24}
$$

The inequality uses $\lambda\coth\lambda\ge1$. Since $D_k\ge1$, equations (21) and (24) prove the lower half of (3), replacing $K$ by $k$ and using positivity if the lower factor is negative.

For $0\le u\le1/4$,

$$
\log(1-4u/3)\ge-2u.
$$

This follows by differentiation, with equality at $u=0$ and nonnegative derivative of the difference on that interval. Combining it with (3) proves (4). In particular, EXT-A is a general proof and does not depend on finite numerical checks.

## 6. EXT-B as a Poisson partition calculation

Assume $k^2/N\to d\in(0,\infty)$. Then $K^2/N\to d$, $m\to\infty$, and $x\to0$. Let $(C_j)_{j\ge3}$ be independent Poisson variables of means $\lambda_j$ from (11). Their total mean is finite because $x<1$ for all sufficiently large $N$. Set

$$
\Lambda=\sum_{j\ge3}\lambda_j,
\qquad
S=\sum_{j\ge3}jC_j.
$$

Almost surely only finitely many $C_j$ are nonzero. Define

$$
w_e(s)=\frac{(m)_s}{m^s},\qquad 0\le s\le m,
$$

and

$$
w_o(s)=\frac{(m-1)_s}{m^s},\qquad 0\le s\le m-1.
$$

Assign each function value zero outside its displayed integer range. Then (12) and (13) give the exact expectations

$$
\frac{Q_{2m}}{L_{2m}}
=e^\Lambda\mathbb E\left[\mathbf1_{\{S\text{ even}\}}w_e(S/2)\right],
\tag{25}
$$

and

$$
\frac{Q_{2m+1}}{L_{2m+1}}
=\frac{e^\Lambda}{\lambda}
\mathbb E\left[\mathbf1_{\{S\text{ odd}\}}w_o((S-3)/2)\right].
\tag{26}
$$

Only the correct parity is evaluated in each expression. The event $S=1$ is impossible because every block has size at least three.

### Step B1. Control all block sizes

The triple and four-block means satisfy

$$
\lambda=\frac23\sqrt{K^3/N}\longrightarrow\infty,
\qquad
\lambda_4=\frac{3K^2}{4N}\longrightarrow\frac{3d}{4}.
\tag{27}
$$

Every larger block is controlled together by

$$
\sum_{j\ge5}\lambda_j
\le\frac{Nx^5}{1-x}
=\frac{K^{5/2}}{N^{3/2}(1-x)}\longrightarrow0.
\tag{28}
$$

Hence the probability of any block of size at least five tends to zero. Also $C_3/\lambda\to1$ in probability, by its Poisson variance, and $C_4$ is bounded in probability. In particular,

$$
\Lambda-\lambda\longrightarrow\frac{3d}{4}.
\tag{29}
$$

### Step B2. Quantify the depletion of available pairs

On the event of no blocks of size at least five, the argument of either availability function is

$$
s=\frac32C_3+2C_4+O(1).
$$

The bounded difference is zero in (25) and $-3/2$ in (26). On the parity event it is an integer. Since

$$
\frac{\lambda^2}{m}\longrightarrow\frac{8d}{9},
$$

we have, in probability on those events,

$$
\frac{s^2}{2m}\longrightarrow d,
\qquad
\frac{s}{m}\longrightarrow0,
\qquad
\frac{s^3}{m^2}\longrightarrow0.
\tag{30}
$$

For $s/m\le1/2$, expansion of each factor gives

$$
\log w_e(s)=-\frac{s(s-1)}{2m}+O(s^3/m^2),
$$

$$
\log w_o(s)=-\frac{s(s+1)}{2m}+O(s^3/m^2).
\tag{31}
$$

The constants are absolute. For example, sum the inequality

$$
0\le-\log(1-u)-u\le\frac{u^2}{2(1-u)}
$$

over the relevant integers $r$ with $u=r/m$. Equations (28) through (31) show that each availability factor tends to $e^{-d}$ in probability on its parity event. All factors lie in $[0,1]$, so the error also tends to zero in mean after multiplication by the relevant parity indicator.

### Step B3. Retain the parity exactly

Let $B=\sum_{j\ge3,\ j\text{ odd}}\lambda_j$. The parity generating function of the independent Poisson counts gives

$$
\mathbb P(S\text{ even})=\frac{1+e^{-2B}}2,
\qquad
\mathbb P(S\text{ odd})=\frac{1-e^{-2B}}2.
\tag{32}
$$

Since $B\ge\lambda\to\infty$, both probabilities tend to $1/2$. The mean convergence in Step B2 yields

$$
\mathbb E\left[\mathbf1_{\{S\text{ even}\}}w_e(S/2)\right]
\longrightarrow\tfrac12e^{-d},
$$

$$
\mathbb E\left[\mathbf1_{\{S\text{ odd}\}}w_o((S-3)/2)\right]
\longrightarrow\tfrac12e^{-d}.
\tag{33}
$$

There is no assumption of independence between an availability factor and the parity event. Bounded convergence in mean is what justifies these equations.

### Step B4. Restore the falling-factorial correction

For either parity, $\cosh\lambda\sim e^\lambda/2$ and $\sinh\lambda\sim e^\lambda/2$. Thus (25), (26), (29), and (33) imply

$$
\frac{Q_k/L_k}{H_k}\longrightarrow e^{-d/4}.
\tag{34}
$$

Meanwhile,

$$
\log D_k
=\frac{k(k-1)}{2N}+O(k^3/N^2)
\longrightarrow\frac d2.
\tag{35}
$$

The remainder follows from the same logarithm bound used in Step B2, since $k/N\to0$. Multiplying (34) by $D_k$ through (10) proves (5).

The correction $d/4$ has three separate contributions: $3d/4$ from four-blocks, $-d$ from depletion of pairs by the many triples, and $d/2$ from the falling factorial in the permutation probability.

### Step B5. Derive the uniform bounded square-root statement

If (6) failed for some fixed $C$, there would be a sequence of integer orders $2\le k\le C\sqrt N$ with its error bounded away from zero. Pass to a subsequence on which $k^2/N$ converges to $d\in[0,C^2]$. If $d=0$, (4) gives the claimed convergence. If $d>0$, (5) gives it. Both contradict the selected sequence. This proves (6) without claiming an explicit rate.

## 7. Worked cases and explanatory mechanism

The first polynomials obtained from (9) are

$$
Q_2=N,\quad Q_3=4N,\quad Q_4=3N^2+18N,
$$

$$
Q_5=40N^2+96N,\qquad
Q_6=15N^3+430N^2+600N.
$$

For $Q_6$, the three-pair contribution is $15N^3$. Two triples contribute $160N^2$, one pair and one four-block contribute $270N^2$, and one six-block contributes $600N$. The sum explains the coefficient $430$ and separates the first competing nonpair mechanisms.

At the cubic scale $k^3/N\to c$, triples have a bounded total effective weight. Their parity-conditioned exponential series are $\cosh(2\sqrt c/3)$ and $\sinh(2\sqrt c/3)/(2\sqrt c/3)$. Larger blocks and pair depletion are smaller because $k^2/N\to0$.

In the intermediate regime $N^{1/3}\ll k\ll\sqrt N$, EXT-A still gives relative accuracy. Here the cubic parameter diverges, and

$$
R_k\sim\frac12e^\lambda\quad\text{for even }k,
\qquad
R_k\sim\frac{e^\lambda}{2\lambda}\quad\text{for odd }k.
$$

At the boundary $k\sim\sqrt N$, EXT-B gives $R_k/H_k\to e^{1/4}$. Thus the hyperbolic approximation alone has a nonvanishing relative error there. Including $\exp(k^2/(4N))$ restores uniform relative accuracy for every bounded multiple of $\sqrt N$, by (6).

For example, taking even $k=2\lfloor\sqrt N/2\rfloor$ produces the limiting correction $e^{1/4}$. Taking the neighboring odd order gives the same correction relative to its odd normalization. This is a boundary example for the approximation window, not a counterexample to any frozen input theorem.

## 8. Dependence, checks and remaining scope

Direct mathematical dependencies are the definition of uniform permutation moments, the known recurrence and leading terms, elementary power series, finite set-partition counting, and elementary Poisson mean, variance and parity formulas. EXT-A does not depend on the frozen critical-scale proof. EXT-B depends on the same exact representation and EXT-A only for the zero-boundary case and the uniform corollary.

The proof uses no numerical limit as an inference. `check_extension.py` independently compares exact moment formulas, polynomial recurrence and positive partition coefficients, checks finite normalized bounds numerically, and records square-root examples in `extension-checks-v1.json`. These checks corroborate the implementation and examples only.

No end-to-end formal verification is claimed. Historical priority of the extended relative window and its square-root correction remains under source review. The Laguerre generating function and inverse-gamma interpretation must not be advertised as new identities. No assertion is made beyond bounded $k/\sqrt N$, and no new graph spectral-gap theorem is inferred from these moment asymptotics alone.
