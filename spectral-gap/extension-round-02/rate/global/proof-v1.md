# A uniform approximation through the full permutation range

Frozen revision: 1. Task: global exact-denominator extension. Written November 14, 2026 Pacific.

Mathematical status: proved below, awaiting independent review. After the independent saddle review was frozen, the integrator proposed extending its coefficient lemma to $x\le1$ and retaining the permutation denominator exactly. This proof assesses that supplied direction. Prior exposure includes the accepted partition theorem, RATE-1, CORR-1, and the independently reviewed saddle proof. No historical novelty or optimality claim is made for this global formula or its rate.

## 1. Statement

For a uniform permutation matrix of size $N$, define

$$
a_k(N)=\mathbb E\prod_{i=1}^k(M_{ii}-1/N),\qquad 0\le k\le N.
$$

For $m\ge1$, retain

$$
\widetilde a_{2m}=(2m-1)!!N^{-3m},\qquad
\widetilde a_{2m+1}=\frac{4m}{3}(2m+1)!!N^{-3m-2},
\qquad R_k=\frac{a_k}{\widetilde a_k}.
$$

For every $2\le k\le N$, put

$$
\epsilon=k\bmod2,\qquad K=k-\epsilon=2m,\qquad
x=\sqrt{K/N},\qquad\lambda=\frac23Nx^3,
\qquad D_k=\frac{N^k}{(N)_k},
$$

where $(N)_k$ is the falling factorial. Define

$$
H_k=\frac{e^\lambda+(-1)^\epsilon e^{-\lambda}}{2\lambda^\epsilon},
$$

$$
q(x)=x+(x^2-1)\log(1+x)-\frac{x^2}{2}-\frac23x^3,
$$

and

$$
\boxed{
\mathcal A_{N,k}
=D_kH_k\exp(Nq(x))(1+x)^{\epsilon-1/2}.
}
\tag{1}
$$

Every factor in (1) is defined and positive on the entire range, including $k=N$.

**Theorem GLOBAL-1.** There are absolute constants $C_0,N_0$ such that for every integer $N\ge N_0$,

$$
\boxed{
\sup_{2\le k\le N}
\left|\frac{R_k}{\mathcal A_{N,k}}-1\right|
\le C_0N^{-1/4}.
}
\tag{2}
$$

Moreover, there is an absolute constant $C_1$ such that, uniformly for $\sqrt N\le k\le N$ and sufficiently large $N$,

$$
\boxed{
\left|\frac{R_k}{\mathcal A_{N,k}}-1\right|
\le C_1\left(K^{-1}+e^{-\lambda/8}\right)
=O(N^{-1/2}).
}
\tag{3}
$$

The second equality is a uniform upper bound, not an assertion of the exact error order. The constants in the analytic coefficient lemma below are absolute but are not optimized or numerically evaluated. The proof supplies an explicit lower-range bound in Section 5 using the constants of RATE-1.

The exact factor $D_k$ is essential to the stated full range. No expansion of it around $k/N=0$ is used above $\sqrt N$.

## 2. Exact coefficient identity

The accepted partition representation is

$$
Q_k=(N)_kN^ka_k=k![z^k]e^{Nf(z)},\qquad
f(z)=\frac z{1-z}+\log(1-z)
=\sum_{j\ge2}\frac{j-1}{j}z^j.
\tag{4}
$$

The exact normalizers are

$$
\mathcal L_{2m}=\frac{(2m)!}{2^m m!}N^m,\qquad
\mathcal L_{2m+1}=\frac{4m}{3}\frac{(2m+1)!}{2^m m!}N^m,
$$

and $R_k=D_kQ_k/\mathcal L_k$. The underlying recurrence and leading terms remain attributed to Collins and Nagatsu as in the accepted manuscript. Formula (4) is a known special-function reformulation with a positive coefficient interpretation, not a novelty claim of this packet.

## 3. Extend the coefficient lemma to $0<x\le1$

Let $K\ge2$, $x=\sqrt{K/N}\le1$, and $\epsilon\in\{0,1\}$. When discussing a literal permutation moment, also require $K+\epsilon\le N$. Set

$$
r=\frac{x}{1+x},\qquad b=2K(1+x).
$$

The exact saddle equation remains $Nr f'(r)=K$, and now $r\le1/2$. We claim

$$
[z^{K+\epsilon}]e^{Nf(z)}
=\frac{e^{Nf(r)}r^{-K-\epsilon}}{\sqrt{2\pi b}}
(1+E_{N,K,\epsilon}),
$$

$$
\boxed{|E_{N,K,\epsilon}|\le C\left(K^{-1}+e^{-\lambda/8}\right),}
\tag{5}
$$

with an absolute constant $C$ throughout this range.

To reconstruct the angular estimate, write

$$
\Phi(\theta)=N(f(re^{i\theta})-f(r))-iK\theta.
$$

Positivity of the coefficients gives

$$
-\Re\Phi(\theta)
\ge Nr^2\sin^2\theta
+\frac23Nr^3(1-\cos3\theta).
\tag{6}
$$

Since $Nr^2=K/(1+x)^2\ge K/4$, on $|\theta|\le\pi/6$ we have

$$
\Re\Phi(\theta)\le-\frac9{4\pi^2}K\theta^2.
\tag{7}
$$

For every fixed derivative order $j$, all required angular derivatives are bounded by a constant times $K$. Indeed, after factoring out $Nr^2\le K$, their absolute sums are bounded by convergent series of powers of the index times $(1/2)^{\text{index}-2}$. Thus

$$
\Re\Phi=-b\theta^2/2+O(K\theta^4),\qquad
\Im\Phi=O(K|\theta|^3)
$$

uniformly. Pairing conjugate angles turns the phase factor into $\cos(\Im\Phi-\epsilon\theta)$. The same real exponential comparison and cosine bound used in the reviewed saddle lemma give a central integral error bounded by

$$
C\int_{-\pi/6}^{\pi/6}
(K\theta^4+K^2\theta^6+\theta^2)e^{-cK\theta^2}\,d\theta
=O(K^{-3/2}).
$$

The central Gaussian integral is of order $K^{-1/2}$ because $2K\le b\le4K$.

At the second peak, write $\theta=\pi+u$ modulo $2\pi$, with $|u|\le\pi/6$. Then $1+\cos3u\ge1$, and

$$
\frac23Nr^3=\frac\lambda{(1+x)^3}\ge\lambda/8.
$$

The pair term supplies the same Gaussian bound in $u$. This neighborhood contributes at most $CK^{-1/2}e^{-\lambda/8}$. On the remaining angles, the pair term gives $e^{-K/16}$ damping. Dividing all errors by the central Gaussian integral proves (5).

This proof is uniform at $x=1$. The integration radius is then $r=1/2$, which stays strictly inside the singularity at $z=1$. No singular endpoint analysis is needed for the coefficient integral.

## 4. Exact denominator and normalization above $\sqrt N$

Set

$$
h(x)=q(x)+\frac23x^3.
$$

The exact action identity is

$$
Nf(r)-K\log r+K\log x-K/2=Nh(x).
$$

Applying Stirling's formula to $m!$ in the exact leading polynomial, with its $O(K^{-1})$ relative error, gives

$$
\frac{Q_k}{\mathcal L_k}
=\frac{e^{Nh(x)}(1+x)^{\epsilon-1/2}}{2\lambda^\epsilon}
\left[1+O\left(K^{-1}+e^{-\lambda/8}\right)\right].
\tag{8}
$$

The odd additional factor is exactly $3/(2Kr)=(1+x)/\lambda$, as in the reviewed saddle proof. This identity is valid throughout $0<x\le1$, including $K=N-1$.

Divide (8) by $e^{Nq(x)}(1+x)^{\epsilon-1/2}H_k$. The exact residual parity factor is

$$
\frac1{1+(-1)^\epsilon e^{-2\lambda}}.
$$

For $\lambda\ge1$, its denominator is bounded away from zero. Multiplication by $D_k$ cancels exactly between $R_k$ and $\mathcal A_{N,k}$. Hence

$$
\left|\frac{R_k}{\mathcal A_{N,k}}-1\right|
\le C'\left(K^{-1}+e^{-\lambda/8}\right).
\tag{9}
$$

If $k\ge\sqrt N$, then $K\ge\sqrt N-1$ and $\lambda\ge cN^{1/4}$ with an absolute $c>0$ for large $N$. The right side of (9) is uniformly $O(N^{-1/2})$. This proves (3) all the way to $k=N$.

## 5. Explicit patch below $\sqrt N$

For $N\ge16$ and $2\le k\le\sqrt N$, define

$$
J_{N,k}=\log\frac{\mathcal A_{N,k}}{e^{k^2/(4N)}H_k}.
$$

The exact derivative identity $q'(x)=2x(\log(1+x)-x)$ and the bounds

$$
0\le\log(1+x)-x+x^2/2\le x^3/3
$$

imply

$$
0\le q(x)+x^4/4\le2x^5/15.
\tag{10}
$$

These follow by integrating elementary derivative inequalities, so no asymptotic series truncation is required.

The denominator bound from RATE-1 is

$$
0\le\log D_k-\frac{k(k-1)}{2N}\le\frac{k^3}{3N^2}.
$$

The difference between $k(k-1)/(2N)$ and $(k^2+K^2)/(4N)$ has absolute value at most $k/(2N)$ for both parities. Also $|(\epsilon-1/2)\log(1+x)|\le x/2$. Therefore

$$
|J_{N,k}|
\le\frac{k}{2N}+\frac{k^3}{3N^2}
+\frac{2K^{5/2}}{15N^{3/2}}+\frac12\sqrt{K/N}
\le r_N,
$$

$$
r_N=\frac{19}{30}N^{-1/4}+\frac56N^{-1/2}.
\tag{11}
$$

Let $A_1(1),A_2(1),A_3(1)$ be the explicit constants in RATE-1 and put

$$
L_N=A_1(1)N^{-1/4}+A_2(1)N^{-1/2}+A_3(1)N^{-1}.
$$

Since $R_k/\mathcal A_{N,k}=W_{N,k}e^{-J_{N,k}}$, RATE-1 and (11) give the fully explicit lower-range estimate

$$
\boxed{
\sup_{2\le k\le\sqrt N}
\left|\frac{R_k}{\mathcal A_{N,k}}-1\right|
\le e^{r_N}L_N+e^{r_N}-1.
}
\tag{12}
$$

This is $O(N^{-1/4})$ with an absolute constant. Combining (12) with (3) proves GLOBAL-1.

The low-order patch does not treat the small-$\lambda$ coefficient integral as a single saddle. It uses the exact parity-sensitive theorem already proved on that range.

## 6. The endpoint $k=N$

For even $N$, one has $K=N$, $x=1$, $r=1/2$, $\lambda=2N/3$, $h(1)=1/2$, and $q(1)=-1/6$. Every factor in (1) is finite, and (9) has error $O(N^{-1})$. Stirling's formula for $D_N=N^N/N!$ yields

$$
\boxed{
R_N=\frac{e^{3N/2}}{4\sqrt{\pi N}}\left(1+O(N^{-1})\right)
\qquad(N\text{ even}).
}
\tag{13}
$$

For odd $N$, the required normalization has $K=N-1$ and $x=\sqrt{1-1/N}$, rather than $x=1$. In this case

$$
Nh(x)=N/2-\log2+O(N^{-1}),\qquad
\lambda=\frac{2N}{3}(1-1/N)^{3/2}.
$$

The odd factor in (8) remains $(1+x)^{1/2}/(2\lambda)$. Together with $D_N$, it gives

$$
\boxed{
R_N=\frac{3e^{3N/2}}{8\sqrt\pi\,N^{3/2}}\left(1+O(N^{-1})\right)
\qquad(N\text{ odd}).
}
\tag{14}
$$

Equivalently, in the original unnormalized moments both parities satisfy

$$
\boxed{a_N(N)=\frac1{2N!}\left(1+O(N^{-1})\right).}
\tag{15}
$$

One direct check of (15) uses the analytic coefficient lemma with degree $K=N$ and phase offset zero, irrespective of the parity of the integer $N$. The coefficient lemma itself has no evenness hypothesis on $K$. At $r=1/2$, it gives

$$
[z^N]e^{Nf(z)}=\frac{e^N}{\sqrt{8\pi N}}\left(1+O(N^{-1})\right).
$$

Equation (4) says $a_N=[z^N]e^{Nf(z)}/N^N$, and Stirling's formula proves (15). The literal odd moment normalization in the global theorem is nevertheless always the one with $K=N-1$, as explicitly checked in (14).

## 7. Dependencies, checks and scope

GLOBAL-1 depends on the exact positive coefficient identity, the elementary extended angular estimate in Section 3, the exact even and odd normalizers, and RATE-1 for the low-order patch. The reviewed sublinear saddle proof supplies the pattern of the calculation, but its restriction $x\le1/4$ is not silently reused beyond its scope. The needed enlargement is proved here with new uniform bounds at $r\le1/2$.

The full-range result retains $D_k$ exactly. Replacing it with a truncated exponent near $k/N=0$ would lose the endpoint statement. No historical novelty, best possible global rate, or graph eigenvalue conclusion is claimed.

`check_global.py` corroborates finite moments and the endpoint examples. General validity and uniformity depend on the proof, not the numerical checks. This packet must receive an independent review before any new canonical status or manuscript claim is changed.
