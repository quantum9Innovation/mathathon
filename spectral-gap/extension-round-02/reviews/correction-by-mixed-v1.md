# Independent review of CORR-1

Task CORR-1-REV. Reviewed 15 November 2026 UTC. Verdict: accept the signed first correction. No mathematical gap was found. The rate-optimality consequence extends to every fixed $C>0$ by the argument in Section 6 below.

Reviewed proof: rate/first-correction-v1.md, SHA256 71148f873f45e5c6db0e7535583398712febc6d153874928b1d91701395f2c42.

The separate FIRST_CORRECTION_MANIFEST-v1.json has SHA256 aa3cdc5fdab25c444276313e25f43f868a06e4663aaf986e36d096a8f0107890. Every output and source hash listed in that manifest matched the local bytes.

Prior exposure consisted of the accepted manuscript revision 5 and the independently frozen mixed-envelope proof. For this review, the correction proof, its handoff, and the referenced rate proof were read. No new saddle proof or integrator synthesis was read before this review was frozen.

## 1. Exact normalization and parity

Let $k=2m+\epsilon$, with $\epsilon\in\{0,1\}$. The leading polynomial normalizers satisfy

\[
\frac{\mathcal L_{2m}}{(2m)!}
=\frac{(N/2)^m}{m!},
\qquad
\frac{\mathcal L_{2m+1}}{(2m+1)!}
=\frac{(2N/3)(N/2)^{m-1}}{(m-1)!}.
\]

These follow directly from the stated leading coefficients. In the odd case, one compulsory three-element block is already included in the normalizer.

For counts $c_j$ of blocks with $j\ge3$, put

\[
s=\frac{\sum_{j\ge3}j c_j-3\epsilon}{2}.
\]

Whenever the block counts have the required parity and permit a nonnegative number of pairs, the number of pair blocks is $m-\epsilon-s$. Dividing the corresponding partition term by $\mathcal L_k$ yields

\[
w_\epsilon(s)\,
\frac{\lambda^{c_3-\epsilon}}{c_3!}
\prod_{j\ge4}\frac{\lambda_j^{c_j}}{c_j!}.
\tag{R1}
\]

The formula follows by dividing the pair factorials and using
$\lambda_j=N(j-1)(K/N)^{j/2}/j$, with $K=2m$. Invalid availability indices contribute zero.

For blocks of sizes two, three and four, (R1) gives $s=3J/2+2L-3\epsilon/2$. Since $J$ has parity $\epsilon$, this is a nonnegative integer. Summing its weights and dividing by $H_k$ gives exactly $e^\eta\mathbb Ew_\epsilon(s)$. In the odd case, the factor $\lambda^{-1}$ in (R1) cancels the same factor in $H_k=\sinh(\lambda)/\lambda$.

For exactly one five-element block, $J$ instead has parity $1-\epsilon$, and

\[
s_5=\frac32J+2L+\frac52-\frac32\epsilon.
\]

The minimum possible value is four for $\epsilon=0$, and one for $\epsilon=1$. Thus it is again a valid nonnegative integer. Formula (R1) gives exactly the factor

\[
\theta e^\eta
\frac{Z_{1-\epsilon}(\lambda)}{Z_\epsilon(\lambda)}
\mathbb Ew_\epsilon(s_5)
\]

in equation (17) of the reviewed proof. The parity change and the odd normalization are correct.

## 2. Independent coefficient reconstruction

Write $a=3/2$, $J=\lambda+Z$, and $h=2L-a\epsilon$. For either parity,

\[
\mathbb EZ=O(\lambda e^{-2\lambda}),
\qquad
\mathbb EZ^2=\lambda+O(\lambda^2e^{-2\lambda}).
\]

The exact identity $\mathbb EJ^2=\lambda^2+\mathbb EJ$ follows from the second factorial moment. Also $\mathbb Eh=2\eta-a\epsilon$. Expanding

\[
A=\frac{(aJ+h)^2+(2\epsilon-1)(aJ+h)}{2m}
\]

therefore gives

\[
\mathbb EA-\delta
=
\left[
\frac{a^2-a}{2}
(a-a^2)\epsilon+2a\eta
\right]\frac{\lambda}{m}
O(m^{-1})+O(\lambda^2e^{-2\lambda}/m).
\]

At $a=3/2$, the bracket is $3\eta+3(1-2\epsilon)/8$, agreeing with equation (9).

The leading fluctuation of $A-\delta$ is $a^2\lambda Z/m$. Its variance contribution to $\mathbb Ee^{-A}$ is

\[
\frac{a^4\lambda^3}{2m^2}.
\]

The next term in the logarithm of the falling factorial contributes

\[
-\frac{a^3\lambda^3}{6m^2}.
\]

Their combined coefficient is

\[
\frac{a^4}{2}-\frac{a^3}{6}
=\frac{81}{32}-\frac9{16}
=\frac{63}{32}.
\tag{R2}
\]

Restoring the single five-element block adds $\theta$. The complete unsimplified first correction is therefore

\[
\left[\frac38(2\epsilon-1)-3\eta\right]\frac{\lambda}{m}
+\frac{63\lambda^3}{32m^2}+\theta.
\]

The parameter conversions give the signed term $(2\epsilon-1)\sqrt{K/N}/2$, while the remaining coefficient is

\[
-3+\frac73+\frac45=\frac2{15}.
\tag{R3}
\]

This independently reconstructs the claimed coefficient in equation (1).

## 3. Uniform remainder audit

All statements in this section concern $k/\sqrt N$ in a fixed compact subset of $(0,\infty)$. Then $\lambda\asymp N^{1/4}$, $m\asymp\lambda^2$, and $\eta,\delta$ remain bounded. The constants are uniform over both parities.

The probabilities of the two Poisson parity events are $(1\pm e^{-2\lambda})/2$. They are bounded below uniformly for large $N$. Dividing a restricted nonnegative central moment by this probability bounds the conditioned moment by a constant times the unconditioned one. This proves the fourth and sixth central-moment bounds used in the proof. Holder's inequality then gives $\mathbb E|Z|^3=O(\lambda^{3/2})$.

Every fixed absolute moment of $h$ is uniformly bounded because $L$ has bounded Poisson mean. Hence every fixed raw moment of the nonnegative integer $s=aJ+h$ is $O(\lambda^q)$ at order $q$.

In the decomposition $A-\delta=a^2\lambda Z/m+V$, the displayed terms of $V$ give

\[
\mathbb EV^2=O(\lambda^2/m^2)=O(\lambda^{-2}),
\qquad
\mathbb E|V|^3=O(\lambda^3/m^3)=O(\lambda^{-3}).
\]

For example, the $Z^2/m$ term uses the fourth and sixth central moments, while $Jh/m$ uses independence and the bounded moments of $h$. Cauchy-Schwarz bounds the covariance between the leading term and $V$ by $O(\lambda^{-3/2})$. The third absolute moment of $A-\delta$ is consequently $O(\lambda^{-3/2})$. Since $A,\delta\ge0$, the third derivative bound for $e^{-x}$ applies throughout the Taylor interval.

For the availability logarithm, summing $u=r/m$ over $r=\epsilon,\ldots,s-1+\epsilon$ gives the linear term exactly equal to $A$. On $s\le m/2$, the quadratic sum equals

\[
\frac{s^3}{6m^2}+O(s^2/m^2),
\]

and the remaining logarithm terms total $O(s^4/m^3)$. The nonlinear remainder $B=-\log w_\epsilon(s)-A$ is nonnegative and bounded by $Cs^3/m^2$ on this event. Thus the quadratic error in expanding $e^{-B}$ has expectation $O(\mathbb Es^6/m^4)=O(\lambda^{-2})$.

The discarded event satisfies

\[
\mathbb P(s>m/2)
\le\frac{16\mathbb Es^4}{m^4}
=O(\lambda^{-4}).
\]

The factors $w_\epsilon(s)$ and $e^{-A}$ are bounded by one even outside the retained event. The discarded cubic expectation, divided by $m^2$, is at most

\[
\frac{(\mathbb Es^6)^{1/2}
\mathbb P(s>m/2)^{1/2}}{m^2}
=O(\lambda^{-3}).
\]

Finally,

\[
\frac{\mathbb E[|e^{-A}-e^{-\delta}|s^3]}{m^2}
\le
\frac{(\mathbb E(A-\delta)^2)^{1/2}
(\mathbb Es^6)^{1/2}}{m^2}
=O(\lambda^{-3/2}).
\]

The resulting error budget is:

| Source | Bound |
| --- | --- |
| Omitted terms in $\mathbb EA-\delta$ | $O(\lambda^{-2})$ plus exponential error |
| Variance remainder and third Taylor remainder | $O(\lambda^{-3/2})$ |
| Quadratic and higher errors in the availability logarithm | $O(\lambda^{-2})$ |
| Tail contribution of the bounded factors | $O(\lambda^{-4})$ |
| Tail contribution of the cubic term | $O(\lambda^{-3})$ |
| Replacing $e^{-A}$ by $e^{-\delta}$ in the cubic term | $O(\lambda^{-3/2})$ |

Every entry is $o(\lambda^{-1})$, uniformly on the stated compact positive scale. No tail contribution of the required order has been omitted.

## 4. Higher blocks and the five-element contribution

With $x=\sqrt{K/N}$, the total weight of blocks of size at least six is at most

\[
\frac{Nx^6}{1-x}=O(N^{-1/2})=O(\lambda^{-2}).
\]

Also $\theta=O(\lambda^{-1})$, so the weight of at least two five-element blocks is $O(\lambda^{-2})$. Removing availability factors increases these nonnegative sums. Summing the remaining triple counts without parity restrictions costs at most a bounded factor $e^\lambda/Z_\epsilon(\lambda)$ after normalization by (R1). The four-element blocks contribute the bounded factor $e^\eta$. This justifies the normalized omission bound in equation (16).

The convergence assertion for one five-element block can be made quantitative using the same moment estimates. Put

\[
A_5=\frac{s_5(s_5-1+2\epsilon)}{2m}.
\]

Its shifted constant part has bounded moments, so
$\mathbb E|A_5-\delta|=O(\lambda^{-1/2})$. The global availability estimate from the referenced rate proof gives

\[
\mathbb E|w_\epsilon(s_5)-e^{-A_5}|
\le\frac{4\mathbb Es_5^3}{m^2}
=O(\lambda^{-1}).
\]

The Lipschitz bound for $e^{-x}$ on $x\ge0$ now implies

\[
\mathbb Ew_\epsilon(s_5)
=e^{-\delta}+O(\lambda^{-1/2}).
\]

After multiplication by $\theta$, its error is $O(\lambda^{-3/2})$. The ratio of opposite parity normalizers differs from one by $O(e^{-2\lambda})$. Thus the contribution retained in equation (17) is correct, with a remainder smaller than the target order.

## 5. The permutation denominator

Direct logarithmic expansion gives

\[
\log D_k
=\frac{k(k-1)}{2N}+O(k^3/N^2).
\]

The difference between the first term and $(k^2+K^2)/(4N)$ is $-k/(2N)$ for even $k$, and $-1/(4N)$ for odd $k$. Both that difference and the remainder are $O(N^{-1/2})$ on the scale under review. Hence

\[
D_k\exp\left(-\frac{k^2+K^2}{4N}\right)
=1+O(N^{-1/2}).
\]

This is $o(N^{-1/4})$. The other deterministic multipliers remain bounded above and below on the positive compact scale, so multiplying the previous remainders does not change their order. Exact normalization therefore introduces no additional first-order coefficient.

## 6. Optimality for every fixed positive endpoint

The reviewed proof explicitly states a supremum lower bound only for $C\ge1$. This is a limited statement of a stronger consequence, not a defect in CORR-1.

Fix any $C>0$ and choose $c\in(0,C)$. Let $k_N$ be the largest odd integer at most $c\sqrt N$. Then $k_N\ge3$ for all sufficiently large $N$, it belongs to the range $2\le k\le C\sqrt N$, and $k_N/\sqrt N\to c$. CORR-1 gives

\[
N^{1/4}(W_{N,k_N}-1)
\longrightarrow
g_1(c):=\frac{\sqrt c}{2}+\frac{2c^{5/2}}{15}>0.
\]

It follows that

\[
\liminf_{N\to\infty}
N^{1/4}
\sup_{2\le k\le C\sqrt N}|W_{N,k}-1|
\ge g_1(c)>0.
\tag{R4}
\]

Since this holds for every $c<C$, continuity as $c$ increases to $C$ also gives the lower bound $g_1(C)$. No matching upper asymptotic for this supremum is asserted by this review.

For $C<1$, the upper $O(N^{-1/4})$ rate already follows by restricting RATE-1 with endpoint one to the smaller range. Thus the order is optimal for every fixed $C>0$, without requiring any extension of the published constants in RATE-1.

The exceptional zero of the even coefficient does not affect this conclusion. The odd coefficient is strictly positive, and the argument deliberately selects odd orders.

## 7. Independent finite corroboration

An independent exact rational calculation compared the original partition coefficient with (R1), separately for blocks of sizes two, three and four and for exactly one five-element block. All 184 cases passed, covering $2\le k\le32$ and $N$ in the distinct values among $k$, $2k$, and $k^2$.

The rational coefficient calculations (R2), (R3), and both parity constants also passed. A separate 60-digit recurrence calculation evaluated eight examples at $N=10^6$ and $N=10^8$, with limiting scales $c=1/4$ and $c=1$, in both parities. The values approach the predicted signed limits. For instance, at $N=10^8$, $k=10000$ gives scaled error approximately $-0.3676814$, compared with the limit $-11/30$. At $k=9999$ the value is approximately $0.6260080$, compared with $19/30$.

These calculations corroborate the normalizations and coefficients only. The universal conclusion rests on the reconstructed argument and remainder bounds above. The original numerical checker was not treated as independent proof evidence.

## 8. Findings and recommendation

- CORR-REV-01: exact parity conditioning and normalization pass.
- CORR-REV-02: signed coefficient, cubic logarithm term, and five-element coefficient pass.
- CORR-REV-03: the remainders are uniform on every compact positive scale and are smaller than $N^{-1/4}$.
- CORR-REV-04: the exact denominator does not change the first coefficient.
- CORR-REV-05: the consequence for every $C>0$ is supplied by (R4). The integrator may state this stronger consequence explicitly.

Recommend accepting CORR-1 at the reviewed hash. This review does not assess historical priority, an unbounded scale, or a further coefficient at the exceptional even value. No source or canonical file was changed.
