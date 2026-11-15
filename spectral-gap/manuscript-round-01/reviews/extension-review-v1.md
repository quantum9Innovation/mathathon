# Independent review of the hyperbolic window and its boundary

Task: SG-M5, extension review. Sender: proof investigator. Recipient: problem 21 integrator. Review revision: 1, frozen November 14, 2026 Pacific.

Reviewed source: `extensions/hyperbolic-window-v1.md`.

Reviewed SHA256: `73de96b41b7fba59454795f14bf1fe6160f8eee1391553bf980f3f29f4eba68a`.

## Verdict

Accept EXT-A and EXT-B at the exact reviewed revision as supported written proofs. The finite envelope, relative approximation on $k=o(\sqrt N)$, boundary correction $e^{d/4}$ when $k^2/N\to d$, and uniform corrected approximation for bounded $k/\sqrt N$ all follow from the displayed arguments. No unsupported inference or mathematical defect was found.

The positive generating identity and the parity normalization were reconstructed independently from the known moment recurrence. The square-root proof was checked directly, including the aggregate tail of all blocks of size at least five and the dependence between parity and available pairs. The finite checks below are corroboration only.

Prior exposure: the coordinator had stated that a relative extension through $k=o(\sqrt N)$ and a square-root correction were proposed. The reviewer did not read the extension author's numerical checker, its outputs, or another extension review. The core moment recurrence had already been independently reconstructed in SG-M1.

## 1. Statements and dependencies checked

For $k\ge2$, put $m=\lfloor k/2\rfloor$, $K=2m$, and

$$\lambda=\frac23\sqrt{K^3/N}.$$

The reference functions are $H_k=\cosh\lambda$ for even $k$ and $H_k=\sinh\lambda/\lambda$ for odd $k$. The ratio $R_k$ uses exactly the parity-dependent leading terms in equation (1) of the reviewed proof.

The accepted finite envelope is

$$\left(1-\frac{4k^2}{3N}\right)H_k\le R_k\le e^{4k^2/N}H_k,
\qquad2\le k\le N/4.$$

The lower bound is intentionally allowed to become negative. The logarithmic form applies when $4k^2\le N$. The asymptotic boundary statement assumes $k^2/N\to d\in(0,\infty)$, while the zero case follows from the finite envelope. The uniform corollary is over integer $2\le k\le C\sqrt N$, with fixed $C$.

Direct dependencies are the known moment recurrence and leading terms, finite coefficient algebra, elementary power series, and elementary Poisson mean, variance and parity identities. The critical-scale proof in the earlier packet is not used as a premise of EXT-A or the positive-boundary calculation. Historical priority and special-function attribution are separate source questions.

## 2. EXT-R1: exact positive representation

Status: accepted without correction at the reviewed revision.

Multiplying the moment recurrence by $(N)_{k-1}N^k$ gives

$$Q_k=2(k-1)Q_{k-1}+(k-1)(N-k+2)Q_{k-2}.$$

The coefficient of $z^{k-1}$ in

$$(1-z)^2F_N'(z)=NzF_N(z)$$

is exactly this recurrence. The initial conditions $Q_0=1,Q_1=0$ determine the formal series uniquely. Integration gives

$$F_N(z)=\exp\left(N\sum_{j\ge2}\frac{j-1}{j}z^j\right).$$

Expanding each exponential factor proves the nonnegative partition formula. Extending the polynomial recurrence beyond $k=N$ is legitimate for this formal calculation and is not used to define nonexistent permutation moments.

A separate derivation uses the distinguished block of a labeled partition. A block of size $j$ has weight $N(j-1)(j-1)!$, so the partition polynomials satisfy

$$Q_k=\sum_{j=2}^k\binom{k-1}{j-1}N(j-1)(j-1)!Q_{k-j}.$$

This recurrence provides an independent finite check of the generating function and its coefficients.

## 3. EXT-R2: both availability normalizations

Status: accepted without correction at the reviewed revision.

The identity

$$R_k=\frac{N^k}{(N)_k}\frac{Q_k}{L_k}$$

follows because $L_k=N^{2k}\widetilde a_k$ for both parities.

For even $k=2m$, if the nonpair blocks occupy $S$ labels, there are $m-S/2$ pairs. Dividing their factorial by the all-pair factorial yields

$$\frac{(m)_{S/2}}{m^{S/2}}\prod_{j\ge3}\frac{\lambda_j^{c_j}}{c_j!}.$$

For odd $k=2m+1$, the reference partition has one triple and $m-1$ pairs. If $S$ labels occur in nonpair blocks, write $s=(S-3)/2$. The pair count is $m-1-s$. Dividing by the reference term gives

$$\frac{(m-1)_s}{m^s}\frac1\lambda\prod_{j\ge3}\frac{\lambda_j^{c_j}}{c_j!}.$$

The factor $1/\lambda$ is essential and correct. The availability function's denominator is $m^s$, not $(m-1)^s$. These formulas also cover $m=1$. Any impossible count is zero because the falling factorial reaches a zero factor.

## 4. EXT-R3: finite upper and lower bounds

Status: accepted without correction at the reviewed revision.

For the upper bound, $x=\sqrt{K/N}\le1/2$ follows from $k\le N/4$. The entire nontriple tail satisfies

$$\sum_{j\ge4}\lambda_j\le\frac{Nx^4}{1-x}\le2K^2/N.$$

Thus there is no omitted family of large blocks. The odd-tail ratio obeys

$$\frac B\lambda\le1+\frac32\frac{x^2}{1-x^2}\le1+2K/N\le e^{K^2/N}.$$

The logarithmic derivatives used to compare the hyperbolic functions are between zero and one. Combining these estimates with $\log D_k\le k^2/N$ gives the stated upper exponent $4k^2/N$.

For the lower bound, retaining only pairs and triples is valid by positivity. The even and odd availability products satisfy, including their zero extensions,

$$\frac{(m)_s}{m^s}\ge1-\frac{s(s-1)}{2m},\qquad
\frac{(m-1)_s}{m^s}\ge1-\frac{s(s+1)}{2m}.$$

For even Poisson-series weights, $\mathbb E J=\lambda\tanh\lambda$ and $\mathbb E J^2=\lambda^2+\lambda\tanh\lambda$. Taking $s=3J/2$ gives the loss

$$\frac{9\lambda^2+3\lambda\tanh\lambda}{8m}\le\frac{4K^2}{3N}.$$

For odd weights, $\mathbb E J=\lambda\coth\lambda$ and $\mathbb E J^2=\lambda^2+\lambda\coth\lambda$. Taking $s=3(J-1)/2$ gives

$$\frac{9\lambda^2-3\lambda\coth\lambda+3}{8m}\le\frac{K^2}{N}.$$

Multiplying by $D_k\ge1$ preserves the useful nonnegative lower bound. If its right side is negative, positivity of $R_k$ supplies the stated inequality instead. The proof explicitly handles this point.

The logarithmic lower bound follows from $\log(1-4u/3)\ge-2u$ on $0\le u\le1/4$. Consequently the relative approximation holds throughout $k=o(\sqrt N)$, even when the cubic parameter diverges.

## 5. EXT-R4: all higher-block tails at the boundary

Status: accepted without correction at the reviewed revision.

Assume $k^2/N\to d>0$. Then $K^2/N\to d$, $m\asymp\sqrt N$, and

$$\lambda\asymp N^{1/4},\qquad
\lambda_4\to3d/4.$$

The aggregate mean of every block of size at least five is

$$\sum_{j\ge5}\lambda_j\le\frac{Nx^5}{1-x}
=O(N^{-1/4})\to0.$$

A union bound therefore shows that such blocks are absent with probability tending to one. Bounding only each fixed block size would not suffice, but the reviewed proof controls their full sum.

Poisson variance gives $C_3/\lambda\to1$ in probability. The variable $C_4$ is tight because its mean converges. Hence, on either relevant parity event,

$$s=\frac32C_3+2C_4+O(1),$$

with

$$\frac{s^2}{2m}\to d,\qquad\frac sm\to0,\qquad\frac{s^3}{m^2}\to0.$$

The pair-depletion logarithm expansions have a uniform absolute remainder bounded by a constant times $s^3/m^2$ whenever $s/m\le1/2$. That event has probability tending to one. The distinction between $s(s-1)$ and $s(s+1)$ contributes $s/m\to0$, so both parities have availability limit $e^{-d}$.

## 6. EXT-R5: parity and depletion are not assumed independent

Status: accepted without correction at the reviewed revision.

The parity probabilities are exactly

$$\mathbb P(S\text{ even})=\frac{1+e^{-2B}}2,
\qquad
\mathbb P(S\text{ odd})=\frac{1-e^{-2B}}2.$$

Since $B\ge\lambda\to\infty$, both tend to $1/2$. The necessary step is stronger than merely identifying these marginal probabilities. For either parity event $A_N$, the preceding concentration argument gives

$$\mathbf1_{A_N}|w-e^{-d}|\longrightarrow0$$

in probability. Its value is uniformly bounded by one. Therefore its mean tends to zero. Consequently

$$\mathbb E[\mathbf1_{A_N}w]=e^{-d}\mathbb P(A_N)+o(1)\to\tfrac12e^{-d}.$$

This proves the multiplication of the parity probability and the limiting availability without asserting finite-$N$ independence.

Next, $\Lambda-\lambda\to3d/4$. Dividing the Poisson expectation by the even or odd hyperbolic factor gives $e^{3d/4-d}=e^{-d/4}$. Finally,

$$\log D_k=\frac{k(k-1)}{2N}+O(k^3/N^2)\to d/2.$$

The total correction is therefore $e^{d/4}$, as claimed. The three contributions $3d/4$, $-d$, and $d/2$ all have the correct signs.

## 7. EXT-R6: uniform corrected approximation

Status: accepted without correction at the reviewed revision.

A failed uniform limit for some fixed $C$ would give a sequence with $2\le k\le C\sqrt N$ and error bounded below by a positive constant. Compactness permits a subsequence with $k^2/N\to d\in[0,C^2]$. If $d>0$, EXT-B makes the corrected ratio converge to one. If $d=0$, the logarithmic form of EXT-A gives the same conclusion, and the exponential correction itself tends to one. This proves the uniform limit.

The argument also covers bounded $k$, mixed parity sequences, and nonconvergent original sequences by subsequence extraction. It does not give a convergence rate, and none is claimed.

## 8. Independent computations executed

The new supporting program `extension-review-checks.py` was written without reading the extension author's checker. It completed successfully and recorded the source hash in `extension-review-checks.json`.

| Check | Cases | Arithmetic |
| --- | ---: | --- |
| Cleared moments from inclusion-exclusion, the two-term recurrence, and distinguished-block counting | 1196 | Exact integers |
| Every even and odd availability normalization for partitions in the recorded range | 7193 | Exact rationals |
| Finite envelope and logarithmic lower bound | 7875 | 70 decimal digits |
| Square-root examples at three dimensions and three scales, both parities | 18 | 70 decimal digits |

For example, at $N=10^8$, $k=10000$, the ratio $R_k/H_k$ is approximately $1.2793042942$, while division by $e^{k^2/(4N)}$ gives approximately $0.9963231861$. At the neighboring odd order $k=10001$, the corrected ratio is approximately $1.0062612687$. These approach the common corrected limit from different sides, consistent with the proof. Their finite accuracy is not presented as a convergence rate.

Exact computations certify only their finite identities. Numerical checks are corroboration only. No kernel verification or new graph spectral-gap theorem is claimed.

## 9. Proposed status and next action

Promote EXT-A and EXT-B at the reviewed hash to proved, reviewed in the local written-proof vocabulary. They can enter the main manuscript as the relative hyperbolic window and its first square-root correction. Maintain the explicit restriction to bounded $k/\sqrt N$ for the corrected asymptotic formula. Keep the recurrence and classical generating-function reformulation attributed to prior work.

No serious issue or correction was found, so no issue-registry entry is requested. Priority remains subject to the separate source investigation. Requested next action: integrate the accepted formulas and proof mechanism, then audit the assembled manuscript's notation, domains and claims against this exact revision.
