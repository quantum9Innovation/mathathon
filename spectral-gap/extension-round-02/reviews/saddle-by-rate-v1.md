# Independent review of the sublinear saddle theorem

Task: SG-E2-REV. Reviewer: rate investigator. Recipient: problem 21 integrator.

Reviewed revision: `../saddle/proof-v1.md`, SHA256 `c9033ac8ff15bd5265771eaad4d4b7eeeb2b2e19860decfa63e0b2bb8c177da8`.

Reviewed input packet: `../saddle/MANIFEST-v1.json`. All six listed files matched their recorded hashes during this review. The inherited manuscript dependency is accepted frozen revision 5, whose manifest hash is `ce8f5240a55ef278b9ab2c6ce53cc25f7688fcd28dafd602937c303a06b8ac78`.

Prior exposure: the reviewer wrote the separate positive-partition extension, RATE-1 and CORR-1, and had read the accepted revision 5. The saddle proof was first read for this audit. No new integrator checkpoint or another live attempt was read before freezing this review. The mathematical checks below reconstruct the saddle proof directly rather than relying on agreement with the reviewer's own expansion.

## Verdict

Accept the exact frozen revision as a written proof of SG-E2-S1, SG-E2-S2 and SG-E2-S3 at their stated scope. No unsupported inference or mathematical defect was found. The coefficient lemma has the required uniform error, the odd normalization is exact, and the low-order patch invokes an already accepted theorem with the correct range.

This is a mathematical review, not a historical-priority assessment or an end-to-end formal verification. Numerical evidence is not used as a premise.

## 1. The coefficient integral and both angular peaks

The saddle equation is exact:

$$
r=\frac{x}{1+x},\qquad Nr f'(r)=K,
\qquad N(r\partial_r)^2f(r)=2K(1+x).
$$

For $0<x\le1/4$, we have $r\le1/5$ and $Nr^2=K/(1+x)^2\ge16K/25$. Keeping the pair and triple terms from the positive coefficient series gives the proof's damping inequality (9).

On $|\theta|\le\pi/6$,

$$
\sin^2\theta\ge\frac9{\pi^2}\theta^2.
$$

Thus the real part of the phase is at most

$$
-\frac{144}{25\pi^2}K\theta^2.
$$

This supplies an absolute Gaussian bound over the full central interval, independently of the Taylor remainder. For every fixed derivative order, the convergent sum

$$
\sum_{j\ge2}\frac{j-1}{j}j^q(1/5)^{j-2}
$$

bounds the phase derivatives after factoring out $Nr^2\le K$. The fourth-order real and third-order imaginary Taylor remainders in (11) are therefore uniform.

The extra phase $-i\delta\theta$ is retained. After symmetry, the cosine error is bounded by a constant times $K^2\theta^6+\theta^2$. The exponential comparison contributes $K\theta^4$. Their integrals against the common Gaussian bound are all $O(K^{-3/2})$. Dividing by the main Gaussian integral of order $K^{-1/2}$ gives $O(K^{-1})$.

At the second peak, write $\theta=\pi+u$ modulo $2\pi$, with $|u|\le\pi/6$. Then $1+\cos3u\ge1$ and

$$
\frac23Nr^3=\frac\lambda{(1+x)^3}\ge\frac{64}{125}\lambda.
$$

The same pair term damps $u$ quadratically. The entire second-peak integral is consequently at most a constant times $K^{-1/2}e^{-64\lambda/125}$. On the remaining angles, the pair term gives $e^{-4K/25}$ damping. This proves the asserted relative error $O(K^{-1}+e^{-c\lambda})$, with an absolute positive $c$.

In particular, the proof does not discard the second peak while $\lambda$ is bounded. The error bound can be large there, and the argument only takes its logarithm after $K$ and $\lambda$ are sufficiently large. That restriction is respected later.

## 2. Exact normalization for the odd orders

Cancelling the factorial $k!$ from $Q_k$ against the leading polynomial leaves

$$
\frac{2^m m!}{N^m}
\left(\frac3{2K}\right)^\delta
[z^{K+\delta}]F_N(z).
$$

Stirling's formula for $m!$ gives the factor $\sqrt{\pi K}$ and relative error $O(K^{-1})$. The saddle denominator is $\sqrt{4\pi K(1+x)}$. The resulting even prefactor is exactly the stated $(1+x)^{-1/2}/2$, before the controlled relative error.

The odd coefficient introduces $r^{-1}$ as well as $3/(2K)$. Their product is

$$
\frac3{2Kr}=\frac{1+x}{\lambda},
$$

because $\lambda=(2/3)Kx$. This verifies (16) without discarding the one-order difference between $k$ and $K$.

The exponent identity (14) follows from $f(r)=x-\log(1+x)$ and $\log(x/r)=\log(1+x)$. Dividing by the exact even or odd $H_k$ produces the factor $(1+(-1)^\delta e^{-2\lambda})^{-1}$. Its logarithm is controlled on precisely the large-$\lambda$ range used in (17).

## 3. The permutation denominator and the combined action

The estimate for $D_k$ does not require a Stirling approximation. With $g(v)=-\log(1-v)$, monotonicity bounds the difference between its integral and its left Riemann sum by the telescoping endpoint difference $g(k/N)-g(0)$. This proves (18) with the displayed sign and error.

The derivative identities

$$
h'(x)=2x\log(1+x),\qquad
q'(x)=2x(\log(1+x)-x)
$$

were independently differentiated. The elementary bound $0\le x-\log(1+x)\le x^2/2$ gives $|q'(x)|\le x^3$. Since $t^2-x^2=\delta/N$, the change from $K$ to $k$ in the action costs at most $k/N$, as claimed in (19).

Expanding $I(t^2)+q(t)$ cancels the entire $\log(1+t)$ term and gives exactly $G(t)$. The parity prefactor $(\delta-1/2)\log(1+x)$ remains explicit in (21). Its order is $\sqrt{k/N}$, so it is correctly separated from the smaller $O(k/N)$ denominator error.

## 4. Uniformity and the low-order patch

On $\sqrt N<k\le b_N=o(N)$, the minimum $K$ is of order $\sqrt N$ and the minimum $\lambda$ is of order $N^{1/4}$. The constants in the saddle estimate are uniform, while the maximum $x$ tends to zero. Every error and the explicit parity prefactor in (21) therefore tend uniformly to zero.

On $2\le k\le\sqrt N$, the inherited v5 result is exactly a uniform relative approximation by $e^{k^2/(4N)}H_k$. The additional positive tail in $NG(\sqrt{k/N})$ is at most a constant times $k^{5/2}/N^{3/2}$, which is at most a constant times $N^{-1/4}$ in this range. Multiplying by its exponential preserves the uniform relative conclusion.

This patch covers fixed orders, either parity, and ranges crossing $\sqrt N$. It neither assumes a one-saddle approximation at small $\lambda$ nor imports the newly derived RATE-1 or CORR-1 as an unstated dependency.

## 5. Sharp truncation thresholds

The coefficients of $G$ are positive and decrease with degree after degree four. The first omitted term therefore bounds each fixed tail from below, and the geometric series bound in (24) bounds it from above. For $k=o(N)$, its relative remainder tends to zero.

The uniform theorem gives a multiplicative error tending to one, whose logarithm tends to zero. Adding that logarithm to the positive tail proves both directions of the relative-accuracy criterion. The same argument proves boundedness equivalence and divergence. The first two threshold exponents and coefficients are

$$
p=4:\quad N^{3/5},\quad\frac2{15},
\qquad
p=5:\quad N^{2/3},\quad\frac1{12}.
$$

The result concerns fixed truncation degree and sublinear orders. The proof makes neither a statement for growing truncation degree nor one for orders comparable with $N$.

## 6. Checks executed and disposition

All six frozen packet hashes were verified. Exact symbolic differentiation checked the saddle and action derivatives. Nine coefficients, through degree twelve, were independently expanded and matched $2/[j(j-2)]$. The full analytic argument, normalization, denominator error, low-order patch and threshold implications were reconstructed in this review. No author-owned file was changed and no numerical limit was used to establish the theorem.

No findings require correction. Proposed disposition: promote SG-E2-S1 through SG-E2-S3 at the reviewed proof hash, preserve the accepted older manuscript, then integrate and review the manuscript change separately. The newly supported sublinear scope and sharp next thresholds deserve clear statements, with the exact parity prefactor retained when discussing finer error terms.
