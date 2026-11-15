# Central derivations

These notes reorganize the paper's arguments. **Paper** identifies stated inputs. **Derived** contains my expanded steps. No numerical checks were run. Proposals marked “numerically checkable” await user approval, as required by the digest workflow.

For brevity in this file only, set $q=d-1$ in the regular-graph derivations. This $q$ is unrelated to the probability parameter $q$ in Lemma 12 or the path multiplicity $q(\gamma)$.

## D1. From adjacency eigenvalues to non-backtracking eigenvalues

### Target

Show why Theorem 2 implies Theorem 1 and why the non-backtracking additive error becomes squared in Eq. 2.

### Where it appears

Section 2.2, pages 5 and 6, Eqs. 7, 12, and 13. Theorem 1 and Eq. 2 are on page 2.

### Inputs

- **Paper:** Conditioning the configuration model on simplicity gives the uniform simple $d$-regular graph, and $\mathbb P(\text{simple})\to e^{-(d^2-1)/4}>0$ by Eq. 7.
- **Paper:** Ihara-Bass, Eq. 12, for simple $d$-regular graphs.
- **Paper:** Theorem 2 and its quantitative form Eq. 13.

### Derivation

First transfer high-probability events. Let $\mathcal S$ be the simplicity event and let $E_n$ be any spectral bad event for the simple graph. Since conditioning on $\mathcal S$ gives the uniform simple model,

$$
\mathbb P_{\mathrm{uniform}}(E_n)
=\mathbb P_{\mathrm{config}}(E_n\mid\mathcal S)
\leq\frac{\mathbb P_{\mathrm{config}}(E_n)}{\mathbb P_{\mathrm{config}}(\mathcal S)}.
$$

The denominator tends to a positive constant. Therefore a configuration-model bad event of probability $o(1)$ or $O(n^{-a})$ retains that form after conditioning, up to a constant factor.

Now expand Ihara-Bass spectrally. For each adjacency eigenvalue $\mu$,

$$
\det(I-Az+qz^2I)=\prod_{\mu\in\sigma(A)}(1-\mu z+qz^2).
$$

Setting $z=1/\lambda$ and multiplying by $\lambda^2$ produces

$$
\lambda^2-\mu\lambda+q=0,
$$

or equivalently

$$
\mu=\lambda+\frac q\lambda.
$$

The factor $(1-z^2)^r$ accounts for additional spectrum at $\pm1$.

Suppose $|\mu|\geq2\sqrt q$, and put $|\mu|=2\sqrt q(1+\delta)$ with $\delta\geq0$. Choose the root $\lambda$ having the same sign as $\mu$ and larger modulus. Its modulus is

$$
\begin{aligned}
|\lambda|
&=\frac{|\mu|+\sqrt{\mu^2-4q}}2\\
&=\sqrt q\left(1+\delta+\sqrt{(1+\delta)^2-1}\right)\\
&=\sqrt q\left(1+\delta+\sqrt{\delta(2+\delta)}\right)\\
&\geq\sqrt q(1+\sqrt\delta).
\end{aligned}
$$

This is exactly the algebraic relation displayed on page 6.

For the asymptotic implication, if some nontrivial $|\mu|$ exceeded $2\sqrt q$ by a fixed additive amount, then $\delta$ would be bounded below by a positive constant. The corresponding $|\lambda|$ would exceed $\sqrt q$ by a fixed additive amount, contradicting Theorem 2 after conditioning on simplicity.

For the quantitative implication, suppose all non-Perron non-backtracking eigenvalues satisfy $|\lambda|\leq\sqrt q+\eta$. For every nontrivial adjacency $\mu$ with $|\mu|=2\sqrt q(1+\delta)$ and $\delta\geq0$, the preceding root estimate forces

$$
\sqrt q\,\sqrt\delta\leq\eta.
$$

Consequently,

$$
\delta\leq\frac{\eta^2}{q},
\qquad
|\mu|\leq2\sqrt q\left(1+\frac{\eta^2}{q}\right).
$$

Taking $\eta=c\log\log n/\log n$ gives an adjacency additive error proportional to $(\log\log n/\log n)^2$. This is the source of the square in Eq. 2, not an arbitrary loss in the final estimate.

### Dimensional and degree check

$A$ is $n\times n$, while $B$ is $nd\times nd$. The left side of Eq. 12 has degree $nd$ in $z$. The right side has degree $2r+2n$, with $r=nd/2-n$, hence also degree $nd$. The quadratic correspondence therefore preserves the total determinant degree.

### Hidden assumptions

- $d$ is fixed, so the limiting simplicity probability is bounded below.
- The determinant identity is being used as a cited input, not rederived.
- The spectral bad event must include every non-Perron direction relevant to both signs of $\mu$.
- Complex non-backtracking eigenvalues do not invalidate the determinant calculation. Only real roots outside radius $\sqrt q$ are used to infer the adjacency upper bound.

### Intuition

Non-backtracking paths see effective branching $d-1$. Near the Ramanujan threshold, an adjacency excess $\delta$ magnifies to a non-backtracking excess of order $\sqrt\delta$. This square-root sensitivity is why a first-order error for $B$ becomes a second-order error for $A$.

### Failure modes

- Applying the simple-graph conditioning argument without controlling $\mathbb P(\mathcal S)$ would fail.
- Letting $d$ grow with $n$ would require revisiting both the simplicity bound and every $d$-dependent constant.
- Using only $\mu=\lambda+q/\lambda$ near $\lambda=\sqrt q$ gives the weaker linear estimate $|\mu|\lesssim2\sqrt q+\eta$. The square gain requires the precise root formula above.

### Numerically checkable

The identity $|\lambda|=\sqrt q(1+\delta+\sqrt{\delta(2+\delta)})$ can be checked over a grid of $q$ and $\delta$ by evaluating $\lambda^2-\mu\lambda+q$. **Not run.**

### Remember this

Conditioning transfers the model, Ihara-Bass transfers the spectrum, and $\sqrt\delta$ explains the squared rate.

## D2. Lemma 3 and the non-normal eigenvalue bound

### Target

Derive

$$
|\lambda_2|\leq
\sup_{x\perp\chi,\ \|x\|_2=1}\|B^\ell x\|_2^{1/\ell}
$$

without assuming that $B$ is normal, following Eq. 14 on page 7.

### Where it appears

Section 2.3, Lemma 3 and Eq. 14 on page 7.

### Inputs

- **Paper:** $B\chi=q\chi$ and $B^*\chi=q\chi$ from Eq. 11.
- **Paper:** Lemma 3's two inclusions $\operatorname{im}S\subset\ker R$ and $\operatorname{im}S^*\subset\ker R$.
- **Derived choice:** $S=q^\ell\chi\chi^*/(dn)$ and $R=B^\ell-S$.

### Derivation

Let $\lambda$ be an eigenvalue of $S+R$ but not of $S$. For nonzero $\lambda$, $S-\lambda I$ is invertible. Since $RS=0$ from $\operatorname{im}S\subset\ker R$,

$$
R(S-\lambda I)=-\lambda R,
\qquad
R(S-\lambda I)^{-1}=-\lambda^{-1}R.
$$

Therefore

$$
\begin{aligned}
\det(S+R-\lambda I)
&=\det(S-\lambda I)
\det\left(I+R(S-\lambda I)^{-1}\right)\\
&=\det(S-\lambda I)\det(I-\lambda^{-1}R).
\end{aligned}
$$

The left determinant vanishes and the first factor does not. Hence $\lambda$ is an eigenvalue of $R$. Choose $x\ne0$ with $Rx=\lambda x$.

Decompose $x=y+z$ with $y\in\ker S$ and $z\in(\ker S)^\perp$. For a complex matrix,

$$
(\ker S)^\perp=\operatorname{im}(S^*).
$$

The second kernel inclusion gives $Rz=0$. Orthogonality also yields $\|y\|_2\leq\|x\|_2$. Since $Sy=0$,

$$
Rx=Ry=(S+R)y,
$$

so

$$
|\lambda|\leq\frac{\|(S+R)y\|_2}{\|y\|_2}
\leq\max_{u\in\ker S,\ u\ne0}
\frac{\|(S+R)u\|_2}{\|u\|_2}.
$$

If $\lambda=0$ and $0$ is not an eigenvalue of $S$, then $S$ is invertible. The assumption $\operatorname{im}S\subset\ker R$ forces $R=0$, contradicting that $0$ is an eigenvalue of $S+R$ but not of $S$. Thus the excluded zero case causes no gap.

For the application, $S$ has image $\operatorname{span}\{\chi\}$, as does $S^*$. Also $R\chi=B^\ell\chi-q^\ell\chi=0$, so the two inclusions hold. Moreover, $\ker S=\chi^\perp$.

An eigenvalue $\lambda_j$ of $B$ gives a power eigenvalue $\lambda_j^\ell$ of $B^\ell$. If this power is not an eigenvalue of $S$, Lemma 3 applies. If it is $0$, the desired bound is immediate. If it is $q^\ell$, then $|\lambda_j|=q$, which is already harmless relative to $\sqrt q$. Applying this to the second eigenvalue modulus gives Eq. 14.

### Dimensional and type check

In generic Lemma 3, $R,S$ act on $\mathbb C^N$. In the application $N=dn$, $\chi\in\mathbb C^{dn}$, and $\chi\chi^*$ is an $nd\times nd$ rank-one matrix. Division by $dn$ makes $\chi\chi^*/(dn)$ the orthogonal projector onto $\chi$.

### Hidden assumptions

- Both range-kernel inclusions are needed. One alone would not force $Rz=0$ on the orthogonal complement used above.
- $B$ need not have real eigenvalues or an orthonormal eigenbasis. The argument uses eigenvalue powers and determinants only.
- The spectral ordering is by modulus, and ties can be handled arbitrarily.

### Intuition

The rank-one matrix $S$ captures the Perron component exactly. Once it is removed, every other eigenvalue is bounded by what $B^\ell$ can do on zero-sum vectors, even though restriction to that subspace cannot be treated as a symmetric spectral decomposition.

### Failure modes

Dropping $\operatorname{im}(S^*)\subset\ker R$ breaks the projection onto $\ker S$. Applying a symmetric-matrix min-max formula directly to $B$ would also be unjustified.

### Numerically checkable

A small random complex matrix satisfying the two range-kernel conditions can be used to compare every new eigenvalue of $S+R$ with the restricted norm. **Not run.** This tests linear algebra only, not the graph theorem.

### Remember this

The proof removes the Perron rank-one direction algebraically, then estimates on $\chi^\perp$. No normality is needed.

## D3. Tangle deletion, telescoping, and the remainder matrices

### Target

Derive the path decomposition behind Proposition 8 and explain exactly why $R_k^{(\ell)}$ is necessary.

### Where it appears

Section 2.3, pages 7 through 11, especially Eqs. 18 through 23 and Figure 2 on page 10.

### Inputs

- **Paper:** $B^\ell_{ef}=\sum_{\gamma\in\Gamma_{ef}^\ell}\prod_{s=1}^\ell M_{\gamma_{2s-1}\gamma_{2s}}$.
- **Paper:** $F^\ell$ restricts to paths whose support has at most one cycle.
- **Paper:** $\underline M=M-(dn)^{-1}\chi\chi^*$.
- **Paper:** On an $\ell$-tangle-free graph, $B^{(\ell)}=B^\ell$.

### Derivation

Start with scalar factors $x_s$ and $y_s$. Define

$$
Z_k=\left(\prod_{s<k}y_s\right)x_k\left(\prod_{s>k}x_s\right).
$$

Then $Z_1=\prod_sx_s$, $Z_{\ell+1}=\prod_sy_s$, and

$$
Z_k-Z_{k+1}
=\left(\prod_{s<k}y_s\right)(x_k-y_k)
\left(\prod_{s>k}x_s\right).
$$

Summing over $k$ gives the identity used in Lemma 7,

$$
\prod_sx_s=\prod_sy_s+
\sum_{k=1}^{\ell}\left(\prod_{s<k}y_s\right)(x_k-y_k)
\left(\prod_{s>k}x_s\right).
$$

Substitute $x_s=M_{\gamma_{2s-1}\gamma_{2s}}$, $y_s=\underline M_{\gamma_{2s-1}\gamma_{2s}}$, so $x_k-y_k=1/(dn)$. Summing over $\gamma\in F^\ell$ yields Eq. 21.

To factor the $k$-sum into matrices, split $\gamma$ at the $k$-th matched pair:

- $\gamma'$ uses indices $1,\ldots,2k-1$,
- $\gamma''$ uses $2k-1,2k,2k+1$,
- $\gamma'''$ uses $2k+1,\ldots,2\ell+1$.

If $\gamma$ is tangle-free, all three pieces are tangle-free. The converse fails. Figure 2 shows separate orange and cyan pieces, each with one permissible cycle, whose union has two cycles. Therefore $F^\ell\subset F_k^\ell$ strictly in general, where $F_k^\ell$ imposes only tangle-freeness on the pieces.

On $F_k^\ell$, the middle one-step path has $(d-1)$ choices. Factoring prefix and suffix gives

$$
\sum_{\gamma\in F_{k,ef}^{\ell}}p_k(\gamma)
=(d-1)\left(\underline B^{(k-1)}
\chi\chi^*B^{(\ell-k)}\right)_{ef}.
$$

The excess paths in $F_k^\ell\setminus F^\ell$ form exactly $R_k^{(\ell)}$. Hence

$$
B^{(\ell)}=\underline B^{(\ell)}
+\frac q{dn}\sum_{k=1}^{\ell}
\underline B^{(k-1)}\chi\chi^*B^{(\ell-k)}
-\frac1{dn}\sum_{k=1}^{\ell}R_k^{(\ell)}.
$$

On an $\ell$-tangle-free graph, all shorter tangle-free restrictions also hold, and $\chi^*B^{(j)}=q^j\chi^*$. If $x\perp\chi$,

$$
\chi^*B^{(\ell-k)}x=q^{\ell-k}\chi^*x=0.
$$

Thus all middle terms vanish on $x$, and

$$
B^\ell x=\underline B^{(\ell)}x
-\frac1{dn}\sum_{k=1}^{\ell}R_k^{(\ell)}x.
$$

Taking operator norms and applying D2 produces Proposition 8.

### Dimensional and type check

A length-$\ell$ matrix entry has $\ell$ matching factors and $\ell-1$ internal $N$ transitions, with $2\ell+1$ half-edge entries. The matrices $\underline B^{(k-1)}$, $\chi\chi^*$, and $B^{(\ell-k)}$ all act on $\mathbb C^{dn}$. Their products have sizes $(k-1)+1+(\ell-k)=\ell$ path steps when the middle one-step factor is counted.

### Hidden assumptions

- The identity $B^{(\ell)}=B^\ell$ uses global $\ell$-tangle-freeness of the realized configuration, not merely an assumption on one path.
- Vanishing of the middle term uses both $\ell$-tangle-freeness and $x\perp\chi$.
- The decomposition is not an assertion that $\underline B^{(\ell)}=\underline B^\ell$.

### Intuition

Centering replaces every random match indicator by a nearly centered weight. Telescoping pays one $1/(dn)$ per location where an uncentered weight is retained. The combinatorial price is that prefix and suffix independence is only approximate: their supports can jointly create a second cycle. The remainder records precisely that non-factorization.

### Failure modes

If one first forms $\underline B^\ell$ and then discards tangled paths, the nice path-product decomposition no longer describes $B^\ell$ on $\chi^\perp$. The paper's order, delete first and center second, is essential. Omitting $R_k^{(\ell)}$ would silently impose the false converse illustrated by Figure 2.

### Numerically checkable

The scalar telescoping identity can be checked on short random vectors. **Not run.** It does not test the nontrivial combinatorial statement about $F_k^\ell$.

### Remember this

The centered term is only half the identity. The union-of-tangle-free-pieces defect is not a technical nuisance that can be assumed away, it defines the remainder.

## D4. Why logarithmic neighborhoods are tangle-free

### Target

Recover Lemma 9's probability scale $1-O(q^{4\ell}/n)$.

### Where it appears

Section 2.4, pages 11 and 12.

### Inputs

- **Paper:** Sequential neighborhood exploration with frontier $D_t$ and collision indicator $\varepsilon_t=\mathbf1_{f_t\in D_{t-1}}$.
- **Paper:** $T=\sum_{j=1}^{\ell-1}d(d-1)^{j-1}=O(q^\ell)$ exploration steps reveal the required neighborhood.

### Derivation

When a matched half-edge $f_t$ lands in the current frontier $D_{t-1}$, exploration closes a cycle instead of discovering only new vertices. Two independent cycles inside the explored neighborhood require at least two such closure events, so $\sum_{t<T}\varepsilon_t\geq2$.

At step $t$, the paper computes the exact conditional collision probability as

$$
\frac{|D_t|-1}{nd-2t-1}.
$$

For the bounded exploration horizon, $|D_t|=O(T)$ and $nd-2t-1$ is of order $n$. There is therefore $q_{\mathrm{coll}}\leq cT/n$ such that every successive conditional collision probability is at most $q_{\mathrm{coll}}$. Independence is not needed to bound the chance of two collisions by

$$
\binom T2q_{\mathrm{coll}}^2\leq T^2q_{\mathrm{coll}}^2.
$$

Taking a union over the $n$ roots gives

$$
\mathbb P(\text{some radius-$\ell$ neighborhood has two cycles})
\leq n\,T^2q_{\mathrm{coll}}^2
=O(T^4/n)=O(q^{4\ell}/n).
$$

### Dimensional and type check

$T$ is a number of explored edges. $q_{\mathrm{coll}}$ is dimensionless. Multiplying $n$ roots by an $O(T^4/n^2)$ two-collision probability per root gives $O(T^4/n)$.

### Hidden assumptions

The asymptotic bound requires $T/n$ to be small enough for the uniform conditional estimate. The revealed half-edge count and frontier size remain $O(T)$. Loop and parallel-edge cycles are included by the exploration logic.

### Intuition

Local neighborhoods look tree-like until $(d-1)^\ell$ becomes a non-negligible power of $n$. One collision is common enough to permit a single cycle, but two collisions at one root have quadratic cost and are rare globally at the selected scale.

### Failure modes

Choosing $\ell$ with $q^{4\ell}$ of order $n$ or larger makes the estimate vacuous. Treating collision indicators as independent is unnecessary and would replace a conditional argument by an unjustified model simplification.

### Numerically checkable

Not needed. The argument is a direct conditional probability estimate and does not rely on a concrete numerical identity.

### Remember this

The exponent $4\ell$ is two powers of $T$ from selecting two collision times and two more from squaring their conditional probability.

## D5. Proposition 11: near-centering along consistent unique edges

### Target

Explain the full estimate

$$
|\mathbb E P|\leq c\,2^b(dn)^{-a}(3k/\sqrt{dn})^{a_1}
$$

and why a simple independence approximation is insufficient.

### Where it appears

Proposition 11 on page 13 and its proof on pages 16 through 19.

### Inputs

- **Paper:** Uniform configuration matching $\sigma$ on $dn$ half-edges.
- **Paper:** Multiplicity and consistency in Definition 10.
- **Paper:** Lemmas 12 and 13.
- **Regime:** $k\leq\sqrt{dn}$.

### Derivation

Write $m_0=dn$ to avoid confusing it with the trace parameter $m$. A distinct required pair typically costs order $1/m_0$ in a uniform matching. This explains the base factor $m_0^{-a}$.

The subtle part is $a_1$. For two distinct half-edges $e\ne f$,

$$
\mathbb E\underline M_{ef}
=\frac1{m_0-1}-\frac1{m_0}
=\frac1{m_0(m_0-1)}.
$$

This small mean does **not** by itself prove a $(k/\sqrt{m_0})^{a_1}$ gain for a long product. Bounding every factor in absolute value discards the sign cancellation that the proposition needs.

Instead, let $T$ index consistent edges appearing once in the centered segment and not afterward. Divide $T$ into:

- $T^*$, whose half-edges either match each other or avoid all other half-edges used by $\gamma$,
- $S$, whose members are entangled by the random matching with other members of $T$.

On $S$, $M_{ef}=0$ and $\underline M_{ef}=-1/m_0$. Hence these factors contribute $m_0^{-|S|}$ with no useful extra cancellation beyond the baseline. The complementary product is written

$$
P=(-m_0)^{-|S|}P^*Q,
$$

where $P^*$ contains the $T^*$ factors and $Q$ all remaining factors.

Condition on $T^*$ and on matching values outside $T^*$. Within $P^*$, if $\hat N$ counts consistent pairs whose endpoints are not actually paired to each other,

$$
P^*=\left(1-\frac1{m_0}\right)^{|T^*|-\hat N}
\left(-\frac1{m_0}\right)^{\hat N}.
$$

The exact conditional law of $\hat N$ has a normalizer $Z$ comparable to $m_0^{|T^*|}$ and produces the alternating moment treated by Lemma 12 with $z=2$. Its conclusion gives, for $\varepsilon=3a/\sqrt{m_0}$,

$$
|\mathbb E[P^*\mid\mathcal F]|
\lesssim(\varepsilon/m_0)^{|T^*|}.
$$

For $Q$, conditional one-factor estimates give:

- at most $1/m_0^*$ for repeated or uncentered relevant pairs,
- at most $2/m_0^*$ for inconsistent centered singletons, producing $2^b$,
- exactly $1/m_0$ on the remaining consistent set excluded from $T^*$.

Here $m_0^*=m_0-2a+1$, comparable to $m_0$ because $a\leq k\leq\sqrt{m_0}$. Lemma 13 makes these conditional bounds multiplicative. Combining everything yields

$$
|\mathbb E P|
\lesssim2^bm_0^{-a}\varepsilon^{a_1}
\mathbb E\varepsilon^{-|T\setminus T^*|}.
$$

The last expectation must be bounded independently. Members of $T\setminus T^*$ require collisions between their half-edges. The paper's union estimate is

$$
\mathbb P(|T\setminus T^*|\geq x)
\lesssim\left(\frac{2a}{\sqrt{m_0}}\right)^x
=\left(\frac{2\varepsilon}{3}\right)^x.
$$

Therefore

$$
\mathbb E\varepsilon^{-|T\setminus T^*|}
\lesssim\sum_{x=0}^{\infty}\varepsilon^{-x}
\left(\frac{2\varepsilon}{3}\right)^x
=\sum_{x=0}^{\infty}\left(\frac23\right)^x
=3,
$$

with constants absorbed into $c$. This is the form of the geometric series required by the preceding estimate. The final negative exponent printed on page 18 is a typographical defect, as discussed in the weak-points file.

Substituting $\varepsilon=3a/\sqrt{m_0}$ and using $a\leq k$ gives exactly the proposition's factor $(3k/\sqrt{m_0})^{a_1}$ after changing constants.

### Dimensional and type check

All factors are real scalars. $a$, $a_1$, and $b$ are counts bounded by $k$. The estimate compares an absolute expectation with a nonnegative bound. One must not replace it by $\mathbb E|P|$, since cancellation inside $\mathbb E P^*$ is essential.

### Hidden assumptions

- Consistency ensures that the consistent pairs in $T$ have disjoint half-edge sets.
- $k\leq\sqrt{m_0}$ controls factorial denominators, normalizers, and collision tails.
- The centered entries are dependent through the global matching. “Approximately independent” is motivation only.
- Figure 1 explains why inconsistent singleton edges need separate treatment. Their repeated half-edges invalidate the disjointness used for $T$.

### Intuition

A generic product of $a$ rare matching constraints costs $m_0^{-a}$. Centering creates alternating signs. On clean consistent singleton edges, the global almost-independence of the matching turns those signs into a second small factor. Inconsistent or heavily revisited edges do not get this gain uniformly.

### Failure modes

- Absolute-value bounds before taking the expectation destroy the essential cancellation.
- Ignoring cross-collisions between consistent pairs produces an unbounded inverse-$\varepsilon$ expectation.
- Removing the short-path regime invalidates the approximation of falling factorials and the lemma's hypotheses.

### Numerically checkable

For very small $m_0$ and prescribed consistent pair sets, one can enumerate all matchings, compute the exact product expectation, and compare it with the formula's scaling. **Not run.** Small examples validate algebra and sign conventions only, not the asymptotic proof.

### Remember this

The extra small factor is a cancellation theorem for a conditional alternating product, not a consequence of each centered entry having small mean.

## D6. Lemma 12: finite differences replace hypergeometric asymptotics

### Target

Reconstruct the mechanism of Lemma 12, including why its bound scales as $(Ck\sqrt{q_{\mathrm{prob}}})^k$.

### Where it appears

Pages 13 through 15, Eqs. 24 through 26.

### Inputs

- **Paper:** $N\sim\operatorname{Bin}(k,p)$ and the alternating-product expectation.
- **Paper parameters:** $z\geq1$, probability parameters $p,q_{\mathrm{prob}}\in(0,1)$, and $zq_{\mathrm{prob}}k^2\leq1$.
- **Paper notation:** $\delta=-zq_{\mathrm{prob}}$ and $\varepsilon=1-p/(q_{\mathrm{prob}}(1-p))$, with $|\varepsilon|\leq1/2$.

### Derivation

Let

$$
f(x)=\mathbb E\prod_{j=0}^{N-1}(zj-1/x).
$$

Expanding the binomial law and factoring powers of $q_{\mathrm{prob}}$ gives

$$
f(q_{\mathrm{prob}})=(1-p)^k
\sum_{t=0}^{k}\binom kt(-1+\varepsilon)^t
\prod_{j=0}^{t-1}(1+\delta j).
$$

The product is expanded by the number $s$ of selected indices,

$$
\prod_{j=0}^{t-1}(1+\delta j)
=1+\sum_{s=1}^{t-1}\delta^sP_s(t).
$$

Each $P_s(t)$ is a sum of products of $s$ distinct indices $j_i$. It is a polynomial in $t$ of degree $2s$ and satisfies

$$
0\leq P_s(t)\leq(t^2/2)^s.
$$

Setting $P_0=1$ and dropping $(1-p)^k\leq1$ leads to Eq. 24,

$$
|f(q_{\mathrm{prob}})|
\leq\sum_{s=0}^{k-1}|\delta|^s
\left|\sum_{t=0}^k\binom kt(-1+\varepsilon)^tP_s(t)\right|.
$$

The central algebraic fact is that if $\deg P<k$,

$$
\sum_{t=0}^k\binom kt(-1)^tP(t)=0.
$$

To prove it, differentiate $(1+x)^k$ at $x=-1$ up to order $k-1$. This gives the identity for falling factorials $(t)_r$. Those falling factorials form a basis of all polynomials of degree below $k$, so linearity gives the claim for every such $P$.

The sum is split at $s\approx k/2$.

For high $s$, no cancellation is needed. Using $|P_s(t)|\leq(k^2/2)^s$ and $|-1+\varepsilon|\leq3/2$,

$$
\left|\sum_t\binom kt(-1+\varepsilon)^tP_s(t)\right|
\leq(5/2)^k(k^2/2)^s.
$$

Thus the high-$s$ part $I$ is controlled by a geometric series in $|\delta|k^2/2=zq_{\mathrm{prob}}k^2/2\leq1/2$, yielding

$$
I\leq2\left((5/\sqrt8)k\sqrt{zq_{\mathrm{prob}}}\right)^k.
$$

For low $s$, expand

$$
(1-\varepsilon)^t=T_{k,s}(t)+R_{k,s}(t),
$$

where $T_{k,s}$ keeps terms through $t^{k-1-2s}$ in binomial-coefficient form. Then $\deg(T_{k,s}P_s)<k$, so the finite-difference identity annihilates its contribution. The remainder satisfies

$$
|R_{k,s}(t)|\leq|\varepsilon|^{k-2s}2^t.
$$

Consequently, each low-$s$ signed sum is at most

$$
3^k|\varepsilon|^{k-2s}(k^2/2)^s.
$$

Summing $|\delta|^s$ times this bound gives a geometric series in $|\delta|k^2/(2\varepsilon^2)$, and

$$
J\leq2\left((3/\sqrt2)k\sqrt{zq_{\mathrm{prob}}}\right)^k.
$$

Finally, $|f|\leq I+J$, and the larger of the two constant bases gives the paper's uniform bound

$$
|f(q_{\mathrm{prob}})|
\leq4\left(3k\sqrt{zq_{\mathrm{prob}}/2}\right)^k.
$$

### Dimensional and type check

$\delta$ has the units of $q_{\mathrm{prob}}$, while $s$ and $t$ are integer indices. The ratio $|\delta|k^2$ is dimensionless. $P_s(t)$ is evaluated at integer $t$ but extended as a polynomial for the finite-difference argument.

### Hidden assumptions

- The condition $zq_{\mathrm{prob}}k^2\leq1$ makes the high-$s$ geometric series converge.
- The lower condition on $zq_{\mathrm{prob}}k^2$ relative to $\varepsilon^2$ makes the low-$s$ geometric estimate work.
- The degree $2s$ of $P_s$, not merely the fact that it is a polynomial, determines the split.

### Intuition

The alternating binomial sum sees none of the polynomial behavior below degree $k$. What remains must involve either high-degree product terms or high-order binomial tail terms. Both carry enough powers of the small parameter $\delta$ to produce the desired exponential-in-$k$ cancellation bound.

### Failure modes

Replacing $(-1+\varepsilon)^t$ by a crude absolute value before using polynomial cancellation loses the mechanism. The proof also cannot simply set $\varepsilon=0$ before controlling $R_{k,s}$.

### Numerically checkable

The exact expectation can be simulated for small $k,p,q_{\mathrm{prob}},z$ and compared with the stated bound and with the finite-difference intermediates. **Not run.** Such a check supports sign and parameter conventions, not the general inequality.

### Remember this

Product expansion creates polynomial degrees $2s$. Finite differences kill low total degree, and geometric tails control everything else.

## D7. High trace and the centered norm bound

### Target

Explain how path-circuit combinatorics proves Proposition 14.

### Where it appears

Section 2.5.1, pages 19 through 25, particularly Figures 3 and 4 and Eqs. 35 through 43.

### Inputs

- **Paper:** $C=\underline B^{(\ell)}$ and Proposition 11.
- **Paper:** Labeling bound Lemma 15, canonical class bound Lemma 16, mean-circuit bound Lemma 17.
- **Paper parameter:** $m=\lfloor\log n/(13\log\log n)\rfloor$.

### Derivation

Since $CC^*$ is positive semidefinite,

$$
\|C\|^{2m}=\|CC^*\|^m
=\lambda_{\max}(CC^*)^m
\leq\operatorname{tr}((CC^*)^m).
$$

Expanding this trace creates $2m$ length-$\ell$ tangle-free paths, alternating between $C$ and $C^*$. Figure 3 depicts them as a closed $2m$-strand circuit. The even-indexed strands are reversed to put their matrix weights in the same symmetric $M$ convention. The endpoint sums give a factor $q(\gamma)\leq(d-1)^m=q^m$.

Let $\gamma\in W_{\ell,m}$ be such a circuit, let $G_\gamma$ be its support, and set

$$
s=|V_\gamma|,\qquad a=|E_\gamma|,\qquad g=a-s+1.
$$

The boundary identifications make $G_\gamma$ connected, so $g\geq0$ is its cycle rank. Three estimates multiply.

**1. Labelings within an isomorphism class.** If $d_v$ is the number of visited half-edges at $v$, the exact number of vertex and local-half-edge label choices is bounded by

$$
(n)_s\prod_v(d)_{d_v}
\leq n^s d^s(d-1)^{2a-s}
=n^s(d(d-1))^s(d-1)^{2g-1}.
$$

The last equality uses $\sum_vd_v=2a$ and $g=a-s+1$. This is Lemma 15.

**2. Canonical representatives.** Isomorphism can rename vertices and local half-edges so that new objects receive the next available canonical label. A first visit creates a spanning tree. An important time uses an excess edge. There are $g$ distinct excess edges.

Figure 4 shows why marking every important time is wasteful. Reusing the unique cycle produces arbitrarily many superfluous times while introducing no new independent cycle. Tangle-freeness on each strand permits one short-cycle mark to absorb all of them. Each strand has at most one short cycling time and at most $g-1$ long cycling times. With at most $h=4\ell m$ half-edges, the resulting generous encoding bound is

$$
|\mathcal W_{\ell,m}(s,a)|
\leq(4\ell m)^{6mg+6m},
$$

which is Lemma 16.

**3. Expected weight of one circuit.** There are $2\ell m$ total matched-pair visits. Let $a'_1$ count distinct edges visited once and $a_2$ those visited at least twice. Then

$$
a'_1+a_2=a,
\qquad a'_1+2a_2\leq2\ell m,
$$

so $a'_1\geq2(a-\ell m)$. Inconsistent singletons can arise only at forest starts or excess-edge discoveries, giving at most $4g+4m$ of them. The number $a_1$ of consistent singletons therefore satisfies

$$
a_1\geq2(a-2g-(\ell+2)m).
$$

Applying Proposition 11 gives Lemma 17,

$$
|\mu(\gamma)|
\leq c^{g+m}(dn)^{-a}
\left(\frac{(6\ell m)^2}{dn}
\right)^{(a-2g-(\ell+2)m)_+}.
$$

Now multiply the three estimates and substitute $a=s+g-1$. The core powers simplify as

$$
n^s(d(d-1))^s(d-1)^{2g-1}(dn)^{-a}
=\frac{dn}{q}(d-1)^s
\left(\frac{q^2}{dn}\right)^g.
$$

Up to constants absorbed throughout, the total sum becomes

$$
S\lesssim n(c\ell m)^{6m}
\sum_{s,g}(d-1)^s\eta^g
\varepsilon_0^{(s-g-1-\ell'm)_+},
$$

where

$$
\eta=\frac{(c\ell m)^{6m}}n,
\qquad
\varepsilon_0=\frac{(6\ell m)^2}{dn},
\qquad
\ell'=\ell+2.
$$

The extra consistent-singleton exponent is precisely what makes the sum over large $s$ controllable.

For the displayed $m$, and $\ell\leq\log n$,

$$
\ell m=O((\log n)^2),
\qquad
\eta\leq n^{-1/13+o(1)},
\qquad
\varepsilon_0=o(1).
$$

The sum is divided into three regions:

- $S_1$, with $s\leq\ell'm$: no cancellation exponent is needed once $\varepsilon_0^x\leq1$, and $\sum_{s\leq\ell'm}q^s=O(q^{\ell'm})$. The $g$-sum has ratio $\eta=o(1)$.
- $S_2$, with large $s$ and small $g$: summing first over $g$ has ratio $\eta/\varepsilon_0$. The remaining $s$-series has ratio $q\eta$, summing finite geometric series while retaining a factor $q^{\ell'm}$.
- $S_3$, with large $s$ and large $g$: the $g$-sum begins at $g=s-\ell'm$, providing $\eta^{s-\ell'm}$ and making the remaining $s$-series geometric with eventual ratio below $1$.

Together they prove

$$
S\leq n(c\ell m)^{6m}q^{\ell'm},
$$

with $c$ adjusted. Since $q^{\ell'm}=q^{2m}q^{\ell m}$ and the endpoint and other fixed-power factors are absorbed,

$$
\mathbb E\|C\|^{2m}\leq n(c\ell m)^{6m}q^{\ell m}.
$$

Markov's inequality then gives

$$
\mathbb P\left(\|C\|\geq n^{1/(2m)}(c\ell m)^3q^{\ell/2}x\right)
\leq x^{-2m}.
$$

With $m\sim\log n/(13\log\log n)$, the factor $n^{1/(2m)}$ is a fixed power of $\log n$, approximately $(\log n)^{6.5}$ before rounding. Since $c\ell m$ is polylogarithmic, every fixed $x$ growing polylogarithmically makes the norm loss another fixed polylogarithm and the probability arbitrarily small. The paper states exponent 15.

### Dimensional and type check

$2m$ strands of length $\ell$ give $2\ell m$ matched-pair visits. $s$ and $a$ count support objects, not visits. The identity $g=a-s+1$ is precisely connected cycle rank. The $1/(dn)$ expectation scale cancels labeling powers of $n$ in every final geometric ratio, so no uncontrolled positive power of $n$ remains beyond the trace's overall factor $n$.

### Hidden assumptions

- Every constituent path is tangle-free. This is what controls long cycling marks.
- Isomorphism preserves all matrix weights $\mu(\gamma)$.
- $2\ell m\leq\sqrt{dn}$ is needed to apply Proposition 11 and holds with much room at the chosen scales.
- The norm-to-trace inequality works because $CC^*$ is positive semidefinite, not because $C$ is normal.

### Intuition

Labeling supplies roughly $n^s$, matching probability removes $(dn)^a$, and entropy supplies $(d-1)^s$ times an excess-edge cost. Most terms therefore have a $1/n$ excess-edge discount. Near-centering supplies a further discount when the support has many vertices relative to cycle rank and strand endpoints. Polylogarithmic entropy remains after taking a $1/(2m)$ root.

### Failure modes

- Letting strands become tangled invalidates the compression of repeated cycling times.
- Ignoring inconsistent edges overestates how often Proposition 11 grants extra cancellation.
- Choosing $m$ too large breaks the path-length hypothesis. Choosing it too small leaves an excessive factor $n^{1/(2m)}$.
- Bounding $\|C\|^{2m}$ directly without $CC^*$ would lose the positive-semidefinite trace inequality.

### Numerically checkable

The exponent simplification after $a=s+g-1$ and the normalizer $(c\ell m)^{6m}/n$ can be evaluated on logarithmic test values. **Not run.** A numeric check would not test injectivity of the path encoding, which is the substantive point.

### Remember this

The final norm bound is a product of labeling entropy, cycle-rank enumeration, and conditional matching cancellation. Figures 3 and 4 describe the first two, while Proposition 11 supplies the third.

## D8. Final regular-graph assembly and rates

### Target

Derive Theorem 2, then Eq. 13 and Eq. 2, while identifying the exact roles of $\ell$ and $m$.

### Where it appears

Section 2.6 on page 29 and the model conversion in Section 2.2.

### Inputs

- **Paper:** Lemma 9 and Propositions 8, 14, and 18.
- **Paper:** $0<\kappa<1/4$ and $\ell\sim\kappa\log_qn$.

### Derivation

Set

$$
J=\|\underline B^{(\ell)}\|
+\frac1{dn}\sum_{k=1}^{\ell}\|R_k^{(\ell)}\|.
$$

Since $q^\ell=n^{\kappa+o(1)}$, the tangle probability is

$$
O(q^{4\ell}/n)=O(n^{4\kappa-1+o(1)})=o(1).
$$

On the tangle-free event, D2 and D3 give $|\lambda_2|\leq J^{1/\ell}$. With high probability, Propositions 14 and 18 bound

$$
J\leq(\log n)^{15}q^{\ell/2}
+\frac{(\log n)^{30}}{dn}q^\ell.
$$

The second term is at most $(\log n)^{30}n^{\kappa-1+o(1)}=o(1)$ because $\kappa<1/4<1$. Therefore

$$
J^{1/\ell}
\leq q^{1/2}(\log n)^{15/\ell}(1+o(1))
=\sqrt q\left(1+O\left(\frac{\log\log n}{\log n}\right)\right).
$$

For any fixed $\varepsilon>0$, this is eventually strictly below $\sqrt q+\varepsilon$, proving Theorem 2.

For the stronger tail, choose $0<\kappa<a/4$, so the tangle event has probability $O(n^{-a+o(1)})$. Remarks 1 and 2 strengthen each norm estimate to failure probability $O(n^{-a})$ by enlarging polylogarithmic constants. Choosing an additive non-backtracking allowance $\eta=c\log\log n/\log n$ with $c$ large enough absorbs every polylogarithmic $1/\ell$ root. This establishes Eq. 13. D1 then gives Eq. 2, followed by conditioning on simplicity.

The proof's displayed moment parameters satisfy

$$
\ell m=O((\log n)^2),
$$

so $2\ell m=o(\sqrt n)$ and $6\ell m=o(\sqrt n)$. Thus the matching-product hypotheses are not the bottleneck.

**Source correction:** Remark 4 on page 29 prints $\varepsilon=c\log n/\log\log n$. That expression grows and is incompatible with the immediately preceding root calculation and with Eq. 13. The logically required choice is $\eta=c\log\log n/\log n$. This is a local typographical repair, not a new mathematical assumption.

### Dimensional and scale check

- $\ell$ is a path length and controls both the eigenvalue root and local tangle-freeness.
- $m$ is a trace power and controls only moment tails.
- $q^\ell$ is polynomial in $n$ when $\ell\sim\kappa\log_qn$.
- $(\log n)^{c/\ell}=1+O(\log\log n/\log n)$ for fixed $c$ and $\ell\asymp\log n$.

### Hidden assumptions

$d$ is fixed and $\kappa$ is strictly below $1/4$, leaving a polynomial margin in both the tangle probability and the $1/n$ remainder discount. Quantitative probability exponents require high-probability versions of both norm propositions, not just their whp statements.

### Intuition

Taking an $\ell$-th root turns a polylogarithmic operator-norm overestimate into $1+O(\log\log n/\log n)$. Choosing $\ell$ of order $\log n$ is therefore not optional. Yet $\ell$ cannot be too large, or local tangles cease to be rare.

### Failure modes

- $\ell=o(\log n)$ does not suppress polylogarithmic trace losses to $1+o(1)$.
- $\ell$ with $\kappa\geq1/4$ loses the stated tangle-free probability bound.
- Dropping the $1/(dn)$ factor would leave a remainder of order $q^{\ell}$, whose $\ell$-th root is $q$ rather than $\sqrt q$.
- Using Remark 4's printed growing $\varepsilon$ literally would not establish Eq. 13.

### Numerically checkable

The scale identities $q^\ell=n^{\kappa+o(1)}$ and $(\log n)^{c/\ell}=1+O(\log\log n/\log n)$ can be evaluated directly. **Not run.** These are elementary asymptotics, not evidence for the probabilistic norm bounds.

### Remember this

There are two logarithmic scales with different jobs: $\ell$ takes the spectral root, while $m$ purchases high-probability moment control.

## D9. Random lifts: new spectrum and base-path growth

### Target

Explain the changes needed to prove Theorem 23 with threshold $\sqrt{\rho_1}$.

### Where it appears

Sections 3 and 4, especially Definition 22, Eqs. 50 through 56, Eq. 67, Lemma 31, and Section 4.4.

### Inputs

- **Paper:** A finite connected base graph with $|E|>|V|$ and independent uniform edge-fiber permutations.
- **Paper:** $B_nH\subset H$, $B_n^*H\subset H$, and $B_n|_H=B$.
- **Paper:** Propositions 26, 28, 29, and 33, together with Lemma 27.
- **Paper:** For $\rho>\rho_1$, $\|(B^*)^k\delta_e\|_1\leq c_\rho\rho^k$.

### Derivation

First remove inherited base behavior. A vector $x\in H$ is constant on every directed-edge fiber $\{(e,i):i\in[n]\}$. The definition of an $n$-lift makes $B_n$ preserve $H$, and its adjoint also preserves $H$. Restriction to $H$ reproduces the base matrix $B$. Therefore $H^\perp$, of dimension $nr-r$, contains precisely the new spectrum. Applying Lemma 3 with $S=PB_n^\ell P$ yields

$$
|\lambda_1|^\ell
\leq\sup_{x\in H^\perp,\ \|x\|_2=1}\|B_n^\ell x\|_2.
$$

Fiber centering is now

$$
\underline M_e=M_e-\frac{\chi\chi^*}n.
$$

On $H^\perp$, each such matrix acts only after summing its row or column against a zero-sum fiber vector. The same delete-first telescoping mechanism as D3 produces Proposition 26. Figure 2 still explains the remainder. Figure 5 makes the fiber permutations concrete.

For expected path weights, group pairs of half-edges by their base directed edge. Since $\sigma_{\iota(e)}=\sigma_e^{-1}$, an undirected base edge contributes only one independent permutation. The expectation factors across those base edges, and Proposition 28 supplies the same form of bound as Proposition 11 with $n$ replacing $dn$:

$$
|\mu(\gamma)|\leq c^{g+m}n^{-a}
\left(\frac{(6\ell m)^2}{n}
\right)^{(a-2g-(\ell+2)m)_+}.
$$

The decisive new count is Lemma 31. Isomorphism may permute only fiber indices over each base vertex, so an isomorphism class has at most $n^s$ elements, with no regular-half-edge labeling factor like $(d(d-1))^s$. The price is that base projections now vary and must be encoded.

To bound base projections, let $s_q^i$ count new vertices introduced between successive important times. First-exit segments have total new-vertex count

$$
\sum_{i,q}s_q^i=s-1.
$$

For each base half-edge $e$, $\|(B^*)^{s_q^i}\delta_e\|_1$ counts the possible projected non-backtracking segments of the required length. Eq. 67 bounds all of these by $c_\rho\rho^{s_q^i}$. Multiplication gives

$$
\prod_{i,q}\|(B^*)^{s_q^i}\delta_e\|_1
\leq c_\rho^{2m(g+1)}\rho^{s-1}.
$$

The short/long/superfluous cycle classification from Figure 4 controls the remaining mark positions. Absorbing fixed exponents into $c=c(\rho,G)$ gives

$$
|\mathcal W_{\ell,m}(s,a)|\leq\rho^s(c\ell m)^{8mg+10m}.
$$

Now multiply $n^s$, $\rho^s$, mark entropy, and $n^{-a}$. With $a=s+g-1$, exactly as in D7, the leading identity becomes

$$
n^s\rho^s n^{-a}
=n^{1-g}\rho^s.
$$

Excess $g$ therefore carries an $n^{-g}$ discount, while new-vertex growth supplies $\rho^s$ instead of $(d-1)^s$. The same geometric-sum argument gives Proposition 29,

$$
\|\underline B_n^{(\ell)}\|
\leq(\log n)^{20}\rho^{\ell/2}\quad\text{whp}.
$$

The modified cyclic support for remainders gives the same discount without a global trace factor of $n$, leading to Proposition 33,

$$
\sum_k\|R_k^{(\ell)}\|
\leq(\log n)^{40}\rho^\ell\quad\text{whp}.
$$

Finally choose $\ell\sim\kappa\log_{d-1}n$ with $0<\kappa<1/4$ and $\rho\leq d-1$ such that

$$
\rho>\rho_1,
\qquad\sqrt\rho\leq\sqrt{\rho_1}+\varepsilon.
$$

Lemma 27 is unchanged at scale $O((d-1)^{4\ell}/n)$. If

$$
J_n=\|\underline B_n^{(\ell)}\|
+\frac1n\sum_k\|R_k^{(\ell)}\|,
$$

then whp

$$
J_n\leq(\log n)^{20}\rho^{\ell/2}
+\frac{(\log n)^{40}}n\rho^\ell
=(\log n)^{20}\rho^{\ell/2}+o(1),
$$

because $\rho^\ell\leq(d-1)^\ell=n^{\kappa+o(1)}$. Hence

$$
J_n^{1/\ell}
=\sqrt\rho\left(1+O\left(\frac{\log\log n}{\log n}\right)\right)
\leq\sqrt{\rho_1}+\varepsilon+o(1).
$$

This proves the threshold with $2\varepsilon$ in the paper's final display, then rename $\varepsilon$ as usual. For a $d$-regular base, $\rho_1=d-1$, so D1 converts this into Corollary 24.

### Dimensional and type check

The base $B$ is $r\times r$, $M_e$ is $n\times n$, and $B_n$ is $nr\times nr$. $H$ has dimension $r$ and $H^\perp$ has dimension $nr-r$. The scalar $\rho$ is a non-backtracking path-growth rate, so it enters as $\rho^s$ and its square root appears only in the final spectral scale, exactly as $\sqrt{d-1}$ did in the regular case.

### Hidden assumptions

- Independence is across undirected base edges, not across all directed half-edges individually.
- The base is fixed, so finitely many starting vectors $\delta_e$ can be covered by one constant $c_\rho$.
- $\rho$ is strictly greater than $\rho_1$ throughout the estimates. Taking the limit $\rho\downarrow\rho_1$ is deferred until the end.
- $|E|>|V|$ gives $\rho_1>1$ and maximum degree at least $3$, consistent with Lemma 27.
- Theorem 23 is for non-backtracking eigenvalues. Irregular adjacency conversion lacks the regular Ihara-Bass dictionary used for Corollary 24.

### Intuition

The number of ways to label new lift vertices grows like $n^s$, while each distinct required fiber permutation constraint costs $1/n$. The remaining base-projected non-backtracking entropy is governed by $\rho$. Thus everything from the regular proof survives after replacing the regular tree's branching growth by the base universal cover's non-backtracking growth.

### Failure modes

- Centering on vertex fibers rather than directed-edge fibers would not isolate the correct inherited spectrum.
- Setting $\rho=\rho_1$ from the beginning would not justify a uniform polynomial bound of the stated form from Gelfand alone.
- Replacing $\rho$ by maximum degree minus one everywhere would lose sharpness for irregular base graphs.
- Invoking Corollary 24 for irregular adjacency matrices would exceed the paper's theorem.

### Numerically checkable

For a fixed small base graph, one can compare $(B^*)^k\delta_e$ counts with $c_\rho\rho^k$ for selected $\rho>\rho_1$, and independently enumerate Figure 5's lifted adjacency matrix. **Not run.** Such calculations illustrate the growth convention but do not establish the trace proof.

### Remember this

The regular argument is not merely copied with different names. Its branching factor is replaced by weighted base-path entropy $\rho^s$, while $n^{-g}$ remains the excess-edge discount that closes the sums.
