# Global exact-denominator handoff

Sender: rate investigator. Recipient: problem 21 integrator.

The integrator supplied the direction after the independent saddle review was frozen: enlarge the coefficient lemma to $x\le1$ and retain $D_k$ exactly. This investigation read no new integrator proof before freezing its own derivation. It had already reviewed the saddle proof and had written RATE-1 and CORR-1.

## Proposed theorem GLOBAL-1

With $K=k-(k\bmod2)$, $x=\sqrt{K/N}$ and the exact parity-sensitive $H_k$, define

$$
\mathcal A_{N,k}=D_kH_ke^{Nq(x)}(1+x)^{(k\bmod2)-1/2},
$$

where $D_k=N^k/(N)_k$ and

$$
q(x)=x+(x^2-1)\log(1+x)-x^2/2-2x^3/3.
$$

The proof establishes

$$
\sup_{2\le k\le N}|R_k/\mathcal A_{N,k}-1|=O(N^{-1/4}).
$$

Above $\sqrt N$, the stronger uniform bound is $O(K^{-1}+e^{-\lambda/8})=O(N^{-1/2})$. The lower-range patch has an explicit bound in terms of the accepted RATE-1 constants.

## Endpoint and scope

The coefficient integral stays within radius $r\le1/2$ even at $k=N$. The exact denominator is never approximated in the large-order proof. Both endpoint parities are checked separately, with the literal odd value $K=N-1$ retained.

A simple consequence in the original moments is

$$
a_N(N)=\frac1{2N!}(1+O(N^{-1})).
$$

The corresponding normalized endpoint formulas have distinct even and odd prefactors, displayed in the proof. No historical novelty or best possible global error rate is claimed.

## Frozen outputs and checks

`proof-v1.md` has SHA256 `35d5d3e26de77e71dd666996d0e936c616abcce3a4f83ba2acb2164ea6ea9566`.

`check_global.py` and `checks-v1.json` contain 435 exact inclusion-exclusion comparisons for the normalization and 12332 numerical evaluations of the global formula. All orders were evaluated for the listed sizes through 4097. Larger sizes through 100001 use selected orders including both endpoints and the crossover. The calculations used 80 decimal digits.

At the endpoint, the relative errors of the explicit asymptotic formulas are approximately $-2.500006\times10^{-6}$ at even $N=100000$ and $5.000003\times10^{-6}$ at odd $N=100001$. These are corroborating finite observations, not proof of the uniform theorem.

No implementation or mathematical defect was found during this packet. Existing frozen proofs and reviews were not changed.

## Requested disposition

Propose GLOBAL-1 as proved in writing, awaiting independent review. Request review of the derivative constants at $r=1/2$, the second-peak factor $e^{-\lambda/8}$, the exact odd normalization at $K=N-1$, the explicit low-order comparison, and both endpoint prefactors.

The direct dependencies are the exact partition identity, the enlarged analytic coefficient lemma proved here, and RATE-1 for the low-order patch. The previous sublinear saddle theorem is background for the method, not an authorization to use its smaller parameter range beyond its proved scope.

Stopping reason: the supplied direction yields a complete all-order theorem, endpoint analysis and corroboration. Further optimization is deferred to independent review and manuscript integration.
