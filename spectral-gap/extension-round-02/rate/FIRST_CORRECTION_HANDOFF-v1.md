# Signed-correction handoff

Task: SG-E1 follow-up. Sender: rate investigator. Recipient: problem 21 integrator.

The starting evidence is the accepted positive partition proof and the separately frozen RATE-1 proof. Prior exposure included those proofs. No saddle or integrator attempt was read before this result was frozen.

## Proposed result CORR-1

For $k/\sqrt N\to c>0$, with $\epsilon=k\bmod2$ and the exact parity normalization from the manuscript,

$$
N^{1/4}\left(\frac{R_k}{e^{k^2/(4N)}H_k}-1\right)
\longrightarrow
\frac{2\epsilon-1}{2}\sqrt c+\frac{2}{15}c^{5/2}
$$

along each fixed parity. The frozen proof also states a finite-parameter first-correction expression that permits mixed parities.

At $c=1$, the limits are $-11/30$ for even orders and $19/30$ for odd orders. Therefore the uniform $N^{-1/4}$ rate in RATE-1 is optimal in order. The even leading coefficient vanishes at $c=\sqrt{15}/2$, and no further rate is claimed at that exceptional point.

## Frozen proof and mechanism

`first-correction-v1.md` has SHA256 `71148f873f45e5c6db0e7535583398712febc6d153874928b1d91701395f2c42`.

The proof retains fluctuations in the quadratic pair-depletion exponent, the cubic term in its logarithm, and exactly one five-element block. Higher blocks and repeated five-element blocks have smaller total weight. Exact parity conditioning supplies the sign-changing term. All remainder controls are given before the coefficients are combined.

## Executed checks

`check_first_correction.py` verifies seven symbolic coefficient identities and computes 24 numerical examples through $N=10^{10}$ at 80 decimal digits. Results are in `first-correction-checks-v1.json`.

For $N=10^{10}$ and even $k=100000$, the observed scaled error is approximately $-0.366983$, approaching $-11/30$. For the neighboring odd order, it is approximately $0.631064$, approaching $19/30$.

One checker-only defect was corrected before export: structural equality rejected an expanded expression and an equivalent factored expression. Their simplified difference was zero. The checker now tests that simplified difference. The frozen proof was unaffected, and the corrected full run passed. This finding was reported to the integrator for shared issue tracking.

These calculations corroborate finite identities and examples. The universal asymptotic and optimality conclusions depend on the written proof, not the observed convergence.

## Next action and limitations

Propose CORR-1 as proved in writing, awaiting independent review. Request an independent reconstruction of Sections 4 through 7 against the frozen hash, especially the cubic logarithm sign, the opposite triple parity for one five-element block, and the conversion from $K$ to the limiting scale.

No historical priority, optimal numerical constant in RATE-1, formal verification, or result for unbounded $k/\sqrt N$ is claimed. Existing frozen packets are unchanged. The current investigation stops with a complete signed correction and a clean rate-optimality consequence rather than pursuing an unreviewed further coefficient.
