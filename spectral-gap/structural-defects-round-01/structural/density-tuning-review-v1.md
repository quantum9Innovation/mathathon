# Review of noncoincidence and integer tuning

Date: November 15, 2026. Reviewer: structural workstream. Revision 1.

Target: `../probability/density-and-tuning-v1.md`, SHA256 `cf3e7ef384fad52dd78f22fbdb2d121a8c99049f4736012c4a7dfeae14a91098`.

Verdict: accepted as a paper result at this exact revision. No open finding was identified. This addendum follows the three-paper chain review in `next-scale-probability-review-v1.md`, SHA256 `0f43fa36dbd853f207ecbee78aa0e60676754bb2a02215e471f48aafcb97dbad`.

Exposure: the reviewer had read and independently reconstructed the preceding collective law and self-energy chain. The integrator assigned the exact density and tuning file. No live root graph synthesis was read before this addendum was frozen.

The representation after fixing P_0 is correct. The remaining positive-offset centered series has summable variance. The negative-offset sum has finite Poisson intensity and bounded jumps. The characteristic-function modulus therefore has the stated nonnegative exponent.

For X=|t|kappa/theta>=2 and k=floor(log_2 X), one has k>=1, 2^k<=X<2^(k+1), and 1/2<=X/(2^k+1)<2. Thus 1-cos(t a_k) is at least 1-cos(1/2). The selected intensity is at least

\[
 \frac{3\theta}{4\sqrt2}\frac{|t|\kappa}{2\theta}
 =\frac9{32}|t|.
\]

This proves the exponential Fourier bound with the displayed constant. It uses a positive index and survives fixing P_0, or any fixed finite set of counts. Every polynomial multiple of the characteristic function is integrable. Fourier inversion and differentiation under the integral give a bounded smooth density and hence no atoms.

The negative-ordering argument uses finitely many zero Poisson counts, each with positive probability. Their accumulated deterministic centered drift tends to negative infinity. The independent residual centered tail has variance tending to zero, and the negative-offset compound Poisson sum has a positive probability of being zero. These events yield positive probability below every real threshold. For the positive direction, one unbounded Poisson count with positive coefficient and an independent finite remainder suffice. These are positive probabilities of both orderings against every fixed scalar. The argument need not assert positivity of the density at every point.

The integer construction preserves the exact scaling. The nearest-even rounding error in n_j is bounded, giving a relative error O(1/n_j) in s_j. Since q_j tends to one, the fractional logarithm remains near 1/2 and r_j=j eventually. Hence w_j=kappa q_j+O(1/n_j). Substitution yields

\[
 \beta_j=\beta q_j+\frac{\kappa^2}{2}j(1-q_j)
                +O(1/(n_js_0)).
\]

Here j(1-q_j)=O(j squared s_0) tends to zero and n_js_0 tends to infinity. Thus beta_j tends to the prescribed beta. Rounding m_j only changes the limiting critical ratio, which still tends to c by the displayed identity involving m_j squared/(2 times 4^j q_j squared). Even n_j are admissible cubic sizes eventually, and m_j<n_j.

The preceding first-order phase and logarithmic retunings follow from the same estimates. They do not determine the finite next parameter beta. No integer obstruction remains for any prescribed finite beta.

This acceptance proves noncoincidence of the limiting scalar coefficients and availability of the size sequences. The exact graph root count, ordering and physical eigenvector selection remain a separate synthesis obligation.
