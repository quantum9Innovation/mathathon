# Reconstruction of the independent polynomial proof

November 15, 2026. Reviewer: root. Reviewed source: [chebyshev-proof-v1.md](../probability/chebyshev-proof-v1.md), SHA256 d9265e631ea99465eb243aaeecda7ad5a6d27c92b977ebe3b4cf185ac411a011.

Verdict: accepted. No mathematical correction is required.

Exposure: the reviewer authored the separate nonbacktracking upper proof and received the polynomial argument's proposed outline. The reviewed file was read only after it was frozen. This is distinct proof reconstruction, not blind review.

The stronger input is real and necessary for this route. I directly re-read equation (2) on printed page 1394 of the retained published Bordenave source. It states the two-sided nontrivial spectral bound with error c(loglog(n)/log(n))^2 and failure at most n^(-xi), for fixed 0<xi<1. It applies to the uniform simple labelled fixed-d model. The source does not supply the marked estimate itself.

The Chebyshev expansion has the correct Delta normalization. Evaluation at d gives p_r(d)=(r+1+sum tau^(2k))/Delta. Its linear growth retains the stationary correction. Differentiating log tau gives d/[Lambda sqrt(d^2-Lambda^2)], so epsilon_n log(n)->0 provides the uniform q^(-r) squared approximation rate. A fixed-width spectral interval alone would not justify that rate.

Polynomial locality is correctly applied to actual graph distance. The centered matrix W_r has operator norm bounded by the approximation error on the complementary spectrum. Its row squared mass and the exact stationary subtraction imply the far-row bound with r^2/n, without an extra number-of-columns factor on the W_r term.

Exchangeability is used under the full graph law with the label-invariant spectral event inside the expectation. It justifies each fixed ordered marked pair and the Frobenius sum. The close-pair probability is separately bounded by the maximal ball size and a union bound. The chosen floor radius simultaneously makes both errors proportional to sqrt(m^3/n), with no hidden logarithmic growth restriction.

The previous diagonal single-walk bound and derivative theorem are valid outside the earlier sufficient collective range as finite-n inequalities. Their use here is legitimate. The deterministic diagonal remainder, k=0 stationary subtraction and exceptional spectral event are accounted for. This establishes the displayed quantitative error bound and every stated fixed derivative consequence.

The proof is independent of the new two-walk estimate, although it shares the earlier diagonal and derivative estimates. It does not independently establish the graph-level transfer or necessity. Its quantitative host input must remain cited whenever this route is used.
