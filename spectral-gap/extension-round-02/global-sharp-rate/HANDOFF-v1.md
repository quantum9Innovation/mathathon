# Sharp global rate handoff

Task: GSR-1. Frozen revision 1, November 15, 2026 UTC.

Result: the existing GLOBAL-1 approximation has exact uniform error order N^(-1/3). The packet proves a uniform critical profile over every order from 2 through N, with opposite parity signs, and a sharp limiting supremum constant of approximately 0.395496270090508. The unique maximizing critical scale is approximately 1.16540187318375 and is attained asymptotically by odd orders.

The profile coefficient is obtained from the conditioned triple count. Four-block and common quadratic terms cancel. Both real saddle contributions are retained below the square-root scale. The finite hyperbolic estimate controls fixed orders, and the accepted complex coefficient bound controls every order above the square-root scale, including k=N.

Proof: `proof-v1.md`.

SHA256: `c3f5bd362a005688d28a6ac1f5440188aa0b8f4a802de269b17c7d4e08e96fcf`.

Finite corroboration: three exhaustive scans over all allowed orders, at N=512, 4096, and 32768, and 24 additional two-parity profile checks through N=10^9. The maximizing orders in the exhaustive scans are odd. `checks-v1.json` records these results and `check_global_sharp.py` reproduces them. The proof does not rely on computation.

Status: proved in the frozen packet, awaiting independent review. A draft reconstruction checked the algebra, both tail arguments, and the maximizing equation before freezing. No maintained manuscript, earlier frozen packet, or canonical ledger was edited.

Prior exposure: the candidate profile, maximizing equation, and exploratory decimal constant were supplied before the attempt. They were rederived and checked. The accepted base, rate, saddle, global, and classical-integral packets were already known. No historical firstness is claimed.

One next action: assign an independent review of this exact proof hash, especially the uniform real saddle bounds, adjacent-degree normalization, and the two-tail passage to the full supremum, before canonical integration.
