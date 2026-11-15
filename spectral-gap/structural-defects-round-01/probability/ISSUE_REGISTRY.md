# Structural defect probability issues

November 15, 2026.

| ID | Status | Finding or remaining obligation |
| --- | --- | --- |
| SD-PROB-01 | resolved in candidate statement | Integer centering by r makes the endpoint phase-one law a translate by minus one of the phase-zero law. Adding the fractional phase restores an endpoint-invariant centered law. |
| SD-PROB-02 | explicit proof boundary | The small tail variance is unconditional for the sampled nonbacktracking quadratic. It is not an L2 estimate for the graph resolvent after conditioning on the host-gap event. The transfer uses convergence in probability and keeps that exceptional event separate. |
| SD-PROB-03 | pending after first freeze | An order-s effective graph law requires an explicit normalization and complementary-space correction. No generic avoided crossing or nonzero signed coupling is assumed. |

Prior frozen proofs remain unchanged. This directory owns probability outputs only.

## SD-PROB-04: A generic order-s avoided crossing is not supported

Status: resolved by a new paper argument, awaiting separate review. The actual signed off-diagonal, including its complementary-space correction, is o_P(s) in signed-coupling-v1.md. A smaller-scale coincidence may still need further analysis. The collective self-energy at order s remains to be identified.

## SD-PROB-05: The raw collective quadratic is not the final scalar law

Status: resolved by collective-self-energy-v1.md, awaiting separate review. The collective complementary correction has the same scale and is coupled to the same pair process. Their heavy large-jump contributions cancel. The combined scalar has bounded jump kernel kappa*w/(kappa+w), while treating the two inputs as independent would give the wrong law.
