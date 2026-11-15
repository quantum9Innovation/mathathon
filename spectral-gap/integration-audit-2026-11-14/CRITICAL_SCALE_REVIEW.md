# Integration review of the critical-scale extension

Reviewed proof: [critical-scale-v1.md](../audit-2026-11-14/critical-scale-v1.md), SHA256 ea79cdd43ae88afcc2ca5008e4c4a95e50e12b37ca87904db25ce7cdad0b5596.

Decision: accept as SG-05 at this revision. This is a written mathematical review, without a formal-verification claim or a literature-priority certificate.

The integrator reconstructed the normalized parity recurrences and the comparison equations before reading the completed independent review. With e_m=R_(2m) and o_m=R_(2m+1), the first step gives N/(N-1) and N^2/((N-1)(N-2)). The auxiliary o_0 has coefficient zero, so no undefined normalized first moment is used.

The power-series comparison has parameter u=x^3/N. Its first derivatives are bounded by a constant times x^2/N and its second derivatives by a constant times x/N on u<=T. The apparent 1/x singularity in the odd equation is removable, since E_N-O_N is of order x^3/N. Subtracting the exact even coefficient from 16m^2/(3N) gives an error of order m/N+m^3/N^2. The odd residual has the exact cancellation coefficient -3/[m(2m+1)]. These identities make both local residuals of order m/N, uniformly under the stated hypotheses.

The recurrence is positive. Its row-sum factors are bounded by 1+12m^2/N and 1+4m^2/N, and the coefficient coupling the new even value into the odd step is at most two. The accumulated product is at most exp(16T). Summing the residuals therefore gives the claimed C_T M^2/N bound. No extrapolation from numerical convergence enters this inference.

For even k, the squared hyperbolic argument is exactly 4k^3/(9N). For odd k, replace k by k-1, with an error tending to zero on a bounded critical scale. In the small-error regime, growing k is essential to make the comparison error negligible relative to k^3/N. Along odd k=2m+1 and N=m^4, the ratio of the excess to k^3/N tends to 2/27, proving that a larger universal lower-bound constant cannot hold.

The [independent review](../cross-review-2026-11-14/critical-scale-by-algebra.md), SHA256 d9fc48eb1a6f31db229da13d94fb23494bc4450e9f44058cadfc8dc77c6bd517, separately reconstructs these steps and supplies explicit possible uniform constants. Its bounded numerical calculations are corroboration. They are not premises of acceptance.

The sourced recurrence remains attributed to Collins and Nagatsu. SG-05 adds the uniform comparison argument and its consequences within this packet. A targeted source check does not establish historical priority. The extension neither re-audits the imported finite-defect results nor replaces the separate proof of the mixed-product estimate.
