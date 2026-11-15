# Independent reconstruction of the cubic-scale theorem

Reviewed file: [sharp-scaling-v1.md](../audit-2026-11-14/sharp-scaling-v1.md).
SHA256: fd7383e644319b6d6f9755c3412616923da5e2d9cf7d31bab94d67836d2bb0ec.

Verdict: the necessary-and-sufficient relative-accuracy statement follows from the written inequalities. No mathematical gap was found. A separate cross-review and limited priority search remain part of selection.

## Exact reconstruction

Substitution of the parity-dependent leading terms into the original recurrence gives the coefficients in S7 and S8. For even degree, the coefficients are N/(N-2m+1) and 4(2m-1)(2m-2)/(3(N-2m+1)). Their sum minus one is exactly the stated positive inhomogeneous term. For odd degree, the coefficient sum is N/(N-2m), giving the stated inhomogeneous term 2m/(N-2m).

The initial excess is 1/(N-1). All subsequent coefficients and inhomogeneous terms are nonnegative. Dropping the odd excess term from the even recurrence therefore gives a valid lower bound. Summing its remaining increments gives the cubic polynomial in S2, including its m=1 endpoint.

The polynomial in S3 satisfies S9 exactly. Using the two positive odd-recurrence coefficients proves the odd bound by induction. Its difference from 2(2m+1)^3/27 is positive for every m at least one. The even polynomial is at least (2m)^3/8, which is stronger than the common constant 2/27. This proves S1 for all 2<=k<=N, without any small-moment assumption.

For S4, when 2k<=N every relevant denominator is at least N/2. The even coefficient sum is at most 1+3j^2/N, since (j-1)(4j-5)/3 is at most 4j^2/3. The odd sum obeys the same bound. Applying these bounds to the running maximum of the preceding ratios gives the stated product and exponential estimate. The initial ratio at j=2 is covered separately.

Consequently a ratio tending to one forces k^3/N to tend to zero by S1. Conversely, k^3/N tending to zero eventually implies 2k<=N, so S4 proves convergence to one. The same pair of bounds also proves that the ratios stay bounded along a sequence if and only if k^3/N stays bounded.

## Relation to the actual source question

The published [Collins and Nagatsu paper](https://alco.centre-mersenne.org/articles/10.5802/alco.480/) retains the scaling question in Remark 3.4. Its recurrence, leading terms and normalized error recurrences are prior results. The new deduction here is the explicit positive lower bound and its consequence for necessity. The self-contained upper bound complements that deduction.

The source asks about the cubic range of its argument. The result answers both relative convergence to the specified leading term and bounded comparability with it. It does not address every possible estimate for centered moments, all Weingarten coefficients, or the later spectral trace inequalities.

No critical-scale limit has been established by this review. A primary-source search has not yet ruled out an independent later solution of the same necessity question. That uncertainty is about priority, not a missing step in this proof.
