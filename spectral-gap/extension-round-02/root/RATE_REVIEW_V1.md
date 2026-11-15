# Independent reconstruction of the explicit square-root rate

Reviewed November 14, 2026 Pacific. Reviewer: the problem 21 integrator. Exact source: `../rate/square-root-rate-v1.md`, SHA256 `ed472ce70521c37d59c4e3efc88bf7e883d1a75526023ef2c3a15c57bcd9c581`.

Decision: accept RATE-1, both its finite k-dependent inequality and its explicit uniform constants, at the stated hypotheses. This review reconstructs the written argument. It does not infer the theorem from finite checks or certify historical priority.

## Exact scope

For C>=1, N>=16 C^2 and integer 2<=k<=C sqrt(N), the relative error of R_k against exp(k^2/(4N))H_k is at most A_1(C)N^(-1/4)+A_2(C)N^(-1/2)+A_3(C)N^(-1), with the three constants in equations (2) and (3) of the reviewed proof. The more detailed inequality (5) holds for 2<=k<=N/4. The odd hyperbolic argument uses K=k-1 exactly.

The proof depends on the accepted exact partition representation and the known leading coefficients. It supplies its own quantitative estimate and does not use the previous compactness proof of uniform convergence as a premise.

## Reconstruction

1. Restricting the positive partition sum to blocks of sizes two, three and four gives the exact expectation e^eta E w_epsilon(s). Even and odd triple counts are conditioned on their respective parity. For odd orders, the factor 1/lambda cancels exactly against H_k. The shift t=J-1 makes the availability index nonnegative at the smallest odd order. There is no lower bound on lambda hidden in this step.
2. I differentiated the parity generating functions and independently expanded the moments of J-1. In particular, E(t^2)=lambda^2-q, E(t^3)=lambda^2+lambda^2 q+q and E(t^2-lambda^2)^2=3lambda^2+(4lambda^2-1)q, with q=lambda coth(lambda)-1. The bounds q<=lambda and q<=lambda^2 justify all stated moment inequalities. The negative coefficient when 4lambda^2<1 only improves the upper bound.
3. The availability comparison remains valid at and beyond truncation. For s<=m/2, the summed logarithm remainder is bounded by s^3/m^2. For s>m/2, the proposed upper bound 4s^3/m^2 exceeds one, including m=1. The difference e^(-A)-w is nonnegative because every retained product factor is at most its exponential counterpart.
4. Expanding A-delta gives precisely the five terms in equation (14). Independence and the displayed Poisson moments yield equations (15), (16) and (17). The second-order Taylor estimate uses nonnegative A and delta, where the second derivative of e^(-x) has absolute value at most one.
5. I recomputed the rounded coefficients in the bound B. The lambda^3 coefficient before rounding is 405/32+54=66.65625. The constant part of the lambda^2 coefficient is 225/8+216=244.125. The eta^2 and eta coefficients are 456.5 and 140.5. They are bounded by 67, 245, 457 and 141, respectively. The remaining coefficients agree exactly.
6. Terms containing a block of size at least five are nonnegative. Dropping availability in those terms bounds their contribution by the difference of the unrestricted parity sums. The odd comparison uses sinh(y)/y, so its tail bound stays uniform when lambda is small. Both aggregate tail inequalities in equation (20) hold when sqrt(K/N)<=1/2.
7. Restoring D_k introduces the reference value D_k exp(-(k^2+K^2)/(4N)). The discrepancy of its linear logarithmic term is -k/(2N) for even k and -1/(4N) for odd k. Equation (24) bounds both. This verifies the often-sensitive odd floor correction in the finite result.
8. The uniform hypotheses imply k<=N/4. Substituting the five exact scaling identities of Section 7 into B gives B_1, B_2 and B_3. The factor e^(7C^2/4), the higher-block factor e^(C^2), and the denominator remainder e^(C^2/3) give the displayed A_i without suppressing an N-dependent constant.

## Evidence and limits

The investigator's separate check report records symbolic parity-moment identities, finite availability checks and high-precision examples. Those are corroboration. This review's conclusion rests on the general calculations above.

The constants are deliberately generous. They can produce a bound greater than one at realistic N, so the statement should be presented as an explicit asymptotic rate with a finite validity threshold, not as a highly accurate practical error bar. No claim of rate optimality follows until a separate lower-bound or signed-expansion argument is reviewed.

No correction to the frozen proof is requested. Suggested ledger promotion: SG-09 proved and reviewed, with this exact source hash. A future change to the partition normalization, the odd shift or a moment inequality would require reassessing the dependent rate statement.
