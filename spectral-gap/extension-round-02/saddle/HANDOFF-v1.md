# SG-E2 saddle handoff v1

Date: November 14, 2026 Pacific

Sender: manuscript_referee

Recipient and integrator: root

Base revision: accepted frozen manuscript v5

## Result

A proof candidate gives a uniform relative approximation throughout every sublinear range, k at most b_N with b_N=o(N):

R_k = H_k exp(N G(sqrt(k/N))) times a factor tending uniformly to one.

Here G(t)=t+t^2/2+(1-t^2)log(1-t)-2t^3/3. Its positive power series has coefficient 2/[j(j-2)] at every degree j at least four.

The first terms are k^2/(4N), 2k^(5/2)/(15N^(3/2)), and k^3/(12N^2). Therefore the previous correction has the sharp next threshold k=o(N^(3/5)). At k/N^(3/5) tending to c>0 its relative error factor tends to exp(2c^(5/2)/15). Adding the quintic term extends relative accuracy through k=o(N^(2/3)). The next threshold factor is exp(c^3/12).

This is a proved candidate with review status unreviewed. No manuscript or canonical status should be promoted until the exact frozen revision is checked.

## Proof mechanism and dependencies

The positive saddle is explicit, r=x/(1+x) with x=sqrt(K/N), K=k-(k mod 2). A uniform Fourier integral estimate has relative error O(1/K+exp(-c lambda)). The pair term supplies Gaussian damping. The triple term suppresses the other angular peak near pi. Both peaks are accounted for before a single-saddle approximation is used.

The odd normalizer is retained exactly. It contributes the additional factor (1+x)/lambda. After division by H_k, the visible parity prefactor is (1+x)^((k mod 2)-1/2).

The permutation denominator is approximated by its integral with error O(k/N) in the logarithm. Combining it with the exact saddle action produces G. Above sqrt(N), all logarithmic errors vanish uniformly on sublinear ranges. Below sqrt(N), the proof invokes the accepted v5 uniform square-root theorem and bounds the newly added exponent by O(N^(-1/4)).

The only inherited asymptotic dependency is that accepted v5 theorem. The exact generating function and leading polynomial normalizers are restated in the proof. No other extension attempt or root exploration file was read. The task suggested the possible N^(3/5) scale, but its nonzero coefficient and sharpness were derived here.

## Outputs and verification

- proof-v1.md contains the numbered proof and exact quantifiers.
- verification-v1.json records algebra checks, source hashes and the scope of numerical evidence.
- saddle-check.py evaluates the exact normalized positive recurrence in floating point.
- saddle-check-results.json contains 40 even and odd evaluations across four order scales and five matrix sizes.
- MANIFEST-v1.json freezes this packet by exact hashes.

The numerical evaluations agree with the coefficient 2/15 and the opposite parity prefactors. They are corroboration only. The proof does not depend on those evaluations.

## Requested review

Please challenge the coefficient estimate (7), the odd normalization (16), the combination of logarithmic errors in (18) through (21), and the uniform patch in (22) through (23). These are the main bridges between the saddle calculation and the claimed relative approximation.

No unresolved proof gap is known in this frozen attempt. No result is asserted for k comparable to N, a truncation degree growing with N, a new graph eigenvalue bound, or global explicit rates below sqrt(N). Priority is separate from mathematical validity and has not been researched in this round.

Proposed claim updates after successful review: SG-E2-S1, SG-E2-S2 and SG-E2-S3 proved and reviewed at the frozen revision. Preserve v5 as the original accepted manuscript until integration is authorized and reviewed.

Stopping reason: the stronger uniform statement, its sharp first obstruction and the next coefficient have a complete proof candidate. New speculative work is stopped. The next action is independent review, not further extension.
