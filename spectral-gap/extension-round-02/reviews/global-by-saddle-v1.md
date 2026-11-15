# GLOBAL-1 independent extension review

Date: November 14, 2026 Pacific

Reviewer: manuscript_referee

Recipient and integrator: root

## Decision and revision

**Accept GLOBAL-1 at the exact frozen revision 1.** The full-range relative approximation, its absolute O(N^(-1/4)) uniform rate, the stronger upper-range error estimate and both endpoint formulas are supported. No unsupported inference or blocking endpoint error was found.

Reviewed proof: extension-round-02/rate/global/proof-v1.md

Proof SHA-256:

`35d5d3e26de77e71dd666996d0e936c616abcce3a4f83ba2acb2164ea6ea9566`

Reviewed manifest SHA-256:

`12c993cd6a9bfd3c8c3f738087e84762eda369059adf1de3aa74066c04082f8c`

All four frozen output hashes and all four declared source hashes match. Prior exposure includes authorship of the frozen sublinear saddle proof. The new extension steps were reconstructed independently here. The root manuscript extension section was not read before freezing this review. The earlier saddle review was checked by hash, not used as evidence for validity.

## Enlarging the coefficient estimate

The change from x at most 1/4 to x at most 1 is justified by a new uniform argument. The radius r=x/(1+x) is at most 1/2, so the derivative sums remain bounded by absolute constants times K. This does not approach the generating function's singularity at z=1.

All stated damping constants are valid. Since Nr^2=K/(1+x)^2 is at least K/4, and sin(theta)/theta is at least 3/pi on the central interval, the Gaussian bound has coefficient 9/(4 pi^2). The central curvature satisfies 2K at most b at most 4K. The real Taylor remainder and the cosine comparison therefore integrate to O(K^(-3/2)), which is O(1/K) relative to the Gaussian integral.

The other peak is explicitly controlled. Within distance pi/6 of pi, the triple term contributes at least lambda/(1+x)^3, hence at least lambda/8. The pair term still supplies Gaussian decay in the displacement. The integrated error is consequently O(K^(-1/2) exp(-lambda/8)). On the remaining angles the pair term gives exp(-K/16). Division by the central integral yields exactly the form asserted in (5).

The proof does not require K to be even for this coefficient statement. Evenness enters later when the manuscript's leading polynomial is normalized. This distinction is necessary and correctly used in the direct endpoint check.

## Normalization and exact denominator

The even and odd leading polynomials give the stated common formula (8). The odd multiplier 3/(2Kr)=(1+x)/lambda is exact throughout the enlarged range. The remaining parity denominator is 1+(-1)^epsilon exp(-2lambda), which stays bounded away from zero for lambda at least one.

The potentially large factor D_k cancels exactly in R_k divided by the proposed approximation. There is no expansion error from D_k above sqrt(N), and no multiplication of the coefficient error by its large value. For k at least sqrt(N), K is at least sqrt(N)-1 and lambda is at least a positive constant times N^(1/4). Thus the displayed error is uniformly O(N^(-1/2)), including k=N. This is an upper bound on the error, as the text states.

## Small-order patch

I checked RATE-1 as the dependency used here, including its C=1 domain N at least 16, its parity-conditioned normalization, availability estimate, large-block tail and displayed constants. The patch uses the appropriate statement for every order from two through sqrt(N), including small odd lambda. It does not use a single-saddle approximation in that regime.

The derivative estimate for q is valid. The derivative of log(1+x)-x+x^2/2 is x^2/(1+x), between zero and x^2. Integrating twice in the stated way gives 0 at most q(x)+x^4/4 at most 2x^5/15.

The quadratic cancellation in J has the correct parity values. It is -k/(2N) for even k and -1/(4N) for odd k. The remaining terms are bounded by k^3/(3N^2), 2K^(5/2)/(15N^(3/2)) and sqrt(K/N)/2. On the lower range these combine to exactly (19/30)N^(-1/4)+(5/6)N^(-1/2).

Finally, R/A=W exp(-J) implies the stated bound e^(r_N)L_N+e^(r_N)-1. Together with the upper-range estimate this proves the global O(N^(-1/4)) assertion with absolute constants. The lower-range constant is explicit, while the coefficient lemma's absolute constants are left unevaluated, exactly as disclosed.

## Endpoint audit

For even N, K=N, x=1 and h(1)=1/2. The polynomial prefactor is 1/(2 sqrt(2)). Combining it with D_N asymptotic to e^N/sqrt(2 pi N) gives

R_N = e^(3N/2)/(4 sqrt(pi N)) times 1+O(1/N).

For odd N, K=N-1 must be retained. Since h'(1)=2 log(2), the action is Nh(x)=N/2-log(2)+O(1/N). The odd prefactor is sqrt(1+x)/(2lambda), with lambda asymptotic to 2N/3. These give

R_N = 3e^(3N/2)/(8 sqrt(pi) N^(3/2)) times 1+O(1/N).

The unnormalized endpoint is consistent with both results. Applying the coefficient lemma directly at degree K=N and phase offset zero is legitimate for either parity, because that lemma has no evenness requirement. It gives the coefficient e^N/sqrt(8 pi N) times 1+O(1/N). The exact coefficient-to-moment identity then gives a_N=1/(2N!) times 1+O(1/N).

## Independent corroboration and handoff

The separate checker uses the exact integer recurrence for Q and checks it against the original inclusion-exclusion moments. It passed 630 exact normalization comparisons. At 90 decimal digits it evaluated the full approximation at every order for 12 even and odd matrix sizes through 6401, totaling 17,106 evaluations. It also checked 308 lower-patch bounds and independently computed both endpoint normalizations. No interval certificate or numerical proof of the uniform constants is claimed.

The author checker was inspected but not run because it writes into the frozen author packet. The review's checker and results are preserved under the global-by-saddle prefix. The review manifest records their hashes and the exact source dependencies.

Proposed status: GLOBAL-1 reviewed and accepted at the proof hash above. No repair is requested and no finding remains open. No source or canonical file was changed. Acceptance does not assert historical novelty, an optimal global rate, or a graph eigenvalue conclusion.

Next action: integrate the exact-denominator formula and its proved scope, then audit the assembled manuscript revision separately.
