# Independent reconstruction of the signed next-scale reduction

November 15, 2026. Reviewer: root. Target: probability/signed-coupling-v1.md, SHA256 68660a0914a02b0a6bf53f2ccef75a2b844859e9dafc7f8a9e106db3921d5fba.

Verdict: accepted as the stated graph-derived two-dimensional Schur reduction. The collective self-energy distribution and final eigenvector selection remain outside this revision.

Exposure: the reviewer authored earlier deterministic reductions and reviewed the preceding probability proofs. Before reading the frozen file, the reviewer separately derived the energy-dependent expansion and obtained the same pair coefficient 33/16-beta and collective expression (kappa squared/2)C_n+63/32+Sigma_11/s. The probability author had communicated the value F''(3)=-136/3. This is disclosed partial exposure, not an isolated derivation of that value.

## Checked steps

1. The exact retained pencil has lower block xI-F(3+sx)/(8s). This produces T-x Gamma-(s x squared/16)F''(3), with the second derivative acting only on marked coordinates. The host-star coupling is unchanged by this expansion.

2. The selected-column bound retains a factor 2^(-K) in its squared norm after multiplying by m. For each fixed K, short matching makes the short interaction on V exactly its own pair. The own-partner, diagonal and stationary remainders vanish after this normalization. The left side of equation (14) is independent of K, so the iterated limit proves the claimed little-o estimate. This is stronger than the earlier big-O estimate and does not require a growing cutoff.

3. The direct mixed entry requires signed information. A generic column norm would give only an insufficient square-root bound. Equations (18)-(20) explicitly cancel the leading pair action against both e and the two-endpoint sum. The remaining mixed-tail bound is O_P(m^(-3/2) times a fixed power of log n), which is o_P(s) since ms tends to a positive constant.

4. Direct differentiation gives rho'(3)=-1/2 and rho''(3)=2. For g=rho/(1-rho squared), the derivative with respect to rho at 1/2 is 20/9 and its second derivative is 208/27. Thus g''(3)=52/27+120/27=172/27. Substitution gives

\[
F''_{\rm tree}(3)=-2(2/3)-12(-10/9)-9(172/27)=-136/3.
\]

The order-s analytic coefficient is therefore 17/6, with the sign in equation (24).

5. On the antisymmetric mode, Gamma equals -s(r+1)w to the required precision. Substituting x=-kappa+O(sr) gives

\[
-w-\kappa s(r+1)w+(17/6)\kappa^2s
=-\kappa-(\kappa^2/2)sr+s(33/16-\beta_n)+o_P(s).
\]

The discarded products have size O(s squared r squared)=o(s).

6. Removing the selected endpoints from the collective direction changes f transpose Z f by -2w/m at leading order. The host-star normalization changes its collective energy by +kappa/m. Their combination is (kappa-w)/m=o(s), so the use of C_n with the full e remains correct at this scale. The stationary marked term contributes 3s/8 to the collective diagonal. The analytic correction contributes 51s/32. Their sum is 63s/32.

7. The selected antisymmetric complementary column is o_P(sqrt(s)), while the collective column is O_P(sqrt(s)). The fixed complementary inverse bound therefore gives an induced cross term o_P(s), pair self-energy o_P(s), and collective self-energy O_P(s). The prior gap argument applies after the fixed-K then K-to-infinity limit and survives the o_P(1) pencil correction. Conditioning on p_n=1 is performed only after these unconditional probability bounds.

8. The pencil derivative is O_P(s log squared n). Differentiating its complementary inverse gives a bounded derivative on the good gap event. The collective self-energy derivative is O_P(s), so its change across an O(s) energy interval is o_P(s). This justifies using one fixed evaluation of Sigma_11 in equation (10).

## Interpretation

The leading signed mixing coefficient vanishes in the actual graph pencil, including the complementary-space contribution. This is not exact zero coupling at finite n. The pair shift is established, but the collective correction Sigma_11/s is only shown tight here. Its limit cannot be dropped or identified with the linear quadratic-form limit.

No unresolved mathematical finding was identified in the frozen revision. A final eigenvalue theorem still needs the collective self-energy law, control of its possible coincidences with the pair shift, and the stated physical reconstruction.
