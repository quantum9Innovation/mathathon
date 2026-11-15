# Separate review of the critical effective operator

November 15, 2026, America/Los_Angeles.

Verdict: accept [effective-operator-v1.md](../root/effective-operator-v1.md) at SHA256 13b559897d6ed9253a2fc6dd4dede5dd03914c078558d759542afc9c54d28864. Every section was read and its probability, operator and spectral steps reconstructed. No unsupported inference or unresolved mathematical finding was identified.

This is a paper-proof review. It does not establish the marked-distance limiting law, historical priority or end-to-end formal verification.

## Exposure and inputs

Prior exposure included the preceding transition proofs, their independent reviews, the present problem packet, and discussions of the expected collective-plus-pair limit. The reviewer had also independently suggested that a finite matching sector should decouple from the constant vector. The manuscript itself was first read after its hash was supplied. The present probability attempt was not read before this review.

The inspected dependencies were the previously reviewed nonbacktracking estimate at SHA256 d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896, cluster-width theorem at SHA256 e40164dcf711cca13d945b666645c26aa8095b835e1e727d2d6d7159a78e7b8f, and finite transfer at SHA256 deb05e53631ad4d273f48b2d6253014352c1263010d3990ebcc4e0b616351b99. This is separately reconstructed work with shared target exposure, not access isolation. No proof file was edited.

## E1. Critical input bounds

At m of order n^(1/3), the earlier diagonal expectation divided by s is O(s log^3 n), which tends to zero. The previous fixed-order derivative bound also tends to zero. The width theorem supplies ||G-gI||=O_P(s), since m^2/n and s are comparable at criticality. These are unconditional convergence statements with an exceptional host-gap event of vanishing probability. No expectation is improperly conditioned on that event.

The nonbacktracking series has the correct zeroth Q term and stationary corrections. Its finite estimates apply before any subcritical substitution, so using them at criticality is legitimate.

## E2. Unequal walks and uniqueness

For r=t, N_r(u,v)^2-N_r(u,v) counts ordered pairs of distinct incidence sequences. For unequal lengths, every pair of sequences is already distinct. Thus each quantity being averaged is nonnegative, including under the configuration-model loop conventions.

The combined exposure uses at most r+t fresh pairings. Without a fresh edge hitting a previously discovered vertex, the revealed union is a tree. Reusing exposed edges does not invalidate this implication. Two nonbacktracking walks from the same root in a tree can end at the same vertex only if their lengths and entire sequences agree. Hence every counted distinct pair requires a collision, and the O((r+t)^2/n) bound applies.

Multiplication by the numbers of walk choices and summation over starting vertices gives equation (8). Conditioning on simplicity costs only a bounded factor. Summation over the lengths gives the exact factorial-count quantity S_R(S_R-1), and geometric growth yields equation (9).

The off-diagonal label-symmetry bound is valid under the unconditional simple-graph law. At criticality its upper bound is O(q^(2K)n^(-2/3)log^2 n), which tends to zero for each fixed K. A shortest path is nonbacktracking, so uniqueness gives precisely the weighted geodesic identity (11). The proof correctly avoids demanding tree neighbourhoods around all marks.

## E3. Matching and the operator error

The maximum degree of the host distance graph is O(q^R). Its induced marked-edge expectation is O(q^K), hence tight for fixed K. Its induced wedge expectation is O(q^(2K)n^(-1/3)), so the marked graph is a matching with probability tending to one. Tightness and m tending to infinity imply 2p<m. Direct marked host edges have vanishing probability.

The tail Frobenius estimate, compressed using label symmetry, becomes O(theta q^(phi_n-K)+mL^4/n) after division by s^2. Since theta stays bounded and 0<=phi_n<1, its limiting bound is C q^(-K) with a constant independent of K. Markov's inequality gives the eta^(-2) factor.

All other terms vanish for fixed K: short-path nonuniqueness, the host-gap exception, the diagonal error, stationary subtraction and the projected spectral tail. Therefore equation (15) is an operator-norm approximation over the complete marked subspace. It is stronger than entrywise convergence.

## E4. Transfer to actual ordered eigenvalues

The exact critical Schur identity and signs are correct. The attachment norm is bounded independently of m. The value error is O_P(s), while its derivative error is o_P(1), because the scalar tree derivative calibration remains unchanged. Local second derivatives are uniformly bounded by the host gap.

Using Z=F(d) makes the constant-term error in the finite transfer exactly zero. For a fixed radius B_0s, the transfer error divided by s is o_P(1). On ||T_n||<B_0/2, the finite transfer condition then holds with probability tending to one. Since ||T_n||=O_P(1), first taking n to infinity and then B_0 to infinity removes the exceptional norm tail. This proves equation (19) as an unconditional o_P(1) statement.

The earlier transfer counts and orders all top m+1 roots. No simple-root assumption is inserted, and a repeated eigenvalue is covered. The coefficient multiplying the retained pair matrix is (d-2)d^2g/D=dq/D=h, as stated.

## E5. Decoupling and final comparison

The vector of deleted collective couplings has norm kappa sqrt(2p/m). The corresponding symmetric off-diagonal star has operator norm exactly that quantity. It tends to zero for fixed K because p is tight.

After deletion, the pair blocks and the residual star are a direct sum. The pair eigenvalues are the stated positive and negative amplitudes. The residual star has values plus and minus kappa sqrt(1-2p/m), with m-2p-1 zeros. Its discrepancy from plus and minus kappa is at most 2kappa p/m. Thus the multiset has exactly m+1 elements and every finite normalization correction is controlled.

Weyl's inequality compares the ordered lists even when pair amplitudes coincide with one another or with kappa. Combining the operator error and the terms tending to zero gives the theorem's C eta^(-2)q^(-K) bound, after adjusting a fixed constant.

## Order of limits and disposition

All geometric good events and tightness arguments are for a fixed K. The final conclusion is lim_(K to infinity) limsup_(n to infinity) of the approximation failure probability equal to zero. The proof does not assert a uniform growing-K good event. This is the correct order for the stated truncation theorem.

No Poisson law or limiting distribution is used. The H=0 restriction is substantive because a general H could connect the finite pair sector to the other marks. The next bridge is a separately established marked-distance law and a justified limit of its truncated spectral multisets. No repair is required at the frozen revision.
