# Independent reconstruction of the collective fluctuation

November 15, 2026. Reviewer: root. Target: probability/collective-limit-v1.md, SHA256 e492d3dfa506167ba28782e316129146e72f8046e96bbaf50b265e42d3fc307d.

Verdict: accepted as a paper theorem for the stated quadratic form and joint pair counts. It is not accepted as an eigenvalue law, which the target explicitly does not claim.

Exposure: the reviewer authored earlier deterministic reductions and reviewed the prior probability arguments. The candidate compensated law was discussed before this round. The present review independently reconstructs the finite-sampling, stationary-centering and limiting arguments from the frozen revision. There is no access-isolation claim.

## Reconstruction

1. In a uniform m-subset, two edge indicators with disjoint endpoints have covariance p_4-p_2 squared, which is nonpositive. For nonnegative weights those contributions can be omitted in a variance upper bound. Equal pairs contribute at most a constant times p_2 ||H||_F squared. Overlapping pairs contribute at most a constant times p_3 sum of squared row sums. The prefactor 4/m squared gives exactly the two orders in equation (17). This would fail as written for a signed tail matrix, but the actual U_R and its off-diagonal part are nonnegative.

2. The conditional mean uses the exact row sum 3(L-R)/2 before diagonal deletion. Dividing its first term by s squared leaves the coefficient n(m-1)/(m(n-1)), whose difference from one is O(1/m). Its total error is O(L/m). The trace term has coefficient O(1/n). Equation (19) makes it vanish after scaling. Thus no trace fluctuation is concealed at order s squared.

3. Dividing the variance by s to the fourth power gives n 2^(-R)/m squared, L to the fourth/m squared, and L squared/m. The first equals 2^(phi_n-K)/theta_n and the latter two vanish. The centered tail therefore has the claimed O(2^(-K)) limiting variance bound. These estimates are unconditional under the simple-host law.

4. The diagonal is averaged, not maximized. Its O_P(L cubed/n) error divided by s squared is O_P(L cubed/m), which vanishes. The operator truncation divided by s squared also vanishes. Restoring the off-diagonal stationary term gives -g(1+3L/2)(1-1/m), including the j=0 term.

5. With R=r+K and 3g/2=1, the exact surviving center is

\[
r+g\,3(L-R)/2-g(1+3L/2)=-K-g.
\]

The unordered pair contributes twice to the quadratic form, giving coefficient 2g/(ms) times 2^(phi_n-k). This is precisely b_(n,k)=4 2^(phi_n-k)/(3 theta_n). The stationary constant -2/3 and the compensation of one unit per positive distance level are both correct.

6. For a fixed K the negative-offset window can be opened by controlling the probability of any omitted pair, not its expectation. The ball-size bound gives O(2^(-J)). This is the correct control because the omitted weights have infinite limiting total mean. The limiting negative-offset sum has finitely many nonzero terms almost surely.

7. The positive-offset centered series has tail variance b_0 2^(-K). Combining this with the finite-cutoff graph comparison gives the stated converging-together proof. The same cutoffs preserve any fixed finite count vector. Conditioning on one fixed count uses joint convergence and its positive limiting point mass, without reusing an unconditional graph estimate as a conditional estimate.

8. Reindexing the phase-one coefficients gives k at phase one equal to k-1 at phase zero. This moves exactly one compensated term across the cutoff. Its mean weight is one, so C_1 has the law C_0-1. Adding the full phase to the centered variable restores agreement at the endpoints. This is consistent with, and different from, the uncentered spectral point-process phase identification.

## Scope and remaining obligations

The theorem establishes a new order-s-squared random-graph quadratic limit. The full random-graph eigenvalue at the retuned crossing can also receive complementary-space and nonlinear-energy corrections of that same order. The frozen proof neither computes nor drops those corrections.

No unresolved mathematical finding was identified in this revision. The formalization is still finite and does not encode the probability argument. Historical priority requires the separate source comparison.
