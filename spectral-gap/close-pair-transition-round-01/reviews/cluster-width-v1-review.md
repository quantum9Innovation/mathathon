# Separate review of the marked resolvent and cluster-width upper proofs

November 15, 2026, America/Los_Angeles.

Verdict: accept both frozen upper proofs at the exact revisions below. Every section was read, and the probability estimates and their spectral transfer were reconstructed. No unsupported inference or unresolved mathematical finding was identified.

This is an internal paper-proof review, not end-to-end formal verification, external specialist acceptance or a historical-priority certificate.

## Exact revisions and prior exposure

| Input | SHA256 |
| --- | --- |
| [Nonbacktracking upper proof v1](../root/nonbacktracking-upper-v1.md) | d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896 |
| [Cluster-width proof v1](../root/cluster-width-v1.md) | e40164dcf711cca13d945b666645c26aa8095b835e1e727d2d6d7159a78e7b8f |
| [Previous probability input](../../growing-defects-round-01/probability/proof-v1.md) | 56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b |
| [Previous deterministic transfer](../../growing-defects-round-01/root/transfer-v1.md) | deb05e53631ad4d273f48b2d6253014352c1263010d3990ebcc4e0b616351b99 |
| [Previous graph theorem](../../growing-defects-round-01/root/graph-theorem-v1.md) | b4a00f7b6490590a51e112c99be336e895723f29df4819c68d00dec526a4d2e3 |
| [Previous mass theorem](../../growing-defects-round-01/root/eigenvector-masses-v1.md) | a98fa21b356991a4e3d6a51f1568984f9d0592d3c81c893e0ec81f6fb11561d6 |

Prior exposure included the previous accepted proofs, the present problem packet and integrator descriptions of the intended cutoff and monotonicity upper argument. The reviewer also constructed the separate lower-obstruction proofs. Both upper manuscripts were first read after their hashes were supplied and after the lower manuscripts were frozen. No current alternate probability attempt was read. This is a separately reconstructed review with shared target exposure, not access isolation.

No frozen proof was edited. No numerical experiment was used as a premise.

## U1. Polynomial series and the host gap

The nonbacktracking recurrence is valid for regular incidence graphs, including the configuration model's loop and parallel-edge conventions. The exceptional length-two term is A^2-dI, and the stated generating-function numerator 1-t^2 accounts for it.

At t=1/q, the denominator equals (dI-A)/q. Its prefactor therefore gives the inverse coefficient q/[d(d-2)], exactly g. Each positive-length matrix M_r has constant row sum d/q, so subtracting (d/q)Pi gives M_r Q. The zeroth term is Q, not I. Thus equation (2.1), including its stationary subtraction, is correct.

On the good event, all host-complement eigenvalues lie in [-d rho,d rho]. The displayed Chebyshev expression and its finite geometric-sum bounds yield the stated operator bound with beta<1. The same proof controls negative eigenvalues because absolute values are used. Choosing a sufficiently large logarithmic cutoff makes the projected spectral tail at most n^(-4). No near-edge rate for the random regular spectrum is required.

The host event also excludes a second eigenvalue d, so the top host eigenpair is simple there. The previously reviewed fixed-gap and positive-simplicity inputs suffice.

## U2. The two-walk estimate

For a fixed configuration there are exactly a_r=d q^(r-1) possible nonbacktracking incidence sequences of length r from one root. Independent uniform choices have endpoint-coincidence probability equal to the squared row norm of N_r/a_r.

Deferred pairing exposure of the two walks makes at most 2r discoveries and visits at most 2r+1 vertices before a fresh discovery. The stated forbidden-partner numerator and denominator are conservative. Under 4r+1<=nd/2, their union bound is at most 12r^2/n.

Reusing an already revealed edge does not itself count as a collision. Nevertheless, when every fresh edge joins a previously unseen vertex, the revealed graph is a tree. Nonbacktracking walks on a tree starting from the same root can have the same endpoint only when their incidence sequences coincide. For every fixed graph and first walk, the second picks that exact sequence with probability 1/a_r. This justifies the endpoint bound without assuming independent endpoints.

Multiplying by a_r^2 q^(-2r) and summing over roots gives precisely (d/q)n q^(-r)+12(d/q)^2r^2. The squared Frobenius quantity is nonnegative, so conditioning on simplicity costs only its reciprocal probability. Conditioning on the host-gap event is correctly avoided.

Minkowski's inequality in the square-integrable matrix Hilbert space gives the tail estimate with terms sqrt(n)q^(-R/2) and L^2. Squaring gives equation (3.3). There is no unproved cancellation or missing covariance term.

## U3. Coordinate compression and the log-free range

The unconditional label symmetry identity for off-diagonal squared entries is exact. The ball-size bound and a union bound give the stated short-distance failure probability. On its complement, every nonbacktracking walk of length at most R between distinct marks is absent. This statement holds even when the host has cycles.

With R=floor(log_q(1/s)), the floor gives q^(-R)<=q s and q^R<=1/s. Dividing the marked Frobenius bound by s^2 gives O(m s+m L^4/n), as claimed. Both terms vanish under m^3/n tending to zero. The stationary correction divided by s is O(s L), and the projected operator tail is negligible. Removing a diagonal increases operator norm by at most a factor two, which justifies its treatment of the spectral tail.

For the diagonal, the universal-cover excess return is nonnegative before averaging. The old single-walk estimate therefore controls the sum of the marked diagonal excesses by Markov's inequality without a signed-conditioning error. Its mean divided by s is O(s log^3 n), which vanishes in the new range. This proves the whole marked resolvent approximation, not only its off-diagonal part.

For every fixed positive derivative order j, the previous derivative estimate tends to zero when m^3/n tends to zero. Indeed m<=n^(1/3) eventually, and each fixed logarithmic power is dominated by the remaining negative power of n. The no-marked-edge probability also tends to zero. Thus every input of the earlier deterministic transfer and mass theorem is recovered. The derivative order is fixed, not allowed to grow with n.

The proof therefore legitimately extends the earlier weighted cluster and zero-interaction mass laws to m^3/n tending to zero, with their original constants and uniformity qualifications.

## W1. Variable cutoff up to m=o(sqrt(n))

Write a=m^2/n, s=sqrt(m/n), w=max(s,a), and x=K w for fixed K>=1. Since w tends to zero and w>=n^(-1/2), the chosen R is eventually positive and lies below the logarithmic cutoff L.

The short-pair failure probability is at most C a/x<=C/K. The floor in R gives q^(-R)<=q x, so the squared tail bound is C[a x+m^2 L^4/n^2]. After division by x^2 the first term is at most C/K. The second is bounded by C m L^4/(K^2 n), which vanishes for m=o(sqrt(n)). Hence Markov's inequality gives the stated tail probability at threshold x.

The remaining diagonal and stationary terms are o_P(s), since s log^3 n tends to zero throughout this range. They are consequently negligible compared with x. Adding the vanishing host-gap exceptional probability gives equation (2.3) with a constant independent of K, n and H. The quantifiers are correct: K is fixed before taking the limiting upper probability, and is then made large. This proves O_P(w), rather than a falsely claimed vanishing error at that scale.

## W2. The actual spectral comparison

For |z-d|<gamma, the eliminated host-complement block is positive definite and F'(z)>=I. Let b_norm=||b|| and f_norm=||F(d)||. For t>b_norm+f_norm, the upper retained Schur form is bounded below by

\[
(t-b_{\rm norm})x^2+(t-b_{\rm norm}-f_{\rm norm})\|y\|^2,
\]

which is strictly positive. The lower form at d-t is bounded above by the negative of the same expression. Congruence therefore gives no augmented eigenvalue above d+t and exactly m+1 above d-t. Letting t decrease to T proves the closed interval assertion. The T=0 case is valid by the same limit.

This argument identifies actual ordered eigenvalues and handles repeated roots. It does not require a first-order scalar approximation, derivative convergence or a spacing estimate. Principal-submatrix interlacing gives mu_(m+2)<=lambda_2(A), as stated.

The exact attachment identity for F(d), including the negative stationary term -2cd J_m/n, is correct. The probability of a nonzero marked adjacency block is O(a)=o(1). On its complement the common bound on T is O_P(w), uniformly over ||H||<=H_0. Since w tends to zero, T<gamma with probability tending to one. This verifies the complete passage from the variable-cutoff estimate to the actual cluster-width theorem.

## W3. Combination with the lower results

At m/n^(1/3) tending to a positive finite constant, w is a constant-order multiple of s. The entire top m+1 cluster is tight after division by s. The separate lower proof shows that its top coordinate cannot converge to the star prediction. These are compatible statements. Neither determines a critical limiting law.

For n^(1/3)<<m<<sqrt(n), w=a. The accepted upper proof gives tightness of the top displacement divided by a. The separate pair-scale theorem gives that this quotient is bounded away from zero in probability. Together they identify its order in probability. The lower claim alone does not give an upper bound, and the upper claim alone does not give a nonzero lower scale.

The sharp necessity argument for the cubic H=0 star law is also valid within m=o(n). If m^3/n does not tend to zero, pass to a subsequence on which theta=sqrt(m^3/n) is bounded below by a positive constant. Along that subsequence m tends to infinity, so the lower theorem applies and gives a positive probability of exceeding any fixed K>3/sqrt(8). This contradicts convergence to the star coefficient. Sufficiency follows from the accepted log-free upper proof and the previous transfer. The same logic applies to the weighted bounded-H family using its separately reviewed uniform lower obstruction and the uniform bounded norm of its effective matrix.

This paragraph checks the integration logic. The present reviewer authored the lower proofs, so their independent acceptance must come from the separate integrator review, not from this report.

## Disposition and boundaries

Both upper manuscripts are accepted at their exact hashes. No first unsupported inference or required mathematical repair was found. The cluster-width theorem stops at m=o(sqrt(n)), even though the separate lower divergence continues to m=o(n). The top scale conclusion is not a spatial localization theorem or a spectral-gap theorem for a normalized random walk. Formal checks of finite identities do not certify the probabilistic and analytic proof chain.
