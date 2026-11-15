# Independent reconstruction of the sharpened mixed bound

Reviewed: proof/permutation-proof-v3.md, frozen revision 3. This review concerns the complete refined argument, not only its difference from the starting proof. The integrator independently derived the affine weights and exact factorial merging before comparing with the investigator's written proof.

Decision: accept the exact factor F_n(a-h), the square-root cancellation factor, the universal prefactor sqrt(e), and its optimality for the stated class of arbitrary mixed products. Historical priority and subsequent circuit enumeration remain separate.

The conditional permutation has exactly n-r remaining rows. The mean of nU-1 is r/(n-r), and its row sum is r. A used column removes one or both collided factors. Row relabeling is valid because all other retained cells have distinct rows and columns. This produces the stated nonnegative recurrence with a strictly positive denominator up through the last remaining cell. When no cells remain, only the empty moment is used.

The supersolution identity is exact. Its first step follows from r <= a-1 and beta >= (a-1)/(n-a+1), so the argument does not invoke an undefined negative-order moment. For later steps, r+2j-2 <= 2(a-1) and j-1 <= a-1 hold whenever r+j <= a. The beta simplification in the square-root range follows from sqrt(a-1)/a <= 1/2.

The affine coefficients are nonnegative in their linear part for n >= 2. For a repeated centered cell, even powers are bounded by the second-power expression 1-1/n. Odd powers at least three are bounded by 1-3/n+4/n^2 <= 1-1/n. This explicitly removes the old exp(a/n) loss. Every inconsistent centered singleton has affine weight two, and every other expanded factor has weight at most one.

For compatible selections in different colors, product F_n(r_c) <= F_n(sum r_c) follows by pairing the factors of each descending factorial. The total selected count is at most a-h. This is stronger than bounding each color separately, and does not introduce a constant depending on the number of colors. Factoring n^(-a) through the subset expansion gives exactly the claimed product of affine weights.

The compatible uncentered example with n=a^2 has expectation 1/(n)_a. Its normalized logarithm tends to 1/2, proving optimality of the universal prefactor for this class. This does not claim optimality of every other factor in the inequality or a literature priority result.

Boundary checks include n=1, a=1, h=0, h=a, full depletion with no remaining singleton, and independent colors. The original stated graph reductions use the correct permutation sizes. Same-side entries in the bipartite matching model vanish and can be omitted before applying the bound. No end-to-end formal verification is asserted.

No unsupported inference was found. The manuscript should retain the exact factor as its primary bound and the optimal constant as its simpler corollary.
