# Why centering helps a random matching

Start with the [eight-page illustrated guide](manuscript-round-01/output/pdf/reading-guide.pdf). The [manuscript](manuscript-round-01/output/pdf/centered-permutation-products.pdf) supplies the complete arguments and source comparisons. This entry point explains the proof mechanism, what the extensions mean and where they enter problem 21.

## Cancellation comes from the pattern

A permutation matrix has exactly one entry equal to one in every row and every column. Centering means subtracting the mean 1/N. For separated diagonal cells,

$$
\mathbb E[(M_{11}-1/N)(M_{22}-1/N)]
=\frac1{N(N-1)}-\frac1{N^2}
=\frac1{N^2(N-1)}.
$$

For two cells in the same row, both indicators cannot equal one. Their centered product has expectation -1/N^2. The separated pattern gains an extra factor of about 1/N. Taking absolute values before evaluating the expectation would hide that gain.

## The proof in three moves

First retain all centered factors whose cells occur once and share no row or column with another requested cell of the same permutation. These are the isolated centered singletons. Expand the remaining cell factors only after using their indicator identity M^2=M.

Second condition on a compatible set of r selected matches. They occur with probability 1/(N)_r. Deleting their rows and columns leaves a uniform permutation U of size N-r. The original centering remains 1/N. Consequently Z=NU-1 has row sum r, not zero.

Third sum a row before taking absolute values. The moments of j separated Z entries satisfy

$$
(N-r-j+1)\mu_j
=(r+2j-2)\mu_{j-1}+(j-1)\mu_{j-2}.
$$

The initial values are mu_0=1 and mu_1=r/(N-r), with only the empty product used at full depletion. Every coefficient is nonnegative. The recurrence keeps the cancellation while turning the final bound into a positive calculation.

This proves Bordenave's requested product estimate. The exact positive calculation does more: it identifies the largest possible expectation for fixed support and singleton counts when there are zero, one or two conflicting centered singletons. The guide shows simple patterns attaining all three maxima. Repeated powers and additional independent permutation colors do not exceed those values.

## Why the first transition is cubic

For k distinct diagonal centered entries, divide the moment by its known parity-dependent leading term and call the result R_k. The error recurrence changes by order m^2/N at its mth step. Summing about m such changes produces order m^3/N. The proof makes that intuition exact through uniform lower and upper bounds.

Thus the leading term is relatively accurate exactly when k^3/N tends to zero. At k of order N^(1/3), an even number of extra triples and an odd number of extra triples have different exponential sums. They give a hyperbolic cosine and a normalized hyperbolic sine. This explains the two parity limits.

The positive partition formula makes the mechanism visible. Each block of size j carries weight N(j-1)(j-1)!. Pairs give the leading terms, triples give the first transition, and blocks of four mark the next scale. For six labels,

$$
Q_6=15N^3+430N^2+600N.
$$

The 430N^2 consists of 160N^2 from two triples and 270N^2 from a pair and a block of four. These are exact finite coefficients, not an asymptotic guess.

## Later corrections and their errors

The parity hyperbolic approximation remains accurate through k=o(sqrt(N)). At k^2/N tending to d, the omitted correction tends to exp(d/4). Adding exp(k^2/(4N)) extends relative accuracy to k=o(N^(3/5)). The next retained exponent extends it to k=o(N^(2/3)). The manuscript proves the complete hierarchy throughout sublinear ranges.

For the quartically corrected formula on k<=C sqrt(N), the optimal error has order N^(-1/4). At k approximately sqrt(N), its scaled signed error tends to -11/30 in even degree and 19/30 in odd degree. The manuscript gives an explicit finite bound as well as this sharp asymptotic statement.

A fuller formula keeps the falling factorial denominator, the entire action and the parity amplitude. It is valid for every 2<=k<=N. Its worst error has the smaller order N^(-1/3), with asymptotic constant 0.395496270091. The worst orders are odd and near 1.16540187318 N^(1/3). The guide plots the full signed profile. These two optimal rates concern two different formulas.

## How this answers the graph problem

A random lift assigns independent permutations to base edges. A biregular configuration matches L left half-edges with L right half-edges, where L=n_L d_L=n_R d_R. In both cases, expanding a norm moment produces mixed products of permutation entries. The theorem supplies the required probability bound for each pattern, including its centering and multiplicities.

The remaining spectral argument counts those patterns, controls tangles and translates a non-backtracking bound to adjacency eigenvalues. Section 8 explains the chain and the biregular algebraic bridge. A better bound for a single pattern does not automatically improve the final graph theorem.

The [contribution statement](CONTRIBUTION.md) explains exactly which results are being supplied. The [priority assessment](extension-round-02/PRIORITY_SYNTHESIS.md) credits the known recurrence, factorial inequality, permanent bounds and classical asymptotic methods. The [readiness note](extension-round-02/SUBMISSION_READINESS.md) separates completed mathematics from the remaining submission decisions.
