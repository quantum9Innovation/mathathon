# Independent reconstruction of the permutation proof

Reviewed revision: [permutation-proof-v1.md](../audit-2026-11-14/permutation-proof-v1.md).
SHA256: 8454b19f74d6f7f11ad784b6227e221837dd41887f22f1ff800af92cc7299db7.

Verdict: the stated bound follows from the written argument. No mathematical gap was found in this revision. This verdict covers the mixed product estimate, not literature novelty or the later spectral trace argument.

## Checks that matter

The auxiliary density has shape n-r+1. Its inverse moments are exactly reciprocal falling factorials, so the moment identity and recurrence have the correct shift. Integrating the derivative of exp(-x) x^(n-r) f(n/x) gives the displayed identity. The boundary exponent is positive throughout the stated range.

For the induction constant, r+j is at most a. Therefore r+2j-2 is at most 2(a-1), and j-1 is at most a-1. Since a is at least two in this part of the proof and n is at least a squared, the chosen beta is at most sqrt(2). These inequalities give the displayed strict bound and establish the induction, including its first step.

The compatible-set identity conditions only on actual prescribed matches. It does not reveal arbitrary images and preimages. That distinction makes the residual permutation size n-r correct and avoids both failures in the cited conditioning formula.

The coefficient expansion retains every isolated centered singleton until after cancellation. For the other cells, the coefficient of the indicator is nonnegative, repeated centered powers cost at most 1+1/n, and inconsistent centered singletons cost at most two. Incompatible prescribed sets contribute zero. The global falling-factorial prefactor is bounded before combining independent colors, so no constant grows with their number.

The a=1 branch covers n=1, 2 and 3 separately. A lone centered singleton has expectation zero. All other lone factors have absolute expectation at most 1/n. The proof therefore includes every parameter in its statement.

## Independent source check

Direct enumeration of all 24 permutations of four elements confirms both counterexamples to the source's conditional assertion. The shared-row event has six outcomes and conditional probability one. The disjoint-cell event has two outcomes and conditional probability one half. The printed bound is one third in both examples. The unconditional centered products are respectively -1/16 and 1/48.

The exact results are in [source-counterexamples.json](source-counterexamples.json). They refute the intermediate assertion, not Proposition 28.

## A possible sharpening

The recurrence also admits beta equal to sqrt(a-1) divided by the difference sqrt(n)-sqrt(a-1). Indeed, (n-a+1) beta squared equals 2(a-1) beta plus a-1. This is exactly the inequality required by the same induction. The investigator has been asked to freeze a separate revision for this change. The present verdict remains attached to revision 1.

## Literature boundary

A subsequent primary-source check identified [Collins and Nagatsu, Weingarten calculus for centered random permutation matrices](https://arxiv.org/abs/2503.18453), published in Algebraic Combinatorics in 2026. It treats these moment phenomena. Its precise overlap with the recurrence and the full mixed-product estimate must be stated in the next revision. Independent rediscovery is not evidence of novelty.
