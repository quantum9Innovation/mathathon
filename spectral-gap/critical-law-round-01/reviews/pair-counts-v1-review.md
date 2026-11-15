# Review of the critical marked-pair count proof

Date: November 15, 2026, America/Los_Angeles.

Decision: accepted as a complete paper proof at this exact revision. No mathematical finding remains open in the stated geometric theorems. This review does not establish historical priority or machine formalization.

## Reviewed input and exposure

The complete file `probability/pair-counts-v1.md` was read and checked against SHA256

`702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29`.

Prior exposure includes the round target, the proposed Poisson means, earlier fixed-degree exploration and nonbacktracking bounds, and the already reviewed effective-operator proof. The reviewer did not participate in writing this probability proof. The complete argument, including the deterministic conditional-host sampling lemma, was reconstructed from the frozen file. The source used for the fixed positive simplicity probability was inspected in prior rounds and is not a new independence assumption here.

## Conditional host calculation

Label symmetry exactly replaces the predetermined marked labels by an independent uniform subset for these joint statistics. The proof subsequently works under the simple host law. It never obtains a limiting Poisson probability by dividing by the simplicity probability.

The breadth-first exploration exposes only pairings from levels below the radius. Its collision bound is sufficient for the asserted sphere sizes. Unexposed edges between boundary vertices cannot shorten their distances to the root. A vanishing expected fraction of exceptional roots gives the simultaneous sphere estimate for all levels below the fixed offset cutoff. Deterministic maximum-degree bounds provide both domination and the auxiliary graph degree bound.

Lemma 3 is valid uniformly over the stated coloured hosts. For an edge tuple with v vertices and b nontrivial components, a spanning forest bounds its embeddings by C n^b Delta^(v-b). A nonmatching tuple has v-2b at least one. Multiplication by the uniform-subset probability gives

\[
 C(n\Delta p^2)^b(\Delta p)^{v-2b}=O(1/m).
\]

This also covers cyclic incidence patterns and shared endpoints across colours. Colours are disjoint edge sets, so falling factorials within each colour ensure that every edge in a tuple is distinct.

The replacement of inclusion probabilities by the matching probability is valid because the probability that a specified set is marked decreases with its size. The resulting error is bounded by the already controlled nonmatching contribution. The expansions of the fixed falling factorials and of (m)_(2h)/(n)_(2h) add O(1/m). The hypothesis Delta at least one implies p squared is O(1/n), which justifies the remaining polynomial error.

The moment argument supplies tightness and uniform integrability at every fixed order. Its nonnegative binomial expansion gives finite exponential moments of every subsequential limit, followed by the joint probability generating function. Thus the limiting mixed factorial moments do determine the asserted independent Poisson law. No moment-determinacy gap remains.

The conditional means are bounded uniformly and converge in probability under the simple host law. Their products therefore converge in expectation. Taking the expectation of the uniform conditional factorial estimate correctly proves the unconditional theorem.

## Means, cumulative counts and geometry

The identities

\[
 \frac{m^2q^{r_n}}n=\frac{m^{3/2}}{\sqrt n}q^{-\phi_n},
 \qquad
 a_\ell=dq^{\ell-1}
\]

give the mean d c^(3/2) q^(k-phi)/(2q). Summing the geometric sphere volumes gives d c^(3/2) q^(K-phi)/(2(q-1)) for the cumulative count. The missing constant term in the finite ball volume vanishes after multiplication by m squared over n. The same sampling lemma applies to disjoint bands, including a band containing every shorter positive distance. The deterministic volume bound gives the uniform O(q^(-L)) lower-offset tail needed for later truncation. Phase one and phase zero differ only by an integer reindexing.

The wedge count bounds matching failure by C m^3 q^(2R)/n squared, which is O(n^(-1/3)) at critical scaling. The unequal-length two-walk argument correctly subtracts exactly the identical-sequence contribution when the lengths agree. The remaining count is nonnegative. A collision-free exposed union is a tree, where two distinct nonbacktracking paths from one root cannot have a common endpoint. The configuration expectation and subsequent simplicity conditioning therefore give the asserted O(n^(-2/3)(log n)^2) marked multiplicity bound.

Loop erasure proves that any repeated-vertex path would give a second short nonbacktracking path between the same distinct marks. A shorter geodesic would do the same. Thus uniqueness forces simplicity and distance realization. Finally, if two short paths with four marked endpoints intersect, their nearer endpoints are within the cutoff of one another, contradicting the matching property. An interior additional mark also contradicts matching. This proves the stronger vertex-disjoint path conclusion without requiring a globally tree-like union of all marked balls.

## Scope

Both stated geometric theorems are accepted. The argument proves pair-count Poisson independence and fixed-cutoff path geometry. It does not by itself prove spectral convergence, a globally Poisson signed spectral process, or an unqualified full-sequence limit without a phase subsequence.
