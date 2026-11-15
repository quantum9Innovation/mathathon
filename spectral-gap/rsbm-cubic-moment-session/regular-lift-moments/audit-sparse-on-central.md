# Independent audit of central-lift-uniform.md

Prepared 2026-11-15 by the sparse-boundary worker. I read the entire
central note, including its scalar refinement and unequal-alphabet
bipartite appendix. I find no remaining gap in the bounded uniform-phase
statement or its extension to zero-dimensional sides. The checks below
record the points needed to combine that statement with the boundary
induction.

## Exact normalization

For one alphabet of size `q`, the legal local-star count is exactly
`q^d`: choose the root and any `d-1` neighbors, and determine the last
neighbor by the equation. This is independent of the rank of `R`.
For the independent-neighbor model the count is `q^(d+1)`.

For a prescribed set of directed neighbor labels, the compatible
matching count at one base edge is exactly `prod_ab m_ab!`; division
by `n!` gives the matching probability. Thus

```
E Z_R =q^(dkn) E_P W(M)
```

has neither a missing endpoint-label factor nor a duplicate permutation
factor. For model `Q`, summing weighted assignments produces exactly
`q^(kn)` root assignments per lift, so

```
q^(dkn) E_Q W(M)=1.
```

This identity is especially useful: the central estimate compares the
same nonnegative weight in two finite probability models, preserving
all Gaussian and lattice constants automatically.

In the bipartite appendix, with alphabet sizes `u,v`, every legal left
star has `u v^(d-1)` choices and every legal right star has
`v u^(d-1)` choices. Since a regular bipartite base has equal part
sizes and `e=d k_L=d k_R`, the total legal count is `(uv)^(en)`, exactly
as in equation (20). The independent-neighbor count divided by the
number of root assignments is likewise `(uv)^(en)`. The two identities
in (21) therefore check, including `u=1` or `v=1`.

## Common-row covariance and real spans

For a local test array `f_j(a,b)`, condition on the root `A=a`.
Under the legal law, any two distinct neighbors are independent
uniform because `d>=3` leaves another slot to absorb the sum. They are
also pairwise independent under `Q`. The variance is therefore the
sum of conditional variances plus the variance of the sum of row
means, in both models.

On the actual Euclidean space of arrays with common row sums, the
common-row mode has covariance eigenvalue `d/(q_i q'_i)` and every
row-centered mode has eigenvalue `1/(q_i q'_i)`. For example, a common
row test mode `f_j(a,b)=g(a)` has squared Euclidean norm
`d q'_i sum_a g(a)^2` and variance
`d² sum_a g(a)^2/q_i`; their ratio is `d/(q_i q'_i)`.
This verifies both (8) and unequal-alphabet (22), with the indicated
Euclidean normalization.

The positive covariance proves the full real span in the claimed
common-row space. Equivalently, at a fixed root, any real-valued sum
`sum_j f_j(b_j)` constant on `sum_j b_j=s` forces the row functions to
be constant: using a third slot to compensate makes their additive
increments independent of their arguments, and a finite group has
no nonzero additive homomorphism into `R`. Thus there is no hidden
real linear restriction, including when the target map is singular.

## Maximal integer lattice

The `Q` differences generate the full common-row integer lattice:
within-row label transfers generate its centered directions, while
changing a root with all its neighbor labels held at zero generates
the common-row directions. This claim is about a generated lattice,
so negative combinations of support differences are legitimate.

For `P`, the per-root sum condition in (9) gives one congruence valued
in the opposite alphabet. These congruences are independent: one can
change the target label in one slot within one root row without
affecting its root margin or any other row congruence.

The character argument proves exhaustiveness, rather than just
necessity. On a fixed root row, all slot characters have a common
additive character of the opposite vector space; the remaining row
constants are already accounted for by common-row restrictions.
There are exactly `q'_i` independent character choices for each of
the `q_i` root labels. Consequently the local index is
`(q'_i)^(q_i)`, giving

```
I=q^(kq),
I_bip=v^(k_L u) u^(k_R v).
```

These are the maximal support-difference lattices required by the
local limit theorem. The all-zero support point makes the linear
case compatible for every `n`. In the affine appendix, legal affine
support sets remain subsets of the `Q` affine support set; compatibility
may be empty, in which case the contribution is zero. No particular
residue of `n` is needed for the upper bound.

## Relative local limit comparison and tails

The note uses a relative tilted local limit estimate throughout the
`sqrt(n)log n` window. Its hypotheses hold: fixed finite support,
positive covariance on the claimed real span, and the exact maximal
lattice just established. The tilt is `O(log n/sqrt(n))`, and the
rate-function Taylor error is `O(log³n/sqrt(n))=o(1)`. Fourier inversion
has one maximum on the maximal-lattice torus, with uniform exponential
decay away from that maximum for small tilts.

Since means and covariances coincide for `P,Q`, their point-probability
ratio is precisely `I(1+o(1))` on the legal affine lattice, uniformly in
that window. Multiplication by the nonnegative factorial weight is
safe under this relative estimate. Summing and using the exact
normalized `Q` identity bounds the window by `I+o(1)`.

The extension to a fixed small neighborhood also checks. The local
rate function is analytic near its mean by the inverse function
theorem for the positive covariance. The Stirling expansion of one
edge's factorial weight is

```
(uv)^(-n) (2pi n)^((uv-1)/2) (uv)^(-uv/2)
 *exp[(uv/2)||X_edge||²](1+o(1)),
```

which agrees with (24) and specializes to (14). The linear Taylor
term vanishes because each edge table has fixed total `n`.

For compatible fluctuations, the decomposition

```
X_ij=r_i/q_j+r_j/q_i+Z_ij
```

is orthogonal on each edge: `Z` has zero row and column sums, and the
two root-margin terms are orthogonal because their margins have zero
total. The total directed norm counts each edge twice. Combining
the covariance density with the factorial exponential gives

```
-1/2 sum_i q_i||r_i||² -(uv/2)sum_edges||Z_ij||².
```

This verifies (16) and (25), with no missing factor two. The form is
strictly negative on every nonzero compatible tangent. Cubic
remainders are dominated after shrinking the fixed neighborhood.
Chernoff plus uniform Stirling then gives a polynomial times
`exp[-c||m-nmu||²/n]`. Outside the logarithmic window,
`exp[-c log²n]` beats both this polynomial and the polynomial count of
possible tables. Thus no entropy-only assertion is used for the tails.

## Dimensions and zero-dimensional side checks

The full local dimension is

```
(q_i-1)+d q_i(q'_i-1).
```

Compatible arrays have freely chosen root margins and one zero-row,
zero-column interaction per edge. Their dimension is therefore

```
sum_i(q_i-1)+e(u-1)(v-1).
```

The difference of ambient and compatible dimensions is `e(uv-1)`,
exactly twice the power of `n` in the matching factorial prefactor.
The equal-alphabet formulas (7),(15),(17) are the same calculation.

If `u=1`, the left root-margin modes and all edge interactions are
absent. Right root-margin modes remain and have the strictly negative
coefficient `-v/2`. The left legal-neighbor sum law still has full real
covariance on its `d(v-1)`-dimensional span for `d>=3`. The index becomes
`v^(k_L)`, matching the one opposite-group congruence at each left root
row. All formulas continue to hold. The case `v=1` is symmetric.
If `u=v=1`, the entire space is zero-dimensional and the unique
assignment has deterministic contribution one, as handled separately.

## Scalar refinement

The optional exact scalar coefficient for nonbipartite bases also
checks. Interaction transfers force every dependence coefficient to
be affine in its scalar label, with opposite slopes on adjacent
vertices. An odd cycle in odd characteristic forces the slopes to
zero. The remaining dependence space is exactly
`ker(B-lambda I)`. The compatible integer lattice reduces surjectively
onto its finite-field compatible space, as seen from the root-margin
and free-interior-cell parametrization, so no rank or saturation factor
is missing. The fraction of the Gaussian sum in the legal sublattice
is `p^(-(kp-t))`; combined with `p^(kp)` from the local limit comparison
this leaves `p^t`.

Under normalized `Q` weighting, a random lift with iid uniform root
labels has iid matched label pairs along any fixed base edge. Their
table lies in the logarithmic window with probability `1-o(1)`, by
Chebyshev and a finite union bound. Hence the normalized central
`Q` contribution tends to one. This justifies the asserted exact
scalar coefficient, not just its upper bound.

## Conclusion

The bounded central contribution is justified for arbitrary target
maps and every characteristic, including unequal bipartite alphabets
and zero-dimensional sides. It combines with the independently proved
affine-coset boundary estimate and the finite zero-phase classification
without an uncovered normalization, lattice, or local-limit condition.
