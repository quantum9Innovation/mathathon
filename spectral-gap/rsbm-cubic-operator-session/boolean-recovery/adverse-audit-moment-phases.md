# Adverse audit: entropy phases and near-constant bounds

Prepared 2026-11-15. Scope: `../../rsbm-cubic-moment-session/entropy-types.md`
and `near-constant.md`, excluding the central Gaussian/lattice evaluation.
I tried to find a counterexample or a missing range of types. I found no
hard error in these two components. They do not settle the separate
central prefactor calculation, which this audit does not certify.

## Equality classification and strict negativity

The ordered-star entropy identity is valid even on the boundary of the
probability simplex. If `s=(q+Tq)/2` for an involution `T`, invariance of
`s` gives `sum q log s=sum s log s`, so
`H(s)-H(q)=D(q||s)` exactly. Thus zero exponent forces actual swap
invariance, not merely invariance of the averaged edge tables.

After this step, equality gives `pi=mu x nu` and the conditional
factorizations stated in the note. Two distinct points `b,b'` in the
support of `nu` force the same conditional law `K_a` to be invariant
under the two reflections `u -> a-b-u` and `u -> a-b'-u`. Composing these
reflections gives translation by `b-b'`, or its negative depending on
composition order. Either translation acts transitively on the additive
group of a prime field. Therefore `K_a` is uniform. Symmetry of
`rho1(a,u)=mu(a)/p` then forces `mu` uniform, including exclusion of zero
entries of `mu`. The second block forces `nu` and `L_b` uniform.

The exceptional case `nu=delta_b` was checked separately. A symmetric
edge law with one marginal `delta_b` has both endpoint labels equal to
`b`. The local equation gives `2b=b-A`, so `A=-b`, including in
characteristic two. No extra phase is hidden on a proper support. Over
a non-prime field the translation argument would require modification;
the theorem in this component is expressly over a prime field.

There are therefore exactly the stated uniform point and the `p`
planted constant points in the zero set. Entropy is continuous on the
compact feasible domain, including tables with zero entries. For each
fixed prime, every closed region separated from those points has a
strictly negative maximum exponent. The polynomial count of types then
justifies the asserted exponential removal of that region.

The exact two-table combinatorial factor was also checked: assign central
labels in `N!/prod n_ab!` ways, then assign first and second ordered-star
profiles within each central class in respectively
`prod n_ab!/prod n1_abu!` and `prod n_ab!/prod n2_abc!` ways. Multiplication
gives exactly the numerator of formula (1). Distinguished slots are
retained, so swapping the two different neighbor labels costs no missing
factor of two.

## Near-constant support certificate

The support certificate remains valid with loops, parallel edges, and
finite-field cancellation. For a support of `k` individual coordinates,
let `s` be the number of matched pairs occupied on exactly one side and
`m=(k+s)/2`. At each of the `s` zero partners there must be at least one
internal edge from the support. At a touched zero coordinate in a pair
disjoint from the support, there must be two internal edges from the
support: exactly one nonzero summand cannot vanish in a field. A repeated
edge counts twice, as required by its two stubs. A loop at a support
coordinate contributes two support stubs and one internal edge, exactly
as used in `2k=2e+B`.

Thus `B>=s+2t`, `r<=t`, and

```
E-(m+r) = k+B/2-(k+s)/2-r >= k/2+t-r >= k/2.
```

This is the key gain. The counting step selects supervertices, occupancy
patterns, values, and a valid colored partial matching on distinguishable
stubs. Its intentional overcounts cannot lose an actual support
certificate. For `k<=N/4`, all pairing-probability denominators are at
least `N`, since each block has at most `2k` prescribed pairs. The
partial-matching count and the factorial sums yield the stated
`2k(Dq)^k(k/N)^(k/2)` bound with
`D=3*2^8*4^2*e^2=12288e^2`.

The ratio calculation is uniform from `k=2` through the field-dependent
linear cutoff. With the stated `epsilon_q`, its limiting upper bound is
`2/sqrt(128)<1/2`, leaving sufficient slack for the `1/N` endpoint error.
Support one is impossible because a zero entire block forces the other
block to vanish through the identity cross matrix. Consequently the
series starts at `k=2`, where its first term is `8D^2q^2/N`, and the
geometric sum is at most `16D^2q^2/N`.

This handles the whole mesoscopic range up to `epsilon_q N`; it is not a
fixed-support calculation extrapolated to growing support. The constants
may depend on fixed `q`. That dependence is harmless for a limit in which
`N` tends to infinity before the prime tends to infinity.

Subtracting `a sigma` is a bijection of the kernel, also for configuration
graphs. Distinct planted constants differ at all `2N` individual
coordinates, making the specified small balls disjoint. Their expected
contribution is therefore exactly `q` plus the vanishing sparse term.
Conditioning simplicity changes only that nonnegative vanishing term by
a bounded factor; the deterministic `q` planted vectors retain coefficient
one. This conditioning step does not require a uniform-permutation
2-factor substitution.

## Explicit coverage of all types

There is no gap between the sparse-support and strict-entropy arguments.
For each fixed prime choose a constant-phase neighborhood small enough
that its central pair marginal assigns mass at least `1-delta` to
`(a,-a)`, with `2delta<=epsilon_p`. Every vector counted there differs
from `a sigma` at no more than `2delta N` individual coordinates, so the
entire table contribution is bounded by the near-constant vector count.

Choose the fixed relative uniform neighborhood from the coercivity
argument and make these neighborhoods disjoint. Outside all the fixed
neighborhoods, compactness gives a strictly negative entropy bound. Inside
the uniform neighborhood, the proved quadratic bound removes deviations
larger than `log(N)/sqrt(N)` with a loss of order `exp[-c_p log(N)^2]`,
which dominates all fixed-prime polynomial Stirling and type-count
prefactors. Only the central uniform window remains for the separately
audited prefactor calculation.

Thus these components reduce the desired sharp moment to that one
central window. They do not themselves supply its coefficient or its
dependence on the prime.

## Independent exact certificate for the N=8 recovery example

The Python test now checks the claimed real multiplicity using exact
rational arithmetic, independently of the binary recovery calculation.
For the two cycles already specified in the earlier kernel note, the
integer matrix `A-I` has rational rank 14. Both listed independent integer
vectors lie in its kernel. In the reduced `8x8` matrix
`K=(D-I)(C-I)-I`, the leading `6x6` minor has determinant exactly `-4`,
verified by fraction-free Bareiss elimination. These provide upper and
lower rank certificates showing real corank exactly two. The same graph
has 16 affine binary solutions and only the planted pair of Boolean
solutions, as independently checked by exhaustive enumeration.

These checks live in `test_binary_recovery.py`, with results in
`binary-recovery-results.json`.
