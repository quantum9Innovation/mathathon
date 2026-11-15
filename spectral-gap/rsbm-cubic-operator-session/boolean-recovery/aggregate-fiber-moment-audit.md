# Adverse audit: aggregate fibers give a universal binary moment exponent

Prepared 2026-11-15. I agree with the proposed improvement. The entropy
bound can be applied directly to the uniform distribution on each fiber
of ordered-star arrays with fixed aggregate stub tables. This eliminates
the count of local profile types, while retaining an exact finite
enumeration. The result is

```
E_config |ker_F2(A-(a-b)I)|
 <= e^12 (aN+1)^16 (bN+1)^8 = O_(a,b)(N^24).         (1)
```

Here `a>=2`, `b>=1` are fixed and `aN` is even. No Gaussian prefactor or
local central limit theorem is used.

## Exact fiber enumeration

A left ordered-star profile records its center `X`, its `a` internal
neighbor labels, and its `b` cross neighbor labels; a right profile is
defined analogously. Impose the local equation over `F_2` with eigenvalue
`a-b`. Let `Omega(m_+,m_-,h)` be the set of assignments of such profiles
to all labeled vertices with the specified three aggregate directed-stub
tables: the two internal tables and the forward cross table. The reverse
cross table is fixed to be the transpose of `h`.

For any fixed profile assignment, the number of compatible internal
pairings is exactly `W(m_+)W(m_-)`, and the number of compatible cross
stub bijections is exactly `prod_(u,v) h_uv!`. These depend only on the
three aggregate tables. Thus

```
E |ker| = sum_(m_+,m_-,h) |Omega(m_+,m_-,h)|
          * W(m_+)W(m_-) prod h_uv!
          / [(aN-1)!!^2 (bN)!].                     (2)
```

Empty or inadmissible fibers contribute zero. Every pairing and kernel
vector determines exactly one full ordered-star assignment. Conversely,
the stated matching counts count precisely the compatible pairings for
each assignment. There is no extra multinomial, orientation, or local
profile-type factor in (2).

## Why the single-vertex marginals have exactly the required edge laws

Fix a nonempty fiber and draw its full array uniformly. Independently
permuting the vertices in each block preserves this fiber. Independently
permuting the internal slots, or the cross slots, at any individual
vertex also preserves it: both the local sum constraint and the
aggregate tables depend only on the corresponding multisets of neighbor
labels.

The uniform array law is therefore exchangeable in the vertices within
each block, with common profile marginals `q_+,q_-`; each marginal is
invariant under internal-slot and cross-slot permutations. Since the
aggregate tables are deterministic in the fiber, these common marginals
have internal edge laws exactly

```
F_+=m_+/(aN),    F_-=m_-/(aN),
```

and cross edge law exactly `G=h/(bN)`. Their central and neighbor
marginals satisfy the same consistency identities used in the earlier
entropy inequality. For example, exchangeability identifies the
expected first internal-slot count at a vertex with the table divided
by `aN`; slot invariance makes the first slot equal to the average slot.
No independence of the vertex profiles is asserted or needed.

## Entropy bound on the entire fiber

Because the full array is uniform on the finite fiber,

```
log|Omega| = H(full array)
           <= N H(q_+)+N H(q_-).
```

Deleting the last internal neighbor in each profile and using
conditional entropy subadditivity, exactly as in the general entropy
argument, gives

```
H(q_+)+H(q_-)
 <= (a/2)(H(F_+)+H(F_-))+b H(G),                    (3)
```

for `a>=2`. This is the nonpositive-exponent inequality; for `a=2`
the internal mutual-information coefficient is zero, which is still
enough for (3). The argument uses only the local linear equation,
slot invariance, and the aggregate edge consistency.

Crucially, (3) holds for the actual one-vertex marginals of the uniform
fiber law. They need not correspond to an integral local type. Applying
entropy directly to this law already counts the union of all local
types in the fiber, so multiplying by a number of local types would be
unnecessary.

## Factorial prefactors and number of aggregate tables

For a binary symmetric internal table of mass `aN`, elementary uniform
factorial inequalities give

```
W(m)/(aN-1)!!
 <= e^4(aN+1)^4 exp[-(aN/2)H(m/(aN))].
```

For the binary cross table of mass `bN`, the analogous bound is

```
prod h_uv!/(bN)!
 <= e^4(bN+1)^4 exp[-bN H(h/(bN))].
```

Multiplying these inequalities with the fiber bound (3) cancels the
entropy exponent exactly. Every summand in (2) is at most
`e^12(aN+1)^8(bN+1)^4`.

Each binary internal table has four entries in `0,...,aN`, and each
cross table has four entries in `0,...,bN`. Ignoring symmetry, parity,
total-mass, and marginal constraints only increases the number of
triples, giving the upper bound

```
(aN+1)^8(bN+1)^4.
```

This proves (1). More explicitly, its right side is at most
`e^12(a+1)^16(b+1)^8 N^24` for `N>=1`. Conditioning all graph factors
simple costs a positive degree-dependent constant, so the exponent 24
also holds in the required uniform simple model.

## Algorithmic consequence and prototype update

Use the affine binary system `(A+dI)z=b 1`, with `d=a+b`. Its direction
space is `ker_F2(A-(a-b)I)`. The planted label bits supply a solution.
By (1), the probability that it has more than `N^27` solutions is
`O_(a,b)(N^-3)`. Otherwise, exhaustive enumeration and exact verification
of crossing degree `b` take `O_d(N^28)` elementary bit operations using
packed label lookups.

The generic `recover_regular` prototype now uses cutoff exponent 27
for all fixed parameters. Both test suites were rerun with this cutoff.
The general sampling suite still recovers every requested shuffled
uniform-simple example, including `a=4`, odd `N=101`, and `b=1,2,3`.
