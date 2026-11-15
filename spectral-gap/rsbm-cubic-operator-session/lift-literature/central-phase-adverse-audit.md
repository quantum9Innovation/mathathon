# Adverse audit of the central phase and its exact coefficient

Audited 2026-11-15 against
`spectral-gap/rsbm-cubic-moment-session/central-types.md`.
Scope: the central-phase claim only, not the constant-phase or global
moment estimates. I tried to invalidate the support lattice, the
symmetry-intersection lattice, the covariance/precision, the Gaussian
normalization, and the absence of residue-class restrictions.

**Result: no actual gap found in this central-phase derivation.** The
coefficient is consistent with the exact value `p`. This conclusion uses
the explicit checks below, not an independence assumption between the two
local table increments. The full `2p+o(1)` moment theorem still needs its
separate constant-phase and outside-region arguments.

## 1. Independent exact integer-lattice computations

The script `verify_support_lattice.py` constructs every support point
directly from its four field labels, subtracts the `(0,0,0,0)` support
point, deletes the last coordinate of each zero-total table, and computes
the integer column Hermite normal form. It does not use the proposed
modular constraints or character classification.

The resulting exact indices in the fixed-total integer lattice are:

| p | Rank | Computed support-difference index | Claimed index |
|---|---:|---:|---:|
| 3 | 16 | 432 | `2^4 * 3^3` |
| 5 | 48 | 32000 | `2^8 * 5^3` |
| 7 | 96 | 1404928 | `2^12 * 7^3` |

The script then independently intersects this computed lattice with
symmetry and even diagonal. It starts with an explicit integer basis for
the symmetric, total-zero lattice and tests membership using the inverse
HNF basis. Reduction modulo 2 and modulo p gives intersection index

```
p=3: 2^8  * 3^2,
p=5: 2^16 * 5^2,
p=7: 2^24 * 7^2,
```

relative to the pair of symmetric, total-zero integer lattices, exactly
as claimed. These computations are independent finite-prime checks,
rather than a proof for all odd primes.

Run command:

```
nix-shell -p 'python3.withPackages (ps: [ps.sympy])' --run 'python3 spectral-gap/rsbm-cubic-operator-session/lift-literature/verify_support_lattice.py 3 5 7'
```

## 2. Character classification closes the general support-lattice issue

Here is the detailed check of the short character argument in the source.
Write the rows of the two character tables as `f_a(b)` and `g_d(e)` in
`R/Z`. Constancy on all support points requires

```
f_a(b)+f_a(a+d-b)+g_d(e)+g_d(a+d-e) = a common constant
```

for every four field labels. Fix a and vary d, so `a+d` ranges over the
entire field. Varying b shows that `f_a(b)+f_a(s-b)` depends only on s.
Taking `b=s` and then replacing s by `x+y` gives

```
f_a(x)+f_a(y)=f_a(x+y)+f_a(0).
```

Thus `f_a(b)=alpha_a+k_a b/p` with `k_a in F_p`. The same argument gives
`g_d(e)=gamma_d+l_d e/p`. Mixed differences of the support-constant
identity give

```
(k_a-k_a')(d-d')+(l_d-l_d')(a-a')=0 in F_p.
```

Using one pair of distinct a values and then one pair of distinct d
values forces `k_a=t a+k`, `l_d=-t d+l`. Substitution yields precisely
the two equations for `2alpha_a` and `2gamma_d` in the source. After
quotienting additive constants on each whole table, their choices of
halves give `2^(2p-2)` possibilities, independently of the `p^3` slope
choices. Distinct slopes are detected by within-row differences, so
there is no overcount between slopes and row signs.

Positive-definite covariance gives a full-rank support-difference lattice.
The character classification therefore counts the annihilator of its
finite quotient in the full integer lattice. This verifies the claimed
index for every odd prime, not just the three computed examples.

## 3. Symmetry and parity do not leave a missing restriction

In one symmetric table with total zero, diagonal parities have precisely
one relation: their sum is even. Any allowed diagonal-parity vector is
realizable, so imposing even diagonal has index `2^(p-1)`.

After that constraint, row parities are precisely the degree parities of
the off-diagonal complete graph. Its incidence matrix over `F_2` has rank
`p-1`. Any off-diagonal integer choice can be balanced to total zero by
an even diagonal adjustment, so the total-zero condition imposes no
additional restriction on these row-parity vectors. The second parity
index is consequently another `2^(p-1)`.

The two modular constraints are independent on this parity sublattice:
the diagonal perturbation `+2` at `(a,a)`, `-2` at `(0,0)` changes them by
`(a,a^2)`. Taking `a=1,-1` gives determinant 2, invertible at every odd
prime. Thus the modular factor is exactly `p^2`, independently of the
binary constraints.

The Euclidean covolume of the symmetric total-zero integer lattice is
`p 2^(d/2)`: the symmetric integer lattice contributes `2^(d/2)`, and
the primitive total functional has gradient J of norm p. These factors
give

```
covol(L)=p^5 2^(2p-2),
covol(K)=p^4 2^(d+4p-4),
covol(L)/covol(K)=p 2^(-d-2p+2).
```

I found no missing diagonal factor or an extra p-congruence here.

## 4. Covariance and the sign of the weighted quadratic

The two local tables are dependent. What is actually needed is that
their **cross-covariance is zero**. Each pair selected from `(A,B),(A,C)`
and `(D,E),(D,F)` consists of four independent linear forms of the
uniform tuple `(A,D,B,E)`, so every such pair of directed-edge labels is
independent. This suffices for zero cross-covariance. No higher-order
independence is required for the joint lattice local limit theorem.

Within one table, B and C are independent uniform given A, yielding
`Sigma=(2/p^2)(I+R)` on the total-zero space. Its inverse is
`(p^2/2)(I-R/2)`. Adding the pairing-weight quadratic gives

```
-1/2 <X,Sigma^{-1}X> + (p^2/8)||X||^2
 = -(p^2/8)(||X||^2-||RX||^2).
```

On the symmetric total-zero subspace, the compression of R has only
eigenvalues 1/2 and 0, with multiplicities p-1 and d. Hence the precision
eigenvalues are `p^2/8` and `p^2/4`, both strictly positive. There is no
flat or negative-precision direction left after imposing symmetry.

## 5. Pairing prefactor and cancellation

Independently applying Stirling at `t=2N/p^2` gives

```
P(m) ~ (2 pi t)^(d/2) 2^(p/2) (t/e)^N
         exp[(p^2/8)||X||^2],
(2N-1)!! ~ sqrt(2) (2N/e)^N.
```

Thus the source's one-block prefactor, including `2^((p-1)/2)`, is
correct. The local-limit dimension is `2r0`, so the joint density has
factor `(2pi N)^(-r0)(det Sigma)^(-1)`. The symmetric summation dimension
is `2s`, giving mesh density `N^s/covol(K)`. Consequently the N exponent
is `d-r0+s=0`.

The Gaussian integral divided by the covariance determinant is

```
I^2/(det Sigma) = (2 pi)^s 2^(p-1) p^(2d).
```

The remaining analytic prefactor is `2^(d+2p-2)`; multiplying by the
covolume ratio above gives exactly p. This verifies all powers of p, 2,
pi, and N in the displayed coefficient.

## 6. No affine-N obstruction found

For every N, the two tables `2N e_00` provide a symmetric, diagonal-even
point in the N-fold affine lattice. The differences of all symmetric,
diagonal-even feasible lattice points are exactly K by the lattice
description already checked. K has full rank in the symmetric
total-zero subspace. Its covering radius is a fixed finite constant
depending on p, so each affine translate has a point at distance `O_p(1)`
from the uniform center; positivity of entries follows for large N.

The source's tilted Fourier argument uses the maximal difference lattice,
not a larger ambient lattice. On its dual torus the characteristic
function has only one modulus-one maximum. This deals correctly with
periodicity and proves the relative moderate-deviation estimate on
every affine-lattice point in the central window. In particular, a
possible finite-N semigroup hole is not silently assumed away: the
positive relative local-limit asymptotic excludes such holes near the
mean for sufficiently large N.

Finally, the joint Cramer rate is analytic near the mean because the
finite support spans the full space and all support probabilities are
positive. The strictly positive weighted precision verified above
survives cubic errors after shrinking the fixed p-dependent
neighborhood. The resulting `exp(-c log^2 N)` tail dominates the
polynomial number of tables and the pairing prefactor. This makes the
fixed-neighborhood extension valid and leaves no N modulo p or 2
subsequence in the central-phase result.
