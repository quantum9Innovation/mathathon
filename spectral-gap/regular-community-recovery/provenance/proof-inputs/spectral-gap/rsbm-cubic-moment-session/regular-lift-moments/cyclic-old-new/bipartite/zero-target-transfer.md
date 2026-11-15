# The zero companion target on bipartite regular lifts

Prepared 2026-11-15. This note proves the zero-target moment, including
the mixed-phase integer lattices and every lift-size residue, and
records the resulting real old/new transfer. It uses the frozen
regular-lift type, relative local limit, and sparse-boundary estimates.
It makes no historical priority claim. All writes for this extension
are confined to the new bipartite directory.

## Statement

Let `B` be a fixed connected simple bipartite `d`-regular graph,
`d>=3`, with `m` vertices on each side. Write, with compatible left
and right orderings,

```
B=[0 T; T^T 0],        A_N=[0 X; X^T 0].
```

Here `X` is the square `mN`-by-`mN` cross matrix of the random `N`-lift.
Fix an odd prime `p`, and let all ranks and kernels in the next
formulas be over `Fp`. Put

```
s0=dim ker T=dim ker T^T,       h=dim ker B=2s0.
```

Then, with `p` and the base fixed and `N` tending through all positive
integers,

```
E |ker A_N|=(p+3)p^h+o_(B,p)(1).                          (1)
```

There is no exclusion of primes dividing `d` or lift sizes divisible
by `p`. Moreover

```
limsup_N P[dim ker A_N>h] <=(p+2)/(p²-1).                 (2)
```

The notation `|ker|` means the cardinality of the finite-field
kernel, while `dim ker` means its dimension.

## 1. The four kinds of zero-entropy phase

For scalar zero target, the bipartite zero-phase classification has
`H_L,H_R` independently equal to `0` or `Fp`. The maps between them
are zero, so all four choices are allowed.

* `H_L=H_R=0`: the point maps are the old vectors
  `(a_L,a_R)` with `T a_R=0`, `T^T a_L=0`. There are `p^(2s0)=p^h`.
* `H_L=H_R=Fp`: the one full-uniform phase.
* `H_L=Fp,H_R=0`: the left coset is all `Fp`, while right cosets
  are points `a_R in ker T`. There are `p^s0` such phases.
* `H_L=0,H_R=Fp`: the symmetric collection, indexed by
  `a_L in ker T^T`, again with `p^s0` phases.

There are no other scalar subspaces or zero phases. The individual
phase centers include their unique legal-star laws, not merely their
root marginals.

The frozen sparse point estimate gives total point contribution
`p^h+o(1)`. The frozen exact scalar bipartite central calculation
(the last subsection of `../../central-lift-uniform.md`) gives
the full-uniform contribution

```
p^(h+1)+o(1).                                           (3)
```

Its extra dependency is one alternating slope between the two sides;
the root quadratic constraint vanishes at zero target. The mixed
coefficient requires a separate calculation, supplied next.

## 2. A mixed coset translates exactly to a two-space homogeneous model

Fix a phase `H_L=Fp,H_R=0` and its right point map `a_R in ker T`.
For assignments entirely in these cosets write

```
Y_L=z_L,         Y_R=J a_R,
```

where `J` means fiber-constant pullback. The left equations hold
identically because `X J a_R=J T a_R=0`. The right equations are

```
X^T z_L=0.                                              (4)
```

Thus translation of the right labels by `a_R` gives **exactly** the
homogeneous two-space system with left alphabet `Fp`, right alphabet
`{0}`, and zero maps in both directions. No affine obstruction
remains. This translation is valid for every lift and every `N`.

Within the chosen mixed phase, the left law is uniform, not a point
law. Hence its contribution is the **uniform-phase** contribution
of (4). Using the complete restricted moment instead would double
count point phases; only its boundedness is used for leakage below.

## 3. Exact mixed central coefficient p^s0

Orient every base edge from left type `i` to right type `j`. The
directed table on that orientation is a `p`-by-`1` vector of left
root counts. At a fixed left type its copies in all `d` edge slots
are identical. At a right type the root is the sole zero label and
each slot has a `1`-by-`p` table of neighbor counts.

### Before matching compatibility

Use the independent-neighbor `Q` model from the unequal-space
appendix, with `u=p,v=1`. Left stars just choose one uniform root
label. Right stars choose `d` iid uniform left-neighbor labels.
The legal `P` model constrains each right star's neighbor sum to zero;
the left law is unchanged. Its exact normalizations are

```
E Z_restricted=p^(dmN) E_P W(M),
p^(dmN) E_Q W(M)=1.                                     (5)
```

They follow either from the frozen two-space normalization, or by
counting `p` legal choices per left site and `p^(d-1)` per right
site. Every matching edge still contributes `prod_a m_a!/N!`.

The maximal `P` lattice has one scalar congruence per right old type:

```
C_j= sum_(i~j) sum_(a in Fp) a m_ji(0,a)=0 mod p.           (6)
```

There are no left congruences, since the opposite alphabet there is
the zero group. On the full independent-neighbor common-row integer
lattice, the `m` congruences in (6) are independent: change one
neighbor label in one right slot. Hence

```
[L0:L]=p^m.                                             (7)
```

These are all periods, rather than just necessary congruences. A
character constant on a right legal tuple `sum b_j=0` has slot
functions equal to constants plus one common additive character of
`Fp`, since `d>=3`. Its only period is therefore the one neighbor-sum
character in (6). Left stars have no additional periods. This is the
specialization of the frozen maximal-lattice proof and gives exactly
`p^m`, with no hidden parity factor.

### After matching compatibility

The compatible integer direction lattice `K0` is particularly
simple: choose freely, for each left type `i`, integers `n_i(a)`
with `sum_a n_i(a)=0`. Every edge table is then this vector or its
transpose. There are no interaction coordinates because one edge
alphabet has size one. Thus

```
rank_Z K0=m(p-1).
```

Put `S_i=sum_a a n_i(a) in Fp`. The `S_i` are independently and
surjectively obtainable from `K0`: the integer margin transfer
`n_i(1)=1`, `n_i(0)=-1` changes only `S_i`, by one. Reduction of `K0`
modulo `p` therefore has no saturation obstruction. Under compatibility,
the congruence vector (6) is exactly

```
C=T^T S.
```

Its rank is `rank T=m-s0`, so the compatible legal sublattice has
index

```
[K0:K]=p^(m-s0).                                       (8)
```

### Affine N-residues and the Gaussian fraction

The all-zero star is legal and compatible. If `v0` denotes its
one-copy table array, the two `N`-fold affine lattice hulls are
`N v0+L0` and `N v0+L`; their compatible intersections are
`N v0+K0` and `N v0+K`. This is an exact statement for every `N`.
The continuous uniform means `N/p` need not be integral and need
not belong to these lattices. Each fixed-index lattice nevertheless
has a point within bounded distance of the mean in its real span;
after division by `sqrt N`, that offset tends to zero. Thus there
is no `p|N`, parity, or affine-coset exception.

The frozen unequal-space calculation proves identical positive
covariance under `P,Q`, a relative tilted local limit theorem on the
`sqrt(N)log N` window, and strictly positive weighted precision.
Here the full dimension is `m(d+1)(p-1)` and the compatible dimension
is `m(p-1)`; their difference `dm(p-1)` is twice the matching Stirling
power. The weighted Gaussian has exponent

```
-(p/2) sum_(left i) ||r_i||²,
```

with no right-margin or edge-interaction directions. It is positive
precision on every remaining nonzero direction.

Accordingly the `P/Q` point-probability ratio is `p^m(1+o(1))` on
the legal lattice, while its compatible Gaussian sum has fraction
`p^(-(m-s0))` of the full `Q` compatible sum. The exact normalization
in (5) makes that full `Q` sum tend to one: under normalized weighting,
the left root labels are iid uniform, so their finitely many fiber
histograms lie in the logarithmic window with probability `1-o(1)`.
The relative estimate is safe under the factorial weights. The frozen
positive-precision tail estimate then extends the window to a fixed
uniform neighborhood. The exact mixed restricted coefficient is
therefore

```
p^m p^(-(m-s0))=p^s0.                                  (9)
```

Translation by the fixed old right point map is an exact relabeling,
so (9) is unchanged for every `a_R in ker T`. Each of the `p^s0`
phase centers consequently contributes `p^s0+o(1)`. The complete
left-uniform/right-point family contributes

```
p^(2s0)+o(1)=p^h+o(1).                                 (10)
```

The right-uniform/left-point family is the transpose calculation,
also contributing `p^h+o(1)`.

## 4. Leakage and the exact four-family assembly

For clarity, a mixed phase neighborhood is chosen to require both
small total mass outside its prescribed cosets and edge laws close
to that phase's left-uniform/right-point edge laws. It is not the
entire coset-support neighborhood, which would include point phases.

Inside its exact coset support, its contribution is precisely the
restricted central calculation above. Outside that support, the
frozen bipartite sparse-boundary proposition bounds its contribution
by

```
O_(B,p)(N^(-(d-2))) M_(Fp,0)(N)=o(1),                    (11)
```

because the frozen bounded-moment theorem supplies
`sup_N M_(Fp,0)(N)<infinity`. This handles dependence between rare
defects and the bulk kernel size by the explicit matching-forcing
rank coupling; no independence assumption is made.

There are finitely many centers. Choose disjoint sufficiently small
neighborhoods of their distinct full legal-star laws, using the
corresponding edge neighborhoods and sparse coset radii just
described. All zero-entropy phases lie in these neighborhoods. The
remaining compact feasible-law region has exponent bounded strictly
below zero and contributes exponentially little by the exact type
sum and uniform Stirling bounds. Thus adding the four families gives

```
p^h +p^(h+1)+p^h+p^h+o(1)=(p+3)p^h+o(1),
```

proving (1).

## 5. Even nullity and shifted Markov

For every square matrix `X` over any field,

```
ker[0 X;X^T 0]=(ker X^T) direct-sum (ker X),
dim ker[0 X;X^T 0]=2(dim X-rank X).                       (12)
```

In particular `dim ker A_N` and `h=dim ker B` are both even.
Fiber-constant pullback injects the old kernel into the lift kernel
over every field, without dividing by `N`. Hence

```
dim ker A_N>=h,
dim ker A_N>h  implies dim ker A_N>=h+2.
```

Subtract the deterministic baseline `p^h` and use (1):

```
P[dim ker A_N>h]
 <=(E|ker A_N|-p^h)/(p^(h+2)-p^h),
limsup_N P[dim ker A_N>h] <=(p+2)/(p²-1).
```

This proves (2). The improvement from a one-dimensional to a
two-dimensional excess is necessary: the coefficient `p+3` alone
would not give a vanishing bound with a one-dimensional threshold.

## 6. Compatibility with the complete real old/new transfer

The deterministic good-prime transfer in `../module-transfer.md`
does not use nonbipartiteness. Let `f` be an old irreducible integer
factor of degree `ell`, with old multiplicity `t`, and choose an odd
prime avoiding the discriminant of the squarefree minimal polynomial
of `B`. Factor `f mod p=prod_j g_j` into distinct irreducibles.

A new real root of `f` forces `dim ker f(A_N)>=ell(t+1)` over `Q`;
modular rank reduction preserves this lower bound. Polynomial CRT
then gives `ker f(A_N)=direct-sum_j ker g_j(A_N)` over `Fp`, even if
the entire modular matrix is not semisimple. The old fiber-constant
embedding supplies baseline `dim ker g_j(B)=deg(g_j)t` for every `N`,
including `p|N`. Some factor must exceed its baseline.

For a factor `g_j=t`, the old dimension is even because `B` is
bipartite, and (12) forces any excess to be at least two; use bound
(2). The zero case therefore fits the same CRT union bound, with
no lost parity or baseline assumption. There can be at most one
such factor because the reduced polynomial is squarefree.

For nonzero factors, the companion Hom dimension is a multiple of
`deg g_j` without requiring modular semisimplicity. The nonzero
bipartite moments proved in `bipartite-lattice-forms.md` and
`mixed-phases.md` give the corresponding shifted Markov bounds

```
g nonzero, not even:  1/(p^r-1),
g nonzero and even, r=2s: (2p^s+1)/(p^(2s)-1).
```

Each tends to zero along arbitrarily large fixed good primes.
Uniformly for `p>=3`, both of these and the zero bound (2) are at
most `2/(p-1)`. Consequently these moment results give the concise
aggregate bound

```
limsup_N P[any old/new real spectral collision]
 <=2 deg(m_B)/(p-1),
```

where `m_B` is the squarefree minimal polynomial of the fixed base.
Letting good primes tend to infinity only after the lift-size limsup
then proves complete old/new disjointness for bipartite bases. Together
with the frozen nonbipartite theorem, this covers all fixed
connected simple regular bases of degree at least three.

The transfer itself is fully verified here, including the zero case.
The final all-base conclusion additionally uses the independently
proved nonzero-target bipartite moments; no unsupported nonzero
coefficient is assumed in the proof of the zero theorem (1).

## Independent cross-audit: bipartite-lattice-forms.md

After completing the independent zero-target calculation above, I read
all sections of `bipartite-lattice-forms.md`. Its full-uniform and
auxiliary mixed coefficients pass the following checks.

* The interaction relation gives one matrix `M` on the left and
  `-M^T` on the right. The root quadratic conditions are exactly that
  `RM` and `RM^T` be skew. For invertible `R`, the substitution
  `L=RM` converts the second condition to
  `R²L=L(R^T)²`; I independently derived this identity with the same
  signs and transposes.
* For irreducible nonzero `g`, the field index
  `[Fp(lambda):Fp(lambda²)]` is at most two. Its being two is
  equivalent to `g` being even in odd characteristic. In that case
  the subfield has size `p^(r/2)` and the full alphabet has dimension
  two over it. The automorphism and nonzero constant-term arguments
  cover every irreducible degree, including scalar nonzero targets.
* The trace pairing is nondegenerate. In particular its proof does
  not assume `Tr(1)!=0`: even if `p` divides the extension degree,
  the trace polynomial is nonzero of degree below the field size.
  Reconstructing `Omega` from all `Tr(c Omega)` yields a unique
  bilinear form, and balance transfers scalar multiplication to
  either variable. Alternation follows in odd characteristic.
  Thus the balanced alternating-form dimension is exactly
  `s n(n-1)/2`, giving `s` for the even irreducible case.
* The compatible integer table parameterization reduces
  surjectively modulo `p`. The dependency classification is both
  necessary and sufficient, so its dimension determines the exact
  finite-index lattice kernel, not merely a bound on a necessary
  constraint. The relative local limit comparison, exact `Q`
  normalizer and Gaussian lattice fraction retain that index for
  every affine `N`-translate.
* For the auxiliary two-map system `(I,C)`, the left map forces
  `M` skew and the right map gives `CM=MC^T`. Cyclicity of `C`
  kills every alternating form, including degenerate ones. The
  remaining linear dependency dimension is that of the adjoint
  old two-map operator, hence equals the old homogeneous solution
  dimension. The coefficient `p^(h_U)` is justified.
* The singleton-side auxiliary calculation is precisely (6)-(9)
  above, providing an independent check of its coefficient
  `p^s0`, saturation, Gaussian normalization, and all-`N` claim.

No gap was found in that forms/prefactor note. The separate nonzero
phase assembly and `all-base-old-new-disjointness.md` subsequently
passed independent review, recorded in `audit-zero-on-assembly.md`.
The all-base conclusion in Section 6 is therefore final within its
stated fixed simple regular-base scope.
