# Irreducible intertwiner moments and the old-module baseline

Prepared 2026-11-15. This is a mathematical assembly from the frozen
regular-lift entropy, central, and sparse estimates. It makes no claim
of historical novelty. Its new exact cyclic-target uniform coefficient
is proved in `cyclic-lattice.md` and independently checked in the final
audit section below.

## 1. Exact moment theorem

Let `B` be a fixed connected simple nonbipartite `d`-regular base,
`d>=3`, on `h` vertices. Let `A_N` be the adjacency matrix of its
independent uniform `N`-lift. Fix an odd prime `p`, a monic irreducible
polynomial `g in Fp[t]` of degree `r`, and any companion matrix `R` of
`g`. Put

```
h_old = dim_Fp {X in Mat_(h,r)(Fp): BX=XR}
      = dim_Fp ker g(B).                                  (1)
```

Using the cyclic-target uniform coefficient lemma in Section 2,
the complete moment is

```
E #{Y in Mat_(hN,r)(Fp): A_NY=YR}
       =2 p^(h_old)+o_(B,p,g)(1).                         (2)
```

The limit in `N` is over **all** positive integers. No congruence
condition on `N`, invertibility of `R`, or semisimplicity of `A_N` or
`B` over `Fp` is required for (1)-(2).

## 2. Exact central coefficient used

The new central lemma, proved in `cyclic-lattice.md`, is:

> For any cyclic target `R in Mat_r(Fp)`, on a connected nonbipartite
> simple regular base of degree at least three and odd characteristic,
> the contribution from a sufficiently small fixed full-uniform
> directed-edge-table neighborhood is
> `p^(dim{X:BX=XR})+o(1)`.

The frozen `central-lift-uniform.md` already supplies the exact iid
models, relative local limit comparison, complete maximal lattice,
positive weighted precision, and negligible tails. Its general
comparison index is `p^(h r p^r)`. The new finite-field rank calculation
must show that the legal congruences on the compatible integer
direction lattice have rank

```
h r p^r -dim{X:BX=XR}.                                   (3)
```

Then the Gaussian sublattice density cancels the comparison index
to give the displayed coefficient. The compatible lattice is
parametrized by arbitrary integer root margins of total zero and
free edge-interaction interior cells; it reduces surjectively onto
the corresponding finite-field compatible space. Thus a proof of
(3), together with the frozen central analysis, is sufficient. The
odd-characteristic cyclic alternating-form argument is the intended
proof of (3).

For a cyclic target that is reducible, this lemma still describes
the **uniform** contribution, but (2) need not hold: proper invariant
subspaces then create additional zero phases.

## 3. Irreducibility leaves exactly two kinds of phase

The frozen zero-phase theorem for a connected nonbipartite base
classifies every zero of the exact star entropy exponent as:

* a common `R`-invariant subspace `H<=Fp^r`;
* one affine coset per old type satisfying the old-base intertwiner
  equation in `Fp^r/H`.

Because `g` is irreducible and has degree equal to the dimension of
`R`, the row-action module `Fp^r` is simple. Its only invariant
subspaces are `0` and the whole space. This assertion is unchanged
by transposing a chosen companion convention.

For `H=0`, the phases are precisely the point maps `a_i in Fp^r`
with `Ba=aR`. Their number is exactly `p^(h_old)`.
For `H=Fp^r`, there is just the full uniform phase: all cosets are
the whole alphabet and its uniform legal-star law is unique.
There are no intermediate phases.

## 4. Point phases, disjoint neighborhoods, and compactness

Every old point map lifts to an exact deterministic fiber-constant
intertwiner for every matching realization. The sparse point-map
estimate in `../sparse-lift-common-subspace.md`, with `H=0`, proves
that a sufficiently small support neighborhood contributes

```
1+O_(B,p,r)(N^(-(d-2))).                                 (4)
```

Distinct point maps differ on at least one complete fiber, of size
`N`. Choosing a support radius `epsilon N` with `epsilon<1/2` makes
these neighborhoods disjoint. Their union contributes
`p^(h_old)+o(1)`.

Choose the fixed uniform edge-table neighborhood small enough to
exclude all point centers, and then shrink the point support radii
so that it excludes their neighborhoods too. Such choices exist:
a point edge law has a single entry equal to one, whereas the uniform
edge law has all `p^(2r)` entries equal to `p^(-2r)`, a positive fixed
distance away. A change at `k` vertices changes only `O_B(k)` edge
table entries in total variation.

The exact configuration sum here has no internal pairings or
contiguity step. For legal star counts `n_i(s)` and compatible edge
tables `m_ij`, its summand is exactly

```
prod_i [N!/prod_s n_i(s)!]
 *prod_(edges ij) [prod_ab m_ij(a,b)!/N!].                  (5)
```

Uniform Stirling inequalities, including zero factorial arguments,
give

```
log(summand)=N Phi+O_(B,p,r)(log(N+1)).
```

There are only polynomially many tables for the fixed alphabet and
base. All zeros of `Phi` lie in the open neighborhoods just selected.
Their complement in the compact feasible-law polytope therefore
satisfies `Phi<=-eta<0`. Its total contribution is exponentially
small. Together with the exact uniform coefficient from Section 2
and (4), this proves (2).

## 5. Hom dimension without semisimplicity

For **any** square matrix `T` over `Fp`, let

```
mathcal H_R(T)={X:TX=XR}.
```

Choose a cyclic column vector `v` for `R`. Evaluation `X->Xv` is a
linear isomorphism

```
mathcal H_R(T) -> ker g(T).                               (6)
```

Indeed the vectors `v,Rv,...,R^(r-1)v` form a basis, so the relation
`TX=XR` forces

```
X R^j v =T^j Xv.
```

It also forces `g(T)Xv=Xg(R)v=0`. Conversely, any `w in ker g(T)`
defines a unique `X` by `X R^j v=T^j w`; the last basis relation is
consistent exactly because `g(T)w=0`. This proves (6).

As a result, `dim mathcal H_R(T)` is always a multiple of `r`: the
kernel `ker g(T)` is a vector space over `Fp[t]/(g)`, with `t` acting
as `T`. It counts `r` times the number of `g`-primary cyclic blocks,
not in general `r` times the algebraic multiplicity of `g` in the
characteristic polynomial.

For example, one block `g(t)^2` contributes only `r`, not `2r`, to
this Hom dimension. Thus the unrestricted formula
`h_old=r*mult_g(charpoly B)` would be false at a bad base prime.
If the base is semisimple at `g`, the two quantities agree. No
semisimplicity assumption on the **random lift** is needed anywhere.

## 6. Deterministic old embedding, including p dividing N

Let `J:Fp^h->Fp^(hN)` pull a vector back to be constant on each
fiber. This map is injective over every field and satisfies

```
A_N J=J B.
```

Therefore `X->JX` injects the old intertwiner space into the lift
intertwiner space, so its dimension is always at least `h_old`.
This uses no averaging map and never divides by `N`. In particular
`p|N` causes no loss of old modules and no exceptional sequence of
lift sizes.

Writing `h_N=dim ker g(A_N)` and using (6), equation (2) gives

```
E p^(h_N)=2p^(h_old)+o(1),       h_N>=h_old.
```

Both dimensions are multiples of `r`. Hence

```
limsup_N P[h_N>=h_old+r] <=1/(p^r-1).                     (7)
```

This is obtained by subtracting the deterministic baseline
`p^(h_old)` before Markov's inequality. It detects excess geometric
`g`-module multiplicity even if `A_N` is not semisimple modulo `p`.

## 7. Good primes for a fixed real old factor

Because the fixed integer symmetric base matrix is diagonalizable
over the reals, write

```
charpoly(B)=prod_(i=1)^s f_i(t)^(t_i),
m_B(t)=prod_(i=1)^s f_i(t),
```

with distinct monic irreducible integer polynomials `f_i`. The second
polynomial is the squarefree minimal polynomial and annihilates `B`
over the integers. Its discriminant is a nonzero integer.

Choose any odd prime not dividing `Disc(m_B)`. Then every reduction
`f_i mod p` is squarefree, reductions for distinct `i` are coprime,
and `B mod p` is semisimple because its minimal polynomial divides
the squarefree polynomial `m_B mod p`. These conditions require
excluding only finitely many primes; no prescribed factorization
pattern or congruence class of primes is required.

Fix one factor `f=f_i`, of degree `ell` and old multiplicity `t=t_i`,
and factor its reduction as

```
f mod p =prod_j g_j,       deg g_j=r_j,       sum_j r_j=ell.
```

For every `j`, good-base semisimplicity and the characteristic
polynomial identity give

```
dim ker g_j(B)=r_j t.                                    (8)
```

This establishes the algebraic-multiplicity formula precisely where
it is used, while (6)-(7) remain valid in arbitrary characteristic
for arbitrary lift matrices.

## 8. Rational-to-modular transfer for a new old root

The fiber-constant real subspace and its orthogonal complement are
both invariant under `A_N`. The old block is exactly `B`. The quotient
of characteristic polynomials

```
c_new,N(t)=charpoly(A_N)/charpoly(B)
```

is a monic integer polynomial: the old lattice generated by the
fiber all-one vectors is primitive and extends to an integer basis,
giving an integer block-triangular matrix with old block `B`.
Equivalently, use the exact invariant old rational subspace and
Gauss's lemma for the monic quotient.

If the new real spectrum contains any root of the irreducible old
factor `f`, then `f` divides `c_new,N` over the rationals. Since
`A_N` is real symmetric, this implies

```
dim_Q ker f(A_N)>=ell(t+1).                               (9)
```

Reduction modulo every prime cannot increase the rank of the integer
matrix `f(A_N)`. Thus (9) also holds for its modular kernel. At a good
prime, the factors `g_j` are pairwise coprime, so the standard Bezout
decomposition gives, for **any** modular matrix `A_N`,

```
ker f(A_N)=direct-sum_j ker g_j(A_N).                      (10)
```

One can apply polynomial CRT directly to the module `ker f(A_N)`,
which is annihilated by the squarefree polynomial `f mod p`.
Equation (10) does not assume semisimplicity of the full matrix.

The deterministic baseline (8) sums to `ell t`. Equations (9)-(10)
therefore force at least one index `j` with

```
dim ker g_j(A_N)>r_j t,
```

and the dimension must then be at least `r_j(t+1)` because it is a
multiple of `r_j`. By (7) and a finite union bound,

```
limsup_N P[new spectrum contains a root of f]
 <=sum_j 1/(p^(r_j)-1) <=ell/(p-1).                        (11)
```

For each fixed good prime there are finitely many factors `g_j`, so
all moment limits are taken with `p` and these factors fixed. Only
after this `N`-limsup is taken do arbitrarily large good odd primes
tend to infinity. No error estimate uniform in a growing prime is
being used. Equation (11) then tends to zero. A final union bound
over the finitely many old factors gives complete old/new real
spectral disjointness.

## Independent audit of cyclic-lattice.md

I independently derived the dependency equations before reading
`cyclic-lattice.md`, and then checked its entire proof against that
derivation. The following points pass.

1. The explicit compatible integer parameterization is correct,
   including `m(0,0)=u_i(0)+u_j(0)+sum_(a,b!=0)m(a,b)` in the
   zero-total direction space. Its reduction modulo `p` is surjective,
   so finite-field rank gives the exact integer sublattice index.
2. With labels as rows and dependencies as columns, an interaction
   transfer gives `h_i(a)=K_i a^T+k_i` and `K_j=-K_i^T`. Nonbipartite
   connectivity gives one common skew matrix `K`.
3. The root-margin functional is exactly
   `a(sum_j k_j-Rk_i)-aRK a^T`. Testing `a` and `-a` separates its
   linear and quadratic parts in odd characteristic. The quadratic
   condition is `RK=KR^T`, with the displayed sign and transpose.
4. The surviving linear equations are `BX=XR^T`. The adjoint
   Sylvester operator under the Frobenius pairing has this kernel,
   so its dimension is `h_old(R)` with no base semisimplicity
   assumption.
5. The cyclic alternating-form lemma allows degenerate forms.
   `RK=KR^T` makes the row action self-adjoint for
   `beta(a,b)=aK b^T`. A cyclic row writes every pair as
   `vf(R),vg(R)`; moving polynomials across the form makes the
   pairing symmetric in `f,g`. Skew-symmetry and odd characteristic
   then force it to vanish. No invertibility or diagonalizability
   of the target is used.
6. The full lattice index is `p^(h r p^r)`, while compatibility
   lowers the constraint rank by exactly `h_old` for a cyclic
   target. The Gaussian Riemann sum on the legal compatible
   sublattice has fraction `p^(-rho)` of the `Q` sum. Combined with
   the relative local limit ratio and exact `Q` normalization, this
   gives exactly `p^(h_old)`, rather than an unspecified bounded
   coefficient.
7. Both affine lattice hulls use the all-zero legal-star point, so
   their compatible intersections are its `N`-fold translate plus
   the respective direction lattices. Fixed finite-index lattice
   translations do not change their scaled Gaussian density.
   Every `N`, including `p|N`, is covered. The positive weighted
   precision and frozen tail estimate justify the growing-window
   truncation and its extension to a fixed neighborhood.

**Audit conclusion:** the exact cyclic uniform input is proved, and
there is no remaining conditional lemma in the irreducible moment
assembly (2). The phase assembly, Hom formula, deterministic embedding,
good-prime selection, and modular-to-real transfer above are verified
directly. The separately written `module-transfer.md` was also read
and agrees with these deterministic arguments.

No claim is made here for bipartite bases; their alternating edge
relation and additional phases need separate analysis. All bases,
fields, and targets are fixed before the lift-size limit. The result
contains no uniformity assertion for a growing base or a growing
prime, and no historical priority claim.
