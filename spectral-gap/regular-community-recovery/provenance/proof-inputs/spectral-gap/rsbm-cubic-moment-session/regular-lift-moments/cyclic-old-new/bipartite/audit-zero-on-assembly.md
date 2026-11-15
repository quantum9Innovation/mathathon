# Independent audit from the zero-target worker

Prepared 2026-11-15. Scope: the new bipartite packet only. The frozen
parent files remain unchanged. I independently derived the zero-target
moment and its mixed lattice in `zero-target-transfer.md`, then read
`bipartite-lattice-forms.md` and `mixed-phases.md`. Both pass. Review of
the final all-base assembly is recorded at the end once that file is
available. No historical priority assessment is made here.

## Forms and full-uniform coefficients

I checked the complete compatible-lattice argument. Its maximal local
index is `p^(k r q)` because the vector sum congruences are independent
in every root row, and the additive-character argument proves these
are all periods. The compatible integer parameterization by root
margins and free edge-interior cells reduces surjectively modulo `p`,
so field rank gives the exact finite-index kernel.

For a dependency, all arbitrary functions are forced affine-linear:
`h_i(a)=K_i a^T+k_i`. Connected bipartiteness gives `K_i=M` on the
left and `-M^T` on the right. Evaluating root-margin coefficients at
`a` and `-a` produces exactly the conditions that `RM` and `RM^T`
are skew, plus the old adjoint equations on the constants. The
constants contribute `h(R)` dimensions without assuming base
semisimplicity.

For invertible `R`, the substitution `L=RM` is bijective and the
second skew condition is precisely `R²L=L(R^T)²`. I independently
derived this equation and checked its signs and transposes. For
irreducible nonzero `g`, `Fp(lambda)` has degree one or two over
`Fp(lambda²)`; the degree-two case is equivalent to `g` even in odd
characteristic. The trace-balanced alternating-form proof is valid,
including when `p` divides the extension degree: it proves the trace
map nonzero from its polynomial, rather than assuming `Tr(1)!=0`.
It yields the exact extra form dimension `s` when `deg g=2s` is even,
zero in the non-even case, and one for scalar zero.

The finite-index Gaussian fraction, relative tilted local limit
comparison, exact independent-model normalization and positive
weighted precision retain these indices. The all-zero legal point
gives compatible affine lattices for every `N`, and their offsets
vanish after Gaussian scaling. Thus no parity or `p|N` restriction
is hidden in the full-uniform coefficients.

## Mixed phase classification and exact affine sections

For an even irreducible target, multiplication by `lambda` is
invertible. The two subspace inclusions therefore force

```
H_R=lambda H_L,       lambda² H_L=H_L.
```

The second condition makes `H_L` a vector space over
`K=Fp(lambda²)`. The full alphabet has dimension two over `K`, so
the only proper nonzero pairs come from one-dimensional `K`-lines;
there are exactly `p^s+1`.

For any such line, choose a different `K`-line as its complement on
the left and multiply it by `lambda` for the right complement.
The two summand pairs are preserved by both multiplication maps.
Their coordinates have maps `(I,C)`, where `C` multiplies by
`lambda²`. This is a literal decomposition of every lifted operator,
not merely a dimension count for the base or its semisimplification.
Consequently the old full dimension is exactly `h=2h_H`.

The same complement supplies a linear quotient section intertwining
both maps. Every quotient old point map therefore has an exact
old lift in the complement. Its fiber-constant pullback remains exact
for every random lift. Translation by that actual solution removes
all affine terms in the restricted problem. Thus the coefficient is
unchanged at every `N`; no solvability claim for an unrelated affine
forcing is used.

There are exactly `p^h_H` quotient point maps. The restricted uniform
coefficient is also exactly `p^h_H`: interaction matrices are `M`
and `-M^T`, the identity map forces `M` skew, and the other map forces
`CM=MC^T`. Cyclicity of `C` kills the alternating form, including
degenerate ones. The remaining linear dependencies are exactly the
adjoint old restricted kernel. Its dimension is `h_H`, and the
maximal/compatible lattice indices and exact Gaussian normalization
give the claimed coefficient.

## Narrow neighborhoods and the exact sum

The narrower mixed neighborhoods in `mixed-phases.md` are necessary
and sufficient. They impose small outside-coset root mass **and**
edge tables close to the uniform law on the chosen affine supports.
Taking only the broad coset-support condition would include point
subphases and double count their contribution; the written argument
explicitly avoids this.

On exact support, translating the exact quotient lift identifies the
chosen edge neighborhood with a fixed uniform edge neighborhood of
the restricted two-space problem. This is a bijective relabeling of
rows and columns, so the exact central coefficient applies with the
same finite prefactors. Off support, the whole sparse leakage count
is bounded by the frozen smaller moment times `O(N^(-(d-2)))`, hence
is `o(1)`; restricting further to the narrow edge region only decreases
it.

Distinct zero-phase centers have distinct root laws and therefore
distinct product edge laws. Since every vertex has neighbors, the
edge laws record each root law; uniqueness of the legal star law at
zero entropy prevents distinct centers with the same edge profiles.
There are only finitely many centers for fixed field and base. Small
edge neighborhoods can therefore be chosen disjoint, each containing
its corresponding zero phase in its interior. The residual compact
feasible-law region has a strict negative entropy gap and contributes
exponentially little by the exact type sum. Thus the mixed sum really
is `(p^s+1)p^h+o(1)`, not just an upper bound obtained from overlapping
regions.

The zero target is the same check with alphabets `Fp` and `{0}`.
Its full local index is `p^m`; compatible margins produce the map
`T^T S`, whose rank is `m-s0`. Transfers from label zero to label one
make the `S_i` independently surjective, proving saturation. The
coefficient is `p^s0` for each restricted uniform phase and there
are `p^s0` quotient maps per mixed side. Exact translations exist by
the direct one-sided split. My separate calculation agrees with the
four-family total `(p+3)p^h+o(1)`.

## Transfer checks independent of the final assembly

The fixed base must remain simple, connected and `d`-regular, with
`d>=3`. In its bipartite case the two parts have equal size, so the
cross matrix of every lift is square. For any field,

```
dim ker[0 X;X^T 0]=2 dim ker X.
```

The old baseline is likewise even and injects by fiber-constant
pullback for every `N`, including `p|N`. Thus an excess zero kernel
has dimension at least two above baseline. Subtracting that baseline
from the zero moment gives `(p+2)/(p²-1)`, which tends to zero.

The existing good-prime argument transfers `ker f(A_N)` rank,
not only modular characteristic-polynomial multiplicity. It remains
valid for bipartite bases and arbitrary modular Jordan structure.
Squarefree good-prime factorization permits polynomial CRT on
`ker f(A_N)`. For `g=t`, use the even-nullity increment; for nonzero
irreducibles, use their degree as the Hom-dimension increment.
This covers all factors without requiring a modular old/new direct
sum or division by `N`.

All limits keep the prime, its finitely many irreducible factors,
the base, and all maps fixed while `N` tends to infinity. Arbitrarily
large good odd primes are used only afterward. There is no need for
a prescribed factorization type or an error uniform in a growing
prime.

## Final assembly review status

I read the complete `all-base-old-new-disjointness.md` after it was
written. Its final assembly passes, with the following explicit
checks.

* It retains the precise fixed connected **simple** `d`-regular base
  scope, `d>=3`, and in the bipartite case derives equal part sizes
  from regularity. It does not claim the theorem for general degree
  frames, unequal part sizes, or rectangular cross matrices.
* It uses the three correct moment constants:
  `p+3`, `2`, and `2(p^s+1)`. The full-uniform, point and narrow mixed
  contributions add to each of these constants exactly, with no
  full restricted-moment substitution or point-phase double count.
* The mixed affine sections are actual old solutions in the
  complementary representation, so their pullbacks and translated
  restricted central neighborhoods work for every `N`. Positive
  leakage is controlled by the smaller homogeneous moment through
  the conditional rank coupling. The small edge neighborhoods can
  also be taken to imply the required sparse outside-coset bound:
  the outside root mass is bounded by the edge-table `L1` deviation,
  which is at most a fixed finite-alphabet multiple of its Frobenius
  deviation. Shrinking the finitely many radii therefore makes the
  edge-neighborhood description in the assembly consistent with
  the explicit two-condition description in `mixed-phases.md`.
* The zero threshold is two dimensions above the injected baseline.
  Both old and lifted nullities are even because their cross blocks
  are square. This remains true in bad characteristics and when
  `p|N`; no modular splitting or averaging is needed. The shifted
  Markov numerator is `p+2`, not `p+3`.
* For a good prime, the squarefree minimal polynomial of the base
  annihilates its reduction. Its individual irreducible old factors
  reduce squarefreely and pairwise coprimely. Thus the baseline for
  each modular factor is exactly its degree times the old integer
  exponent, while the random modular matrix may remain arbitrary.
* A real old/new collision gives increased rational nullity of
  `f(A_N)`. Rank reduction and polynomial CRT force excess in at
  least one geometric modular factor kernel. If that factor is
  zero, parity supplies the two-step threshold; all other factors
  use their degree as the dimension increment. The proof never
  transfers only an algebraic modular characteristic multiplicity.
* Every resulting probability bound is at most `2/(p-1)`:
  for the even nonzero case, putting `Q=p^s` gives
  `(2Q+1)/(Q²-1)<=2/(Q-1)<=2/(p-1)`;
  the zero case has `(p+2)/(p²-1)<=2/(p-1)`;
  the remaining case is at most `1/(p-1)`.
* There are finitely many fixed-base factors at each fixed good
  prime. Taking the `N`-limsup first therefore permits a finite
  union bound `2 deg(F)/(p-1)`. Arbitrarily large good primes are
  used only afterward. No prescribed splitting pattern, growing
  prime error bound, or interchange of limits is assumed.

**Final verdict: PASS.** The stated complete old/new real spectral
disjointness theorem is justified for every fixed connected simple
regular base of degree at least three, combining the frozen
nonbipartite theorem with this bipartite completion. I find no
remaining lattice, affine-coset, mixed-neighborhood, zero-parity,
good-prime, or limit-quantifier gap in the written packet.
