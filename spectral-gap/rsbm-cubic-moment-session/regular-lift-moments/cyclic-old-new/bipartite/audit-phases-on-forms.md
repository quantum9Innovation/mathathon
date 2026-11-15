# Fresh cross-audit of bipartite forms and zero-target transfer

Prepared 2026-11-15 after independently completing the mixed-phase argument. Audited `bipartite-lattice-forms.md` and `zero-target-transfer.md` in full. Frozen parent files are unchanged.

**Verdict: PASS**, within the stated scope of fixed connected simple `d`-regular bases, `d>=3`, and fixed odd prime fields. The exact full-uniform coefficients, even/non-even field dichotomy, zero-target mixed coefficients, and modular-to-real probability bounds are mutually consistent.

## 1. Matrix signs and the square-action form condition

The interaction relation is `K_j=-K_i^T`; on a connected bipartite base this permits `M` on the left and `-M^T` on the right. The root quadratic terms require `RM` and `R(-M^T)` skew. Replacing a matrix by its negative preserves this property, so the definition using `RM` and `RM^T` is correct.

For invertible `R`, put `L=RM`. Then `L` is skew, `M^T=-L R^(-T)`, and the second condition is that `R L R^(-T)` be skew. Its transpose is `-R^(-1)L R^T`. Multiplying the resulting equality on the left by `R` and on the right by `R^T` gives exactly

`R^2 L=L(R^T)^2`.

This is self-adjointness of **right** multiplication by `R^2` for `beta(a,b)=aL b^T`. The sign and both transpose positions agree with the row-label convention. No condition was silently imposed that `M` itself be skew before the root tests.

The arbitrary dependency functions become affine-linear by testing the interaction equation against coordinate rows; the remaining constants solve the Frobenius-adjoint old intertwiner equations. Thus the total dependency dimension is the stated `h(R)+b(R)`, without semisimplicity assumptions on the fixed base or target.

## 2. Irreducible polynomial dichotomy

For nonzero irreducible `g`, let `E=Fp(lambda)` and `K=Fp(lambda^2)`. The element `lambda` satisfies a quadratic polynomial over `K`, so `[E:K]<=2`. If the index is two, the quadratic conjugation sends `lambda` to `-lambda`, and therefore these have the same `Fp` minimal polynomial. Normalizing leading coefficients gives `g(-t)=(-1)^r g(t)`. Its nonzero constant term forces even `r`, hence an even polynomial.

Conversely an even `g` makes `lambda->-lambda` a well-defined nontrivial automorphism fixing `K`; odd characteristic and `lambda!=0` make it nontrivial. Therefore the index is two. This proof covers all irreducible degrees and uses no distribution of factorization types as the prime varies.

Thus an even irreducible of degree `2s` gives `K` of size `p^s` and `dim_K E=2`. A non-even irreducible gives `K=E`, so the square action is cyclic and irreducible. The phase conclusion matches this same dichotomy: invertibility forces `H_R=lambda H_L` and stability of `H_L` under `K`; only the even case has nontrivial mixed lines.

## 3. Trace reconstruction is valid even when `p` divides the extension degree

The trace proof does not use `Tr(1)!=0`. Its polynomial `z+z^p+...+z^(p^(s-1))` has leading coefficient one and degree below the field size, so it cannot vanish as a function on all of `K`. This makes `(c,z)->Tr(cz)` nondegenerate.

For any balanced alternating `Fp`-form `beta`, the rule

`Tr(c Omega(x,y))=beta(cx,y)` for all `c in K`

defines a unique `Omega(x,y)`. Nondegeneracy proves additivity and `K`-linearity in the first variable; balance transfers scalars to prove it in the second. Skew symmetry follows by testing every trace scalar `c`, and odd characteristic forces its diagonal to vanish. Conversely taking the trace of any alternating `K`-bilinear form recovers precisely such a balanced `Fp`-form.

This is a bijection, not just a trace construction with an unverified kernel: if all traces of `c Omega(x,y)` vanish, then `Omega(x,y)=0`. The `Fp` dimension is therefore `s*n(n-1)/2` for `K`-dimension `n`. In the even case it is `s`; in the non-even case it is zero. Consequently the full-uniform extra dependency dimensions are exactly those claimed.

## 4. Exact finite indices and every lift-size residue

Before compatibility the legal-star sum congruences have the full maximal-lattice index `p^(krq)`. The character proof identifies all periods, using three compensating neighbor slots. Independent within-row label transfers prove the congruence map is onto its stated finite codomain.

After compatibility, the explicit integer parameterization by free zero-total root margins and free edge interior entries reduces onto every compatible `Fp` direction. Thus the classified field dependency dimension computes the exact integer sublattice index; no saturation index is missing.

The all-zero legal star is compatible. Its `N`-multiple belongs to each compatible affine lattice hull, for every `N`, so there is no absent residue class. The uniform mean need not itself be an integer or legal point. Fixed full-rank lattices have bounded covering radius, and after `sqrt(N)` scaling that offset vanishes. The positive weighted Gaussian Riemann sums therefore have the reciprocal-index fraction uniformly in all changing translates, including `p|N`.

Combining that exact fraction with the relative legal/independent local CLT covolume ratio and the exact independent matching normalizer gives the asserted coefficient. The positive compatible weighted precision controls the fixed-neighborhood tail. No polynomial Stirling factor is discarded at a zero exponent.

The auxiliary `(I,C)` calculation also passes: `I` forces the left slope skew, the opposite map forces `CM=MC^T`, and cyclicity of `C` kills it. Its remaining coefficient is the old two-map kernel dimension, by adjoint rank equality.

## 5. One-sided zero phases and the square-matrix condition

For `H_L=Fp,H_R=0`, the only full-lattice congruences are the `m` right-neighbor sums, so the index is `p^m`. Compatible tables are precisely left root margins. Their first moments `w_i=sum_a a n_i(a)` vary freely over `Fp^m`, and the congruence vector is `T^T w`. The compatible rank is therefore `rank T=m-s0`, giving coefficient `p^s0`. The opposite side is its transpose.

Each quotient point map lifts exactly as a fiber-constant original solution, with the other side zero. Translation removes all affine terms for every `N`. Hence the `p^s0` quotient centers times their `p^s0` uniform coefficients give `p^h` for each mixed family. Narrow mixed neighborhoods, including within-support edge uniformity, correctly avoid counting point subphases twice. Sparse leakage is `o(1)` because the smaller two-space moment is already bounded.

The exact four-family sum is consequently `(p+3)p^h+o(1)`.

The step from excess nullity to an increment of two is correct **because `T` and `X` are square**. A `d`-regular bipartite base has equally many vertices on both sides, by counting edges, and its `N`-lift has equal part sizes. For square `X`,

`nullity [[0,X],[X^T,0]]=2 nullity X`.

This statement would fail in the needed form for unequal base part sizes: a rectangular `X` gives deterministic growing nullity from the part imbalance. No such unequal-frame extension is claimed here.

Fiber-constant pullback stays injective even at `p|N`, so the old even baseline is always present. The shifted Markov numerator is `(p+2)p^h+o(1)` and the threshold denominator is `(p^2-1)p^h`, exactly as written.

## 6. Uniform common probability bound

For the non-even nonzero case, the excess bound is `1/(p^r-1)<=1/(p-1)`. In the even case put `Q=p^s>=p`. Then

`(2Q+1)/(Q^2-1) < 2/(Q-1) <=2/(p-1)`.

For zero,

`(p+2)/(p^2-1) <2/(p-1)`.

Thus `2/(p-1)` is a valid common bound over **all** irreducible factors. This is important because the factorization pattern can change with the good prime. For each fixed prime the factor set is finite and independent of lift size; all local limits are taken before the prime grows.

The good-prime transfer uses the nullity of the integer matrix `f(A)` and polynomial CRT, so no semisimplicity of the lifted modular matrix is needed. Good primes make the base semisimple and give the exact old baselines. The aggregate factor count is at most the degree of the fixed squarefree minimal polynomial of the base. Hence the displayed bound `2 deg(m_B)/(p-1)` follows, and tends to zero after the lift-size limsup.

## 7. Independent finite-field execution

I reran both programs in the available JavaScript runtime: all **20** checks passed (eight form-space dimensions, four direct common-alphabet compatible-lattice ranks, and eight two-space ranks).

The tests include the even irreducible degree-four trace prediction, non-even irreducibles, zero/scalar/Jordan controls, singleton-side restrictions, and the Heawood base with an old irrational even factor. In that latter case the full representation has old dimension twelve and one extra form, while its line restriction has old dimension six and no extra form. This directly checks the `h=2h_H` and mixed central dependency calculation in a nontrivial old-spectrum case.

## Conclusion

No gap or obstruction was found in the audited forms, zero-target, lattice or transfer steps. Together with the separately proved mixed-phase count and the non-even two-phase assembly, these give the proposed bipartite companion moments and their fixed-prime old/new exclusion bounds. The scope remains fixed connected simple regular bases of degree at least three; growing parameters, unequal nonregular frames, and degree two are outside this audit.
