# Rational-to-modular transfer of an old/new spectral collision

Prepared 2026-11-15. This note proves the deterministic and probabilistic transfer requested in `regular-lift-old-new-disjointness-root.txt`. It uses the exact irreducible-companion moment as a separate input, now proved in `irreducible-moment-assembly.md` using `cyclic-lattice.md`; it does not reprove that moment here.

**Verdict:** the transfer is valid for every lift size, including `p|N`. Semisimplicity is needed for the fixed base at a good prime, and for the characteristic-zero symmetric matrices. It is **not** needed for the lifted matrix modulo `p`. One must transfer the dimension of `ker f(A)`, not only characteristic-polynomial multiplicities.

## 1. Old and new spaces in characteristic zero

Let `B` be the fixed `k`-by-`k` integer adjacency matrix of a simple undirected base, and let `A=A_N` be an adjacency matrix of one of its `N`-lifts. Let

`J:Q^k -> Q^(kN)` be the fiber-constant embedding,

`S:Q^(kN) -> Q^k` be the fiber-sum map.

The exact integer identities are

`AJ=JB`, `SA=BS`, `SJ=N I_k`.

Thus over `Q` there is an invariant direct sum

`Q^(kN)=im(J) direct-sum ker(S)`.

The first summand is the old representation. The second is its orthogonal complement and is the usual new representation. The characteristic polynomial of the new restriction is rational, and

`charpoly(A)=charpoly(B) charpoly(A|ker(S))`.

All matrices involved in the rank argument below are integer matrices; the rational splitting is used only to interpret a real old/new collision.

Let `f in Z[T]` be a monic irreducible factor of `charpoly(B)`, of degree `ell`, with exponent `t`. Since `B` is real symmetric, it is semisimple in characteristic zero, so every root of `f` has old multiplicity exactly `t`.

If the new real spectrum contains any root of `f`, irreducibility over `Q` forces the new rational characteristic polynomial to be divisible by `f`. Symmetry of `A` then gives

`dim_Q ker f(A) >= ell(t+1)`.                              (1)

More precisely, if `f` has total exponent `t+u` in `charpoly(A)`, then `A`'s real diagonalizability gives `dim_Q ker f(A)=ell(t+u)`. Rational and real ranks of the integer matrix `f(A)` agree.

## 2. One finite set of bad primes suffices

Factor the fixed integer characteristic polynomial as

`charpoly(B)=product_alpha f_alpha^t_alpha`,

where the `f_alpha` are distinct monic irreducible integer polynomials. Put

`F=product_alpha f_alpha`.

The integer matrix identity `F(B)=0` holds, because `B` is real symmetric and `F` vanishes at every one of its eigenvalues. The polynomial `F` is squarefree over `Q`, so its integer discriminant is nonzero.

Call a prime good if

`p` is odd and `p` does not divide `disc(F)`.                  (2)

There are arbitrarily large such primes. For every good prime, the reduction `Fbar` is squarefree. Consequently:

* each `f_alpha mod p` is squarefree;
* reductions of different `f_alpha` are coprime;
* `B mod p` is annihilated by the squarefree polynomial `Fbar` and is therefore a semisimple `Fp[T]`-module.

For the particular factor `f`, write

`fbar=product_(j=1)^s g_j`, `r_j=deg(g_j)`,

with distinct monic irreducible `g_j`. The sum of their degrees is `ell`. The characteristic polynomial of `B mod p` contains every `g_j` with exponent exactly `t`, and its semisimplicity gives

`dim_Fp ker g_j(B mod p)=r_j t`.                           (3)

Thus no additional `N`-dependent bad primes or rank-minor exceptions are needed for the base. Using the discriminant of `F` simply avoids all fixed-base exceptions at once. One could instead use the discriminant of `f` and its resultants with the other factors.

No prime is required to leave `f mod p` irreducible. Its arbitrary squarefree factorization is enough; no distribution-of-splitting-primes input is used.

## 3. Companion intertwiners equal simple-module eigenspaces

Let `g` be any monic irreducible polynomial over `Fp`, of degree `r`, and let `R_g` be a companion matrix. For any matrix `M` over `Fp`, define

`H_g(M)={Y: M Y=Y R_g}`.

There is an `Fp`-linear isomorphism

`H_g(M) ~= ker g(M)`.                                     (4)

To prove it, choose a cyclic vector `v` for `R_g`. An intertwiner is determined by `w=Yv`, and `g(M)w=Yg(R_g)v=0`. Conversely, given `w in ker g(M)`, define

`Y(R_g^a v)=M^a w`, `a=0,...,r-1`.

These vectors form a basis of the domain, and the polynomial relation `g` makes the resulting map intertwine also at the highest power. This proves (4), without any semisimplicity assumption on `M`.

The space `ker g(M)` is a vector space over the field `Fp[T]/(g)`, with `T` acting as `M`. Hence

`dim_Fp H_g(M)` is a multiple of `r`.                       (5)

It counts the geometric/simple-module multiplicity of `g`. It need not equal `r` times the characteristic-polynomial exponent when `M` is not semisimple.

By (3)--(4), the old companion-intertwiner dimension at `g_j` is exactly `r_j t`.

## 4. Modular rank transfer uses `f(A)`, not `charpoly(A)`

For an integer matrix, reduction modulo a prime cannot increase rank: every minor vanishing over `Q` is the zero integer and remains zero modulo `p`. Therefore (1) gives

`dim_Fp ker fbar(A mod p) >= ell(t+1)`                     (6)

for every prime, in particular every good prime.

Because the `g_j` are pairwise coprime, the polynomial Chinese remainder identity gives

`ker fbar(M)=direct-sum_j ker g_j(M)`                       (7)

for **every** matrix `M` over `Fp`. For completeness, choose polynomial projectors `e_j` with `e_j=1 mod g_j`, `e_j=0 mod g_l` for `l!=j`, and `sum_j e_j=1 mod fbar`. If `fbar(M)w=0`, then `w=sum_j e_j(M)w`, and each summand belongs to `ker g_j(M)`; the same coprime identities show the sum is direct. This proof permits arbitrary higher Jordan blocks in the ambient operator.

Combining (6)--(7), some index `j` must satisfy

`dim_Fp ker g_j(A mod p)>r_j t`.

By (5), this is equivalent to

`dim_Fp H_(g_j)(A mod p)>=r_j(t+1)`.                       (8)

Indeed if all dimensions were at most their old values `r_j t`, their sum would be at most `ell t`, contradicting (6).

This proves the deterministic event implication

`{new real spectrum meets roots(f)}`

` subseteq union_j {dim H_(g_j)(A mod p)>=r_j(t+1)}`         (9)

for every lift size and every good prime.

The use of nullity in (6) is essential. Characteristic-polynomial divisibility alone would not prove (8): a size-two Jordan block for `g=T` has characteristic polynomial `T^2` but only a one-dimensional `ker M`. The rank transfer prevents precisely this loss of geometric multiplicity.

## 5. Why `p|N` does not cause a problem

Reduce the fiber-constant map `J` modulo any prime. It remains injective: a vector's coordinates are merely repeated on its fibers. Also `AJ=JB` remains exact. Thus

`X -> JX`

injects every old intertwiner space into the lifted intertwiner space. In particular

`dim H_(g_j)(A mod p)>=r_j t`                              (10)

for every lift and every good prime, regardless of `N`.

When `p|N`, the relation `SJ=N I` prevents the fiber-sum averaging projection from splitting old and new spaces modulo `p`. The old submodule may even lie inside a larger nonsplit primary block. None of the proof uses a modular old/new direct sum, a modular orthogonal complement, or division by `N`.

The right side of (9) means **excess total modular companion-intertwiner dimension above the injected old baseline**. Calling it a canonical modular “new summand” would be stronger and unnecessary.

## 6. Probability consequence of the exact moment

Use the separately proved irreducible-companion moment: for every fixed good `p` and every `g_j`,

`E |H_(g_j)(A_N mod p)|=2 p^(r_j t)+o_(B,p,g_j)(1)`.         (11)

Let `b_j=p^(r_j t)` and `q_j=p^(r_j)`. The deterministic old embedding gives `|H_(g_j)|>=b_j`. On the event in (8), the field-vector-space divisibility gives `|H_(g_j)|>=b_j q_j`. Shifted Markov therefore yields

`P(dim H_(g_j)>=r_j(t+1))`

` <= [E |H_(g_j)|-b_j]/[b_j(q_j-1)]`.

First take the lift-size limit, keeping `p,g_j` fixed. By (11),

`limsup_N P(dim H_(g_j)>=r_j(t+1)) <=1/(p^(r_j)-1)`.         (12)

There are at most `ell` factors. Equations (9),(12) give

`limsup_N P(new real spectrum meets roots(f))`

` <=sum_j 1/(p^(r_j)-1) <=ell/(p-1)`.                     (13)

Let arbitrarily large fixed good primes tend to infinity only **after** the lift-size limsup. This proves that the collision probability tends to zero.

The same prime can be good for every old factor, by (2). Summing (13) over the finitely many `f_alpha` gives

`limsup_N P(any old/new real spectral collision)`

` <=deg(F)/(p-1)`.

Thus the exact moments (11), if established for all irreducible companion targets over each fixed odd field, imply complete old/new spectral disjointness with high probability for every fixed base to which those moments apply. In the proposed moment packet that scope is connected nonbipartite regular bases of degree at least three. All old algebraic eigenvalues retain their old real multiplicities, including irrational ones.

## Audit conclusion

The semisimplicity, good-prime, modular rank and `p|N` issues introduce no counterexample to the transfer. The separate proof input is exactly the irreducible-companion asymptotic (11), including its uniform-phase coefficient and point-phase contribution; that input is established in `irreducible-moment-assembly.md` and `cyclic-lattice.md`. A merely bounded moment, or an algebraic characteristic-polynomial multiplicity statement modulo `p`, would not suffice for this conclusion.
