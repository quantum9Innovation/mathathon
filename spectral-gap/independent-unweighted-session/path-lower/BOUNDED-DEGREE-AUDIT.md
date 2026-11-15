# Independent audit of the degree-three obstruction

Audit date: 15 November 2026. Reviewed
`../bounded-degree/theorem-and-proof.md` and the supporting algebraic
proof `../path-upper/bounded-degree-independent.tex`.

**Verdict: mathematical PASS.** The construction proves a
`Theta_alpha(1/epsilon)` worst-case strict count for simple, connected,
unit-conductance host graphs of maximum degree three, with exactly one
existing bridge doubled. No use of Schur complementation as an exact
fractional functional calculus is needed. The required low-frequency
limit is valid, including its relative inverse-power factors.

The proof remains an existence argument with potentially enormous
graphs. It does not prove the full determinant-admissible closure at
fixed maximum degree and correctly avoids that stronger claim.

## 1. Primary source: Bordenave supplies every sufficiently large even size

Inspected the actual primary PDF of Charles Bordenave, *A new proof of
Friedman's second eigenvalue Theorem and its extension to random lifts*,
arXiv:1502.04482v4, pp. 1--2, particularly Theorem 1:

<https://arxiv.org/pdf/1502.04482>.

The setup immediately preceding Theorem 1 defines `G_d(n)` as the set
of **simple** `d`-regular graphs on `n` labeled vertices. Theorem 1
states that, for any fixed `eta>0`,

\[
 \mathbb P\{\mu_2(G)\vee|\mu_n(G)|
     \ge2\sqrt{d-1}+\eta\}\longrightarrow0,
\]

and explicitly specifies that the limit is along any sequence tending
to infinity with `nd` even. Therefore take

\[
 d=3,\qquad \eta=(3-2\sqrt2)/2,\qquad
 \gamma_0=(3-2\sqrt2)/2>0.
\]

For **every sufficiently large even integer** `n`, there exists a simple
cubic graph with `mu_2<3-gamma_0`; hence its combinatorial Laplacian gap
is at least `gamma_0`. The bound `mu_2<3` also proves connectivity. A
contrary infinite sequence of bad even sizes would contradict the
stated limit, so the source supplies all sufficiently large admissible
sizes, not merely a subsequence.

This is exactly the reservoir input required. The construction may
cite Bordenave's proof of Friedman's theorem and omit the Alon source.
Subdividing one edge produces an odd reservoir size. Nearest admissible
odd sizes approximate any prescribed positive mass ratio with `O(1)`
rounding error as the common size scale tends to infinity.

The elementary subdivision estimate in the draft is correct. In the
new graph energy `Q`, the old graph energy is at most `2Q`. Old-vertex
variance about the old mean is at most `2Q/gamma_0`, and the new port's
squared deviation from that mean is at most `2Q+4Q/gamma_0`. Thus the
new gap is at least `1/(2+6/gamma_0)`. Consequently
`r(H,p)=e_p^* L_H^dagger e_p<=1/gamma` uniformly.

## 2. Port reduction is exact at zero frequency

Write a reservoir potential as `a 1+h`, with `1^*h=0`. If its port
is connected to a prescribed core potential `x` by a neck of resistance
`ell`, elimination of the neck gives the energy

\[
 h^*L_Hh+(x-a-h_p)^2/\ell.
\]

For fixed `h_p=y`, the minimum first term is `y^2/r`, where
`r=e_p^*L_H^dagger e_p` (with the evident limiting interpretation
when `r=0`). Eliminating `y` leaves

\[
 (x-a)^2/(\ell+r).
\]

Thus the resistance `ell+r` is correct for **fixed reservoir means**.
This accounts for the distributed compensating current implicit in
the mean-zero constraint. It is not the resistance to a pinned
individual vertex. For the anchor, replacing the edited edge's
resistance 1 by `1/2` gives exactly `1+r_0` and `1/2+r_0`.

## 3. Core and determinant/pivot calculation

The graph is simple and has maximum degree three, including the root,
all tree vertices, neck endpoints, and subdivided reservoir ports.
The root-anchor edge is a bridge and therefore has leverage exactly
one before doubling.

The tree-admittance increment calculation is correct:

* A terminal draws current at most `1/ell` under root potential one.
* The root-to-new-leaf voltage drop is less than `1/K`, by summing the
  subtree current bounds over tree depths.
* The new leaf's open-circuit voltage is at least `3/4`.
* Its resistance to ground with the root pinned is at most `k`.
* Adding its shunt changes root admittance by exactly
  `v_j^2/(ell+r_j+rho_j)`, which is at least `1/(4Km)` under the chosen
  constants.

For `S_i={i,...,m}`, the terminal principal determinant retains the
earlier terminals fixed at zero. In the inverse used by the root
determinant lemma, the retained terminals are free and therefore open.
Hence the relevant admittance is indeed `g_(i-1)`. Dividing the joint
core-plus-terminal determinant ratio by the core-only ratio `f(g_m)`
gives exactly

\[
 \frac{\det K'[S_i]}{\det K[S_i]}
 =\frac{f(g_{i-1})}{f(g_m)},\qquad
 \rho_i=\frac{f(g_{i-1})}{f(g_i)}.
\]

The derivative lower bound for `-log f` is uniform in the entire
port-resistance cube, and yields `log rho_i>=h/m`. No factor or
indexing error was found.

## 4. Separated-mass lemma

The supporting `.tex` proof is valid. Its elementary-symmetric-polynomial
argument identifies the unique leading trailing principal minors and
separates adjacent eigenvalue scales. The scalar resolvent identity
then gives the leverage limits `z_i -> tau_i-tau_(i+1)`. The diagonal
fractional-resolvent integral is dominated by an integrable scalar
function, while off-diagonal entries vanish with the positive exponent
`(1-alpha)/2`. The pivot ratios follow from the determinant lemma.

The extension to convergent families is also valid. For fixed `m`,
the port parameter cube is compact, all its terminal stiffness matrices
remain SPD, and the construction varies continuously. The convergent-
family lemma implies uniform convergence by the usual contrary-sequence
and convergent-subsequence argument. Thus choosing the mass separation
before knowing the actual port resistances is justified.

## 5. Slow reservoirs: the relative fractional limit is valid

Here is a more explicit argument for the limiting step in the draft.
Keep the core, `m`, and all positive target masses fixed. Let `P_s` be
the isometry whose columns are normalized reservoir indicators; its
orthogonal complement consists of all core coordinates and the
mean-zero reservoir fluctuations. In this decomposition write

\[
 L_s=\begin{pmatrix}a_s&b_s\\b_s^*&D_s\end{pmatrix}.
\]

The bounds are uniform over all chosen reservoirs with the specified
gap:

\[
 \|a_s\|=O(s^{-1}),\qquad
 \|b_s\|=O(s^{-1/2}),\qquad D_s\succeq cI,
 \qquad \|L_s\|\le6.
 \tag{A}
\]

For the updated pair the same estimates hold, with norm bound 8.
To justify the complementary coercivity in (A), the reservoir gaps
bound the squared norms of every mean-zero fluctuation by its internal
energy. For any core vertex, choose one fixed core path to a reservoir
port. Its squared potential is bounded by the path energy plus the
squared reservoir port fluctuation. Summing over the finite core
controls its full norm by the total energy. Constants can depend on
the fixed core and the common reservoir gap, but not on reservoir size.

The zero-frequency Schur complement is

\[
 a_s-b_sD_s^{-1}b_s^*.
\]

By the exact constrained port calculation above, multiplication by `s`
converges, along any sequence of convergent port resistances, to the
mass-normalized terminal Schur matrix `A`. The corresponding updated
matrix converges to `B`. Replacing `D_s^{-1}` by
`(D_s-lambda)^{-1}` changes this complement by `O(lambda/s)`, uniformly
for small `lambda`. Standard finite-block elimination then proves:

* There are precisely `m+1` low eigenvalues, one of them zero; their
  positive members are of order `s^-1`.
* All other eigenvalues are bounded below by a positive constant.
* The low spectral isometries `U_s` and `U'_s` can be chosen within
  `O(s^-1/2)` of `P_s`.
* `s U_s^*L_sU_s -> A` and `s (U'_s)^*L'_sU'_s -> B`.

Let `Q'_s` project onto the updated high subspace. Since
`||Q'_s U_s||=O(s^-1/2)`, its contribution satisfies

\[
 \|U_s^*Q'_s(L'_s)^\alpha Q'_sU_s\|=O(s^{-1}).
\]

After multiplying by `s^alpha` this tends to zero because `alpha<1`.
The updated low part converges to `B^alpha`; the baseline low part
converges to `A^alpha`. The scaled baseline low matrices have a single
kernel and all other eigenvalues bounded away from zero, so their
Moore--Penrose negative powers converge in norm. It follows that

\[
 U_s^* C_\alpha(L_s,L'_s)U_s
 \longrightarrow
 (A^\dagger)^{\alpha/2}(B^\alpha-A^\alpha)
 (A^\dagger)^{\alpha/2}.
 \tag{B}
\]

The common global constant vector belongs to both low subspaces.
Therefore the shared kernel is handled correctly in (B). This proof
uses the full fractional calculus before compression; it does not
replace it by the power of a Schur complement without a limit.

The estimates in (A) are uniform for fixed target masses and fixed
core. Even if the port resistances do not converge for the chosen
reservoir sequence, compactness of their bounded cube lets one pass
to a convergent subsequence. All possible limiting terminal corrections
obey the same eigenvalue lower bound by the uniform earlier choices.
A contrary sequence of failed finite approximations would yield a
contradictory convergent subsequence. Thus the construction needs no
prescription of port resistances and no assumption that a particular
expander family has convergent port resistance.

## 6. Grounding the anchor and final count

After terminal masses have been chosen, let the anchor mass tend to
infinity. The full mass-normalized terminal pair converges in fixed
dimension to `0 direct-sum A_ground` and
`0 direct-sum B_ground`. Its rank is constantly `m`, and all positive
eigenvalues converge to positive eigenvalues of the grounded SPD
matrix. Both fractional powers and Moore--Penrose inverse powers
therefore converge. The relative correction tends to one extra zero
plus the grounded relative correction. Compactness again makes this
uniform over port parameters.

Choosing terminal separation first, a finite anchor mass second, and
the common reservoir scale last is therefore logically sound. Min--max
transfers the `m` positive eigenvalues of the low compression to the
full relative correction. The final power-of-two choice of `m` gives
the claimed strict count, with slack. The determinant upper bound at
leverage at most one gives the matching order for every graph in the
class.

## Editorial fixes before integration

The draft's first paragraph and Section 4 refer to a pending `.md`
algebraic proof. The completed source is
`../path-upper/bounded-degree-independent.tex`; those references and
the pending-proof wording should be updated. Replace the Alon
reservoir paragraph by the verified Bordenave/Friedman consequence
above. These are presentation fixes, not mathematical gaps.
