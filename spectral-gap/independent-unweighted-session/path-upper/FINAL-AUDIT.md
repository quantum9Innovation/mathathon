# Independent final audit: degree two versus degree three

Audit date: 2026-11-15. Reviewed `../bounded-degree/theorem-and-proof.md`,
the reservoir proof in `../bounded-degree/degree-three-lower-bound.tex`,
and `bounded-degree-independent.tex` (the separated-mass pivot lemma).

**Verdict: PASS for the mathematical construction and transfer.** The
unit-weight degree-three lower bound is a finite graph existence proof,
and the relative fractional limit is justified rather than being
identified directly with a Schur complement. The cycle calculation
below completes the uniform degree-two upper bound. The optimal
degree-two lower bound is supplied by the path-lower investigation and
is outside the proof rechecked in this audit.

## Reservoir coercivity and exact static reduction

Let the finite core and positive target masses be fixed. Constants in
the reservoir limit may depend on these choices, including the number
of terminals and the long neck lengths, but are independent of the
reservoir scaling parameter `s`. This is exactly the uniformity needed
for the sequential existence proof.

For a reservoir vector `x` of mean zero, its gap gives
`||x||^2 <= gamma^(-1) E_res(x)`. For any vector in the complement of
the normalized reservoir indicators, all reservoir restrictions have
mean zero. If `y` is the vector on the finite core and `x_port` is the
finite vector of port values, connectedness to the reservoir pins gives

`||y||^2 <= C_core (E_external(x,y) + sum_i |x_port,i|^2)`.

Since each port value is bounded by its reservoir norm, the reservoir
gap controls the second term. Thus the entire complementary block has
a smallest eigenvalue at least a fixed `eta>0`, uniformly in reservoir
sizes. Doubling the edited edge only increases its quadratic form.

The static contact resistance formula is exact. For a reservoir of
mean zero supplied with current `I` at its port and balanced by a
uniform extraction, its equation is

`L_H x = I(e_p - 1/n 1)`.

Consequently its port-to-mean voltage is
`x_p = I e_p^T L_H^dagger e_p = I r_i` and its minimum energy is
`I^2 r_i`. Eliminating this fluctuation therefore adds `r_i` in series
with the incident edge or neck. Different reservoirs have disjoint
fluctuation spaces, so there are no additional cross contacts.

The stated subdivision estimate also checks: old energy is at most
twice the new energy; old variance is at most `2E/gamma_0`; and the new
port's squared deviation from the old mean is at most
`2E+4E/gamma_0`. Hence the claimed new gap
`1/(2+6/gamma_0)` is valid. A port has internal degree two and external
degree one, so the maximum graph degree is three.

The sole external graph-existence input is standard expander
existence with arbitrary sufficiently large admissible sizes. Alon's
primary abstract was independently opened in this audit:
[Explicit expanders of every degree and size](https://arxiv.org/abs/2003.11673).
For cubic degree, choose a fixed adjacency bound strictly below three.
The parity restriction to admissible even sizes causes only `O(1)`
rounding error after subdivision and does not affect mass ratios.

## The low relative fractional limit

Use the orthogonal decomposition into reservoir indicators and their
complement, and write the graph Laplacian as

`L_s = [ A_s  E_s ; E_s^T  H_s ]`.

The bounds are `A_s=O(s^-1)`, `E_s=O(s^-1/2)`, and `H_s>=eta I`.
Its static Schur complement is

`S_s = A_s-E_s H_s^-1 E_s^T`

and `s S_s` converges, along a contact-resistance subsequence, to the
mass-normalized terminal Laplacian `A`. The updated pair has the same
properties and limit `B`. At spectral parameter `lambda=O(s^-1)`,

`E_s[(H_s-lambda I)^-1-H_s^-1]E_s^T = O(lambda/s) = O(s^-2)`.

Thus precisely `m+1` eigenvalues lie at the low scale, including the
shared zero. The remaining eigenvalues are bounded below, and both
the baseline and updated low spectral subspaces differ from the
indicator space in operator angle by `O(s^-1/2)`.

Choose isometries `U_s,U'_s` of these low spaces using their polar
alignment with the same indicator coordinates. Then, in fixed
`(m+1)`-dimensional coordinates,

`s U_s^T L_s U_s -> A`,

`s (U'_s)^T L'_s U'_s -> B`,

`U_s^T U'_s -> I`.

The high part of `(L'_s)^alpha` has bounded norm (the full graph norm
is at most eight), and its compression to the baseline low space has
norm `O(s^-1)`, since the mutual subspace angle is `O(s^-1/2)`.
Therefore

`s^alpha U_s^T (L'_s)^alpha U_s -> B^alpha`,

because `s^(alpha-1)->0`. The baseline version is immediate because
`U_s` is its own low spectral isometry. On the fixed positive support,

`s^(-alpha/2) [(U_s^T L_s U_s)^dagger]^(alpha/2)
    -> (A^dagger)^(alpha/2)`.

The exact common constant kernel converges in these coordinates, and
all limiting positive low eigenvalues stay bounded away from zero
once the masses are fixed. Hence the stated pseudoinverse convergence
is valid. Multiplying these three convergences proves

`U_s^T C_alpha(L_s,L'_s) U_s
    -> (A^dagger)^(alpha/2) (B^alpha-A^alpha)
       (A^dagger)^(alpha/2)`.

This verifies the reservoir lemma in the precise baseline relative
metric. No claim about convergence of the full high-dimensional
relative response is needed; compression and min-max supply the graph
lower bound.

## Pivot lemma and fanout constants

The independently proved separated-mass lemma checks in all three
parts:

1. Principal-minor elementary symmetric polynomials imply
   `lambda_i ~ kappa_i delta^(d-i)`, with `kappa_i` the reverse Schur
   pivots. The comparison of these polynomials to products of largest
   eigenvalues proves scale separation before leading constants are
   extracted, avoiding circularity.
2. Resolvent responses at each scale identify the leverage weights as
   `z_i -> tau_i-tau_(i+1)`.
3. Dominated convergence in the exact fractional resolvent gives the
   diagonal factors `[(1+tau_i)/(1+tau_(i+1))]^alpha-1`; the off-diagonal
   divided-difference estimate vanishes as a positive power of the
   scale ratio.

The stated convergent-family extension implies uniform convergence on
a compact parameter set by the subsequence criterion. Thus one choice
of terminal mass separation works for every allowable contact vector.
The subsequent anchor grounding is also uniform: in mass coordinates
its anchor row/column tend to zero and the remaining SPD block stays
uniformly positive for fixed terminal masses.

The fanout increment identity and constants pass. At each newly
grounded leaf the open voltage is at least `3/4`; the Thevenin
resistance is at most `k`; and
`ell+r_i+rho_i <= 2Km`. Thus each admittance increment is at least
`9/(32Km)`, which implies the displayed `1/(4Km)` bound. The
root-ground derivative lower bound `beta` is valid uniformly over the
contact cube. The principal determinant ratio is
`f(g_(i-1))/f(g_m)`; dividing adjacent ratios gives the claimed pivot
factor `f(g_(i-1))/f(g_i)` and its lower logarithmic bound `h/m`.

The inequality `rho_i^alpha-1 >= alpha log rho_i` is valid because
`exp(x)-1>=x`. Choosing a power of two
`alpha h/(8 eps) <= m < alpha h/(4 eps)` gives graph eigenvalues at
least `alpha h/(2m)>2 eps`, leaving ample room for strict thresholds.

One editorial point: the draft's sentence about a compulsory local
outlier preventing full determinant-admissible closure is not proved
inside the reviewed degree-three construction. It can be supported by
the following short separate lemma, or omitted as unnecessary for the
degree-two/degree-three rank dichotomy.

For any unit-weight graph of maximum degree at most `Delta`, put
`R=2Delta`, `c_alpha=sin(pi alpha)/pi`, and take the Rayleigh vector
`x=L^(alpha/2)b` on the support. Then

`x^T C_alpha x / ||x||^2
 = b^T[(L+bb^T)^alpha-L^alpha]b / (b^T L^alpha b)`.

For `R<=t<=2R`, one has
`b^T(L+tI)^-1b >= 2/(3R)` and the Sherman--Morrison denominator is
at most two, because the leverage of an included unit edge is at most
one. Restricting the positive fractional integral to this interval
gives numerator at least `(2c_alpha/9)R^(alpha-1)`, while the denominator
is at most `2R^alpha`. Therefore

`lambda_max(C_alpha) >= sin(pi alpha)/(18 pi Delta) > 0`.

This explicit, nonsharp bound proves the required compulsory outlier
uniformly at fixed degree. In particular determinant-admissible lists
whose every correction eigenvalue is below this constant cannot be
limits within a fixed-degree unit-weight class.

## Rigorous cycle calculation and the degree-two class

Let `L` be the unit-weight simple cycle Laplacian on `n>=3` vertices,
and double any edge `b=e_p-e_(p+1)` (indices modulo `n`). The complex
Fourier eigenbasis gives, for `1<=k<n`,

`lambda_k = 4 sin^2(pi k/n)`,

`|<b,phi_k>|^2 = lambda_k/n`,

`z_k=|<b,phi_k>|^2/lambda_k = 1/n`.

All relevant traces and eigenvalues are unchanged by using this
complex unitary eigenbasis instead of a real one. Put
`j=min(k,n-k)`. Concavity of sine on `[0,pi/2]` gives

`lambda_k >= 16 j^2/n^2`.

For `0<delta<4`, there are at most `n sqrt(delta)/2` such positive
eigenvalues, counting both sides of the Fourier spectrum. Therefore

`nu([0,delta]) <= sqrt(delta)/2`.

For `delta>=4`, the same inequality follows from
`nu(total)=(n-1)/n<=1<=sqrt(delta)/2`. Thus the bound holds for every
`delta>0`, uniformly in cycle length and edge location.

The path upper proof applies unchanged: the relative low-block trace
is at most `alpha nu([0,delta])`, PSD pinching removes this block at
`delta` proportional to `eps^2`, and absolute rational compression on
the remaining block yields `O_alpha(log^2(1/eps))` rank. Host and
updated endpoint norms are again at most four and six, respectively.

A finite connected simple graph of maximum degree at most two is a
path, a cycle, or a singleton. The singleton has no edge to double.
Thus the path and cycle estimates give a uniform logarithmic-squared
upper on the entire connected degree-two class. The matching path
lower bound makes its worst-case order `Theta_alpha(log^2(1/eps))`.
