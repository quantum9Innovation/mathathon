# Exact-revision review of the critical lattice spectral law

November 15, 2026. Reviewer: probability owner. Review scope: the synthesis and its use of the frozen probability and effective-operator inputs.

## 1. Frozen inputs and exposure

Reviewed source:

- `root/critical-law-v1.md`, SHA256 `e379a0b55e81925276d2c3046ec1cc4b25c21e028d22fef53516f4b5828e48f3`.

Its mathematical dependencies were read at these exact hashes:

- `root/effective-operator-v1.md`, SHA256 `13b559897d6ed9253a2fc6dd4dede5dd03914c078558d759542afc9c54d28864`.
- `probability/pair-counts-v1.md`, SHA256 `702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29`.

I authored the probability premise and had earlier discussed the general spectral target and constants. This is a separate reconstruction of the synthesis, not an independent review of my own probability proof. I did not read a draft of the synthesis before freezing the probability proof. The probability premise has separate reviewers. I have previously reviewed the deterministic transfer and nonbacktracking estimates used by the effective-operator theorem. This review reads the new effective reduction to check its exact interface, without substituting for its separate full review.

## 2. Decision

Accepted for its stated paper scope, conditional on the named input theorems. No unsupported inference requiring a revision was found in the reviewed synthesis.

The accepted conclusions are the joint fixed-number upper and reflected-lower cluster limits, the signed point-measure limit away from zero, the strict lattice CDF, the circle-phase criterion for existence of a weak top limit, and the lack of such a limit over all admissible sizes. The review does not establish historical priority or end-to-end formal verification.

## 3. Definitions, ordering and constants

The effective source has the actual weighted coupling `sqrt(d-2)AE` and zero added interaction block. Its pair coefficient is

\[
 h=(d-2)d^2g_d(d)/D=d(d-2)^2/(2(d-1)),
\]

and its collective coefficient is

\[
 \kappa=d(d-2)^{3/2}/(\sqrt2(d-1)).
\]

Together with `q=d-1`, these reproduce all constants in the synthesis. The cubic values are `h=3/4` and `kappa=3/sqrt8`.

For each fixed cutoff, the ideal multiset contains two collective values, two signed values per short pair and `m-2p-1` zeros, giving exactly `m+1` entries. Its pair count is tight while `m` tends to infinity. Consequently any fixed number of upper and lower coordinates can be compared with positive and reflected-negative zero-padded lists. The index `m+2-j` selects the j-th eigenvalue counted upward from the bottom of this cluster. It is not an index into the bottom of the full augmented spectrum.

The limit has finitely many atoms above every positive absolute-value threshold. It has infinitely many positive pair atoms approaching zero, as follows from the summability of `exp(-lambda_k)` for increasing k. The positive atoms therefore admit the stated decreasing ordering, with all fixed coordinates positive and with coordinates tending to zero. Each geometric pair contributes both signs with the same multiplicity. The full signed measure is correctly not asserted to be Poisson.

## 4. Two-sided cutoff removal

The left cutoff excludes the rare stronger pairs. The event of a pair at distance less than `r_n-J` has probability at most a constant times `q^(-J)`, uniformly in n. The limiting family has the same bound by its summed Poisson intensity. This controls all discarded large amplitudes without requiring bounded moments of their sizes.

The right cutoff controls small amplitudes in the limit. Every omitted pair has amplitude at most `h q^(-K)`, uniformly in the phase. Deleting those atoms changes each zero-padded ordered coordinate by at most that number.

The corresponding prelimit error is supplied by the effective theorem for the whole ordered cluster. It has limiting upper probability at most `C eta^(-2) q^(-K)` for an error exceeding eta. Thus n tends to infinity with both cutoffs fixed, the cutoffs then tend outward with eta fixed, and eta tends to zero last. This order never substitutes a growing cutoff into an estimate proved only for fixed cutoffs.

At a fixed window, the count vector is integer valued with its discrete topology. Conditional on each count vector, sorting the finite list is continuous in the amplitudes, including collisions with kappa and repeated amplitudes. No simple-eigenvalue assumption is needed. Tight counts also ensure enough zero entries for every fixed coordinate comparison. These facts justify the finite-window continuous mapping step and the bounded Lipschitz truncation argument.

## 5. Vague convergence and uniform local counts

The source uses compactly supported continuous functions on the punctured real line, so their supports lie a positive distance a from zero. On an ordered-operator comparison event with error below `a/4`, only ideal values with absolute value at least `a/2` can contribute. An explicit uniform version of the stated count-tightness argument is as follows.

Every ideal pair value of magnitude at least `a/2` comes from distance

\[
 \ell\le \log_q(2h/(as)).
\]

The deterministic degree bound and label symmetry give

\[
 \mathbb E\#\{\text{such marked pairs}\}
 \le C_d\frac{m^2}{n}\frac{2h}{as}
 \le C_{d,c}/a
\]

for all sufficiently large n. This bound is uniform in the retained upper cutoff K. Including both signs and the two collective values preserves uniform tightness. It remains valid if a given cutoff retains fewer pairs.

For any fixed finite collection of test functions, extend them by zero through a neighborhood of the origin. Uniform continuity then bounds their integral changes by the number of relevant ideal atoms times a modulus of continuity at the ordered error. First restrict to a uniformly bounded count, then send that error to zero. The same count bound gives local tightness of the random measures. Combined with the finite-window joint convergence, this proves convergence in distribution in the vague topology on this locally compact space.

This also checks that small operator errors cannot introduce an uncontrolled number of new atoms into a compact region away from zero. A finite-dimensional coordinate limit alone would not have supplied that fact.

## 6. CDF, atoms and tail

For `x>=kappa`, the event `X_phi<=x` forbids exactly the pair levels satisfying `w_k>x`. If

\[
 t=\phi+\log_q(h/x),
\]

the largest forbidden integer is `ceil(t)-1`, including when t itself is an integer. Summing the geometric means gives exactly

\[
 \exp\left[-\frac{d c^{3/2}}{2(q-1)}
 q^{\lceil\phi+\log_q(h/x)\rceil-1-\phi}\right].
\]

At `x=w_k>kappa`, the jump mass is

\[
 \exp\left[-\sum_{j<k}\lambda_j\right]
 (1-\exp(-\lambda_k)).
\]

If a pair level coincides with kappa, the same strict comparison correctly includes it in the collective-floor atom. Thus the displayed CDF is right continuous at every point and has the correct convention at its atoms.

The exponent lies between `d h c^(3/2)/(2q(q-1)x)` and `d h c^(3/2)/(2(q-1)x)`. This proves reciprocal-order upper tails and an infinite first moment. Replacing x by qx decreases the ceiling exponent by one, proving the stated scaling identity. No convergence of finite-n moments is asserted from weak convergence.

## 7. Phase classification and full-sequence obstruction

The endpoint phases zero and one are identified by replacing k by `k-1` in both the amplitudes and intensities. Two distinct phases in `[0,1)` have disjoint pair lattices. Each lattice has levels strictly above kappa, with the positive atom mass computed above. At one such level the other phase has no atom. The top laws are therefore distinct, despite the common collective floor.

Finite-window Poisson means and amplitudes depend continuously on the phase. The uniform left-tail and weak-amplitude bounds extend that continuity to the top law, including the identified endpoints. This gives a continuous and injective family on the phase circle.

For an arbitrary admissible size sequence, a convergent circle phase gives a weak top limit by the subsequence theorem and compactness. Conversely, a nonconvergent circle phase has two distinct circle limit points. The corresponding subsequences have distinct weak top limits. Thus weak convergence of the top law is equivalent to convergence of its circle phase. An ordinary fractional-part sequence may alternate between limits zero and one without violating this criterion.

For the full sequence of admissible n, the nearest admissible integer to `c^(3/2) q^(3(j+phi))` differs by a bounded amount. Substitution into `log_q(1/s)=(log_q n)/3-(log_q c)/2+o(1)` yields the desired interior phase phi. This remains valid for every deterministic rounding choice `m(n)/n^(1/3)->c`. Choosing two distinct interior phases therefore proves the asserted failure of a full-sequence weak top limit.

## 8. Scope and remaining boundaries

The synthesis covers predetermined labels in the fixed-degree, critically weighted, zero-interaction attachment model. The unweighted cubic case is included exactly. It does not quantify simultaneously over all marked sets and does not cover arbitrary nonzero H. It proves adjacency spectral laws, not normalized-Laplacian or mixing laws, spatial localization or rare occurrence probabilities for independently sampled attachment motifs.

The paper proof uses the separately reviewed graph probability, projected-resolvent approximation and deterministic transfer. The current finite formal packet is not used as a certificate of the infinite point process or the weak convergence argument. No source or prior frozen file was changed during this review.
