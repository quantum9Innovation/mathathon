# Independent reconstruction of the collective self-energy limit

November 15, 2026. Reviewer: root. Target: probability/collective-self-energy-v1.md, SHA256 a3c6b1b42bed9f7f3c7c5d45c1292df5a207951e709e318db24f6f711c9d9d4d.

Verdict: accepted as the stated joint paper limit, conditional on one resonant pair. No unresolved mathematical finding.

Exposure: the reviewer independently derived the same self-energy and bounded-jump kernel before reading the target, using the author's frozen signed-coupling result. The equivalent scalar law and a density strategy were communicated before the target froze. This review reconstructs the cutoff argument and does not claim isolation.

The collective tail-column estimate follows by expanding each row sum squared under exact subset sampling. Equal marked columns contribute p_2 times the Frobenius square, divided by m s squared. Distinct marked columns contribute p_3 times the sum of squared full row sums, with the same denominator. These give 2^(-R), L to the fourth/n and mL squared/n, as displayed. After dividing by s, only the first survives, with coefficient O(2^(-K)). Diagonal, stationary and analytic pencil corrections are negligible in this normalization.

Replacing e by f removes only the two resonant endpoints. The scalar normalization change is O(1/m), and the selected residual columns are o_P(sqrt(s)). Thus the replacement is negligible after division by sqrt(s). This verifies the collective column comparison for the reference actually used in the two-dimensional Schur matrix.

The inverse bound in the cutoff comparison can be chosen independently of K. In the decoupled model, every nonresonant negative lattice level has distance at least kappa/2 from -kappa in the limit. The positive and zero levels are also separated. For each fixed K, restoring its tight finite number of host couplings and changing the reference projection costs o_P(1). A common bound such as 12/kappa therefore works after the limiting gap margin is reduced. This common bound is sufficient for the iterated cutoff argument.

The deterministic resolvent inequality (15) has the correct scale. The actual coupling column divided by sqrt(s) is tight. On its bounded event the column comparison also bounds the model column, so one does not need a K-uniform count bound for the number of short pairs. The global operator comparison controls the inverse difference. This proves the iterated approximation without claiming a growing cutoff.

The finite-arrow coefficient is also correct. If c_0 excludes every short pair, then c_-=c_0-delta sum of the nonresonant symmetric pair vectors+O(delta squared). The change of the complementary projection adds the negative collective energy times that change. At a nonresonant pair of positive weight v_j the resulting coefficient is kappa-(v_j+kappa)=-v_j. At the selected resonant symmetric pair it remains kappa. Their inverse denominators are -kappa-v_j. Thus the leading correction is the negative sum of v_j squared/(kappa+v_j), with the selected term replaced by the same formula because its weight tends to kappa.

Left truncation is controlled by the probability of any stronger pair, not its expectation. Right truncation has summable expected self-energy because its numerator is quadratic in the weak pair weight. Joint convergence uses the same count process as the collective quadratic. It is essential that the two limiting variables are not independent.

Finally, the linear weight and self-energy combine as w-w squared/(kappa+w)=kappa w/(kappa+w). The constant 63/32-kappa squared/3 is 51/32. The resulting bounded jump kernel has finite second moment after compensation, although its two separately written source variables have divergent means. The proof makes this distinction correctly.

The final actual-graph eigenvalue and physical projector theorem still requires the nonlinear-root application and noncoincidence argument. Those are not inferred from this review alone.
