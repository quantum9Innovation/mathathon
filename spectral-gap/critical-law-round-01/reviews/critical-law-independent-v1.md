# Review of the critical lattice spectral law

Date: November 15, 2026, America/Los_Angeles.

Decision: accepted as a complete paper proof at the frozen revision. No mathematical finding remains open in the stated limit theorem. The proof remains distinct from historical priority and from a machine formalization of the random graph limit.

## Exact revision and prior exposure

The entire synthesis `root/critical-law-v1.md` was read at SHA256

`e379a0b55e81925276d2c3046ec1cc4b25c21e028d22fef53516f4b5828e48f3`.

Its two new mathematical dependencies were read in full and independently reviewed at their frozen revisions:

- `probability/pair-counts-v1.md`, SHA256 `702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29`.
- `root/effective-operator-v1.md`, SHA256 `13b559897d6ed9253a2fc6dd4dede5dd03914c078558d759542afc9c54d28864`.

The effective proof was reread during this synthesis review. Its older host gap, marked resolvent and finite transfer dependencies were reviewed in the preceding rounds. This review checks their use at criticality as well as the new probabilistic passage to a limit.

Prior exposure includes the proposed phase-dependent top law, the planned strict-inequality CDF formula, previous reviews, and a terminology recommendation about semistable extremes. The reviewer did not write the frozen synthesis. Exposure to the target formula is disclosed rather than treated as an independent discovery of that formula.

## Full spectral chain

The probability theorem concerns precisely the uniform simple labelled fixed-degree host with predetermined marks. Its conditional-host sampling argument proves joint Poisson convergence with means

\[
 \lambda_k=\frac d{2q}c^{3/2}q^{k-\phi}.
\]

The effective theorem uses the same mark model and the critical weight sqrt(d-2). The unweighted interpretation is therefore valid in degree three. Neither argument requires marks chosen after observing the host.

The marked resolvent tail is controlled in operator norm through a squared Frobenius bound. The fixed cutoff estimate is C eta^(-2) q^(-K) after n tends to infinity. Short nonbacktracking interactions are identified with pair distances on a high-probability uniqueness event. The short marked graph is a tight matching. Diagonal errors and stationary corrections vanish on the critical scale.

The exact Schur comparison retains F(d) as its constant term. Its first derivative converges to D I, with D=2q squared divided by (d-2) squared. The finite transfer argument therefore approximates every ordered eigenvalue in the actual near-d cluster, including repeated roots, with an error o_P(s). This is stronger than entrywise matrix convergence and is sufficient for the later growing-dimensional ordering.

For each fixed cutoff, deleting the host coupling to the finite pair sector costs exactly kappa sqrt(2p/m), which tends to zero in probability. The remaining collective eigenvalues have the finite correction sqrt(1-2p/m). This correction vanishes only after being included in the proof. The pair coefficient is

\[
 \frac{(d-2)d^2g}{D}=\frac{d(d-2)^2}{2q}=h.
\]

The resulting multiset has m+1 entries and agrees with the cluster indexing used in the synthesis. In particular, its reflected lower edge is indexed by m+2-j. No exact finite-graph spectral symmetry is assumed.

## Two-sided truncation and random measures

Both truncations are necessary and are supplied. Very short pairs have large amplitude and are removed with a uniform probability bound O(q^(-J)). For a fixed finite offset window, convergence of the discrete count vector and deterministic amplitudes gives convergence of the sorted multiset. Repeated levels and collisions with kappa do not obstruct this continuous mapping.

Weak levels with k>K have limiting amplitude at most h q^(-K). The entire prelimit error from their interactions is controlled by the effective theorem. The argument takes n to infinity before increasing K, which is required by that theorem. It does not substitute a growing cutoff into a fixed-cutoff estimate. Holding eta fixed while taking both cutoffs to infinity, and only then taking eta to zero, proves convergence of every finite ordered edge vector.

The limiting measure is locally finite on the punctured line. It has infinitely many atoms approaching zero and only finitely many above any positive magnitude. Thus every fixed positive ordered coordinate exists and is strictly positive almost surely. The unbounded upper support does not prevent a finite maximum, since the total intensity above a threshold tends to zero as that threshold tends to infinity.

For compactly supported continuous test functions away from zero, an operator error below the distance of the support from zero prevents the many near-zero comparison entries from contributing. The number of potentially contributing ideal atoms is tight. Uniform continuity therefore controls the sum of errors on that tight finite set, rather than multiplying the error by m. This justifies the stated vague convergence and the local tightness needed to pass from finite families of test functions to the random-measure law.

The signed limiting measure is correctly described as dependent. Every geometric pair creates both signs with the same multiplicity, and the two collective atoms are deterministic. Only the positive pair measure is Poisson.

## CDF, atoms and phase

For x at least kappa, w_k>x is equivalent to

\[
 k<\phi+\log_q(h/x).
\]

Its greatest integer solution is ceil(phi+log_q(h/x))-1. Summing the intensities over these indices gives exactly the displayed CDF. In particular, when x equals a pair amplitude, the corresponding index is excluded. The CDF is right continuous and has the claimed positive jump. When a pair level equals kappa, it merges with the collective floor in the distribution without changing the strict-inequality formula.

The explicit formula describes the limiting law at its atoms. The convergence statement does not assert convergence of finite-n CDF values at every discontinuity, which would require more than weak convergence.

At each pair level w_k>kappa, the top has mass

\[
 \exp\left(-\sum_{j<k}\lambda_j\right)
 (1-\exp(-\lambda_k))>0.
\]

Different phases modulo one have disjoint pair lattices. Selecting such an atom strictly above the collective floor therefore proves that their actual top laws differ. This verifies the essential step from geometric lattice oscillations to spectral nonconvergence.

Phase one is phase zero after replacing k by k-1 in both amplitude and intensity. Uniform finite-window truncations give weak continuity on the phase circle. Compactness and injectivity of the resulting family justify the stated equivalence between phase convergence and weak convergence of the normalized top on an arbitrary admissible size sequence.

When all admissible sizes are used, nearest admissible integers to c^(3/2) q^(3(j+phi)) give every prescribed interior phase. The relative rounding error vanishes, and the assumed convergence of m/n^(1/3) contributes only o(1) to the logarithm. Two distinct interior phases suffice to prove absence of a full-sequence top law. The argument does not need a literal fractional-part limit at either endpoint.

## Tails and scope

The ceiling exponent lies between log_q(h/x)-1 and log_q(h/x). This proves the reciprocal intensity bounds. Hence the limiting tail has reciprocal order and its first moment is infinite. The discrete scaling identity F(qx)=F(x)^(1/q) is valid on the stated region x at least kappa. The collective floor is correctly retained when discussing semistable terminology.

The scope remains H=0, fixed d, critical weighting and predetermined marks. No eigenvector localization, normalized Laplacian law, mixing consequence, arbitrary interaction block, or priority claim follows from this review. Existing Poisson, lattice and semistable precedents remain credited by the separate priority notes. The specific explicit spectral law and its coexistence with the collective mode are the mathematical content accepted here.
