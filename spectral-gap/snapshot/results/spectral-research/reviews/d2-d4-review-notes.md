# Review notes for the lattice and relative-cover submissions

## Lattice, d2

The Bloch decomposition and analytic Hessian checks reproduce, including the honeycomb calculation and explicit Cayley arithmetic.

Section 7's range theorem needs correction before it can be accepted. It compares $\mu_M(\Lambda)$, a minimum over $\Lambda^*/\mathbb Z^d$ modulo $\mathbb Z^d$, with the shortest full-lattice vector in that Minkowski sense. These are different optimization problems. The parenthetical claim that they agree up to an absorbed factor is not a proof, especially where an allegedly sharp Hermite endpoint is asserted.

A usable one-sided estimate is immediate: $\mu_M(\Lambda)$ is bounded above by the quadratic length of the shortest nonzero vector in $\Lambda^*$, because it is valid to choose the full-lattice representative. That does not establish equality or the desired extremal behavior. Supply a valid argument for every claimed endpoint, or explicitly restrict the result to geometry and normalizations where the equality holds. Do not replace the distinction with a constant absorbed into the definition of $\mu_M$.

The proof also needs to keep the index of the sublattice, the dual covolume and the number of vertices $Np$ explicit throughout. The Cayley-range numerics support the broad behavior, not the exact argument as currently written.

## Relative covers, d4

The two-periodic Collatz-Wielandt bound and the biregular quartic computation are useful. The old/new separation and the associated conditional application of the Hashimoto theorem are clearly identified.

The claimed failure of radial reduction is not established. Constructing the actual finite tree with $(n_0,tail)=(3,[2,1])$ gives 64 vertices at depth 6 and largest adjacency eigenvalue $2.429652634824895$. Constructing the weighted Jacobi matrix from the same level-size sequence gives $2.429652634824895$ as well. At depth 15 both are $2.4488676957068$. The weighted finite reduction does not reproduce the claimed $\sqrt2+1$ Floquet boundary. Applying the advertised Floquet parameter selection to the same actual generator would require a different object from the measured radial reduction.

Thus the example demonstrates an inconsistency in the radial/Floquet conventions or boundary derivation, not that non-radial directions force the spectral radius above the radial result. Establish the correct root, period and weighted Jacobi conventions and reconcile them with the displayed numerical counterexample. Do not infer that degrees alone are insufficient from the present calculation.

## Lattice revision, d2

The revised Theorem 6 is correct and removes the old shortest-vector mistake. The exact constant is the minimum over the nonzero finite torus group $\Lambda^*/\mathbb Z^d$. Since $N\Lambda^*\subseteq\mathbb Z^d$, a nonzero coset has Euclidean length at least $1/N$, which proves the lower endpoint. For the upper endpoint, disjoint balls of radius $r$ about the $N$ torus points require each nonzero difference to have $M$-norm at most $2r$. Their volume is $N\omega_d r^d$ in $M$-coordinates, against total volume $\det(M)^{1/2}$. Optimising $r$ gives the stated constant. The skew family supplies $m(M)/N^2$ through a primitive integer vector, and the cubic family $\Lambda=n\mathbb Z^d$ gives $m(M)n^{-2}$ exactly. Index $N$, vertex count $Np$ and dual covolume $1/N$ are now correctly separated.

There are three qualifications that must remain attached to reuse.

1. `s12_coset_minimum.py` tests the 17 indices `2,3,4,5,6,8,9,12,16,25,36,49,64,100,144,196,256`. It does **not** test every $N\le 256$ as the report and dossier say. The exact computations at these sampled indices ran successfully. This numerical overstatement does not affect the analytic range proof.
2. Theorem 4's conversion of $|\kappa|^4$ into $O(\mu_M^2)$ uses $\kappa^TM\kappa\ge\lambda_{\min}(M)|\kappa|^2$. It needs $M$ positive definite. Only that version is accepted here, not the unqualified semidefinite remainder claim. A singular-$M$ law needs separate treatment, exactly as the dossier's conjecture and open-case discussion indicate.
3. Lemma 1's torsion reduction says that an eigenvector phase is a sign. A complex eigenvector need not have phases $0$ or $1/2$. The conclusion survives by a direct repair: Perron-Frobenius equality gives phases $\phi_u$ with $\langle\kappa,g\rangle+\phi_v-\phi_u\in\mathbb Z$ on each edge. Summing around a cycle gives $\langle\kappa,w(C)\rangle\in\mathbb Z$. The winding rank is $d$ by connectivity, so $\kappa\in\mathbb Q^d/\mathbb Z^d$. This replaces the finite-sign-pattern argument and restores the strict maximum conclusion.

With those qualifications, the exact Bloch decomposition, the positive-definite band-edge sampling law, and the coset range theorem are useful results. The positive-definiteness conjecture, arbitrary singular-$M$ rate, sharp packing constant, and non-abelian extensions remain open. No comprehensive novelty certification is made.

## Relative covers revision, d4

The revision resolves the mathematical objection above. The old diagnosis was false and is now explicitly withdrawn. In its place, Proposition 3 makes the correct distinction between the essential spectrum of the radial half-line Jacobi operator and an isolated eigenvalue caused by a root defect.

The Jacobi coefficients satisfy $b_k^2 = |S_{k+1}|/|S_k|$, independently of the member's reduction script. The stated sequence gives the root equation and every interior equation at $\lambda = \sqrt6$. The two-step periodicity propagates the residual identity after the initial checks. Its $\ell^2$ sum is $8$. For clarity, if $u_k$ is the Jacobi-coordinate eigenvector, the full-tree radial eigenfunction is $f(x)=u_k/\sqrt{|S_k|}$ for $x \in S_k$. The squared mass of shell $S_k$ is therefore $u_k^2$, not $|S_k|u_k^2$.

Changing the first Jacobi coefficient is a finite-rank perturbation of the periodic operator. The essential spectrum is consequently the computed periodic two-band set $\pm[\sqrt2-1,\sqrt2+1]$. The band polynomial is $(x^2-3)^2-8$ and equals $1$ at $x=\sqrt6$, so the eigenvalue lies strictly outside the bands. Thus $\rho(A_T)\ge \sqrt6>\sqrt2+1$. This does not assert that non-radial modes raised the radius, so the previous objection no longer applies.

The retained two-periodic Collatz-Wielandt bound, subdivision identity, biregular quartic computations and conditional Hashimoto conversion were also re-run. The example in Proposition 3 is a defect tree, not itself claimed to be the universal cover of a finite base. Its role is to prevent an unqualified identification of essential Floquet bands with the full spectrum. The utility header `scripts/floquet_bands.py` still contains the old unqualified spectrum equivalence. That docstring must not be cited as a theorem after this correction.

Verification artifacts: [independent exact check](d4_bound_state_review.py) and [its output](d4_bound_state_review.json). The member's `bound_state_check.py` and `biregular_checks.py` both ran successfully. This review does not certify the open general irregular conversion problem or a comprehensive novelty claim.

## What was actually run

- Lattice: `code/s10_M_formula_2d.py` and `code/s01_abelian.py`.
- Relative covers: `scripts/biregular_checks.py`, plus independent dense construction of the reported tree using `build_tree_sparse` and of a Jacobi matrix using the sphere sizes directly.
- The finite tree has degrees 3,2,3,2 repeating across all levels. Its weighted Jacobi truncation was computed from $\sqrt{w_{k+1}/w_k}$ on successive level counts, not from the unverified Floquet formula.
