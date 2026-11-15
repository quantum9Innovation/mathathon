# Status

## Current state

Phase 1 is complete for arXiv:cs/0405020v1. All 118 PDF pages were read in complete ranges. The original TeX was consulted for exact formulas. Both substantive figures were rendered and inspected directly. No substantive visual remains unexamined.

## Completed reading and synthesis

- [x] Metadata, source integrity, random graph models, and main statements in Section 1
- [x] Standard trace method and its obstruction in Section 2
- [x] VLG, realization, non-backtracking growth, and $\operatorname{Tree}_d$ machinery in Section 3
- [x] Tangle occurrence rates and lower failure probability in Section 4
- [x] Walk sums, forms, types, and new types in Section 5
- [x] Selective trace counting and model-specific $\tau_{\mathrm{fund}}$ in Section 6
- [x] Ramanujan functions and selective trace expansions in Sections 7 and 8
- [x] Conditional tangle strata and Möbius inversion in Section 9
- [x] Strongly irreducible spectral identities in Section 10
- [x] Sidestepping lemma in Section 11
- [x] Magnification and spreading in Section 12
- [x] Final spectral assembly in Sections 13 and 14
- [x] Open problems, glossary, and references in Section 15 and pages 113 to 118
- [x] Figure 1 on page 31 and Figure 2 on page 41
- [x] Central derivations, assumptions, limitations, and source defects

## Dossier map

- `SOURCE.md`: identity, source paths, hashes, and reading coverage
- `01-executive-map.md`: contributions and mastery goals
- `02-prerequisites.md`: background needed for the proof
- `03-notation.md`: objects, types, and notation collisions
- `04-paper-structure.md`: section map and complete visual inventory
- `05-main-results.md`: main claims and dependency graphs
- `06-derivations.md`: expanded central arguments
- `07-techniques.md`: reusable proof machinery
- `08-intuition.md`: explanations at several altitudes
- `09-assumptions-and-weak-points.md`: hypotheses, limits, and source defects

## User background

Unknown. The working assumption is comfort with finite-dimensional linear algebra, elementary graph theory, basic probability, and asymptotic notation. The prerequisite file separates fluent requirements from topics that can be reviewed on demand. No teaching session has occurred, so `LEARNING-RECORD.md` has not been created.

## Hardest points to revisit

1. **Theorem 6.6:** Why selectivity gives walk growth strictly below $\sqrt{d-1}$, and why long type edges strengthen the bound.
2. **Theorems 8.2 and 8.5:** How the walk growth bound cancels the inverse decay of the edge-length summations and yields d-Ramanujan coefficients after summing over all multiplicities.
3. **Theorem 9.3:** Why conditional tangle strata still admit expansions, and why minimal supercritical tangles form a finite set.
4. **Lemma 11.1:** How finite differences remove unknown polynomial coefficients and isolate $\theta_i$ values bounded away from zero.
5. **Section 13:** The exact choice of $k\asymp\log n$, the treatment of complex $\mu$ pairs, and the conversion back to adjacency eigenvalues.

## Local unresolved points and source defects

The supplied text has several local defects that must not be silently normalized:

- Page 12 says $q_k(d)=(d-1)^k$, while the recurrence and Theorem 2.7 require $q_k(d)=d(d-1)^{k-1}$ for $k\geq1$.
- The proof of Theorem 6.10 first identifies $\lambda_{\mathrm{Irred}}$ with the square root of a matrix Perron value and then equates it with that Perron value. The square root reading gives the intended comparison.
- The proof of Lemma 9.2 says $\psi_\infty$ properly contains the $\psi_i$, although its limit construction and the adjacent example require the reverse inclusion.
- Theorem 1.3 imports the $\mathcal G_{n,d}$ exponents for $\mathcal J_{n,d}$, while Theorems 4.13 and 6.12 compute the larger $\mathcal I_{n,d}$ style exponents. The lower probability statement needs reconciliation. The high probability Alon conclusion is not threatened by using the larger exponent.
- Figure 2 uses $v_2$ near vertex 4 in a way that is coherent for the compressed type numbering but not for first-visit numbering in the original form.

These and smaller presentation issues are detailed in `09-assumptions-and-weak-points.md`. No fatal gap in the main $\mathcal G_{n,d}$ proof was established by this reading, but no independent verification of every constant, tail estimate, or model transfer is claimed.

## Remaining work

No required Phase 1 reading remains. Phase 2 material is on demand: teaching, oral examination, talk preparation, a meeting brief, or research directions. Optional numerical checks are identified in the derivation notes but were not run, since they require user approval.

## Next recommended action

Teach the central mechanism using Figure 2: compress walks into new types, bound selective walk growth below $\sqrt{d-1}$, and use that gap to make the expansion converge. Then ask the user to explain why the ordinary type expansion cannot establish the same convergence.
