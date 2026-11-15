# Mixed-degree bounded moments with forced zero omission weights

**Proved:** the root candidate's bounded raw finite-field moment theorem holds under symmetric `0<=q_ij<1/2` omission weights with `sum_j d_ij q_ij=1`, including weights forced to zero. The proof uses the stated closed heterogeneous channel class. Historical priority is not asserted.

For every fixed reversible integer frame, positive fixed proportions, prime `p`, dimension `r`, and matrix `R`,

```
sup_N E #{Y in F_p^(n by r): A_N Y=Y R}<infinity.
```

Total degrees may differ. The model has independent internal uniform stub pairings and cross-stub bijections, retaining loops and multiplicities; the theorem also transfers directly to independent uniform simple factors. Every admissible size residue and characteristic two are covered. All fixed powers of the raw count are bounded.

The accompanying composition gives **unconditional expected `soft-O(n^2)` bit work** for blind recovery of the finest planted partition within fixed class and degree bounds, with high-probability statistical correctness. It uses the existing certified sparse full-kernel primitive, now supplied with the required raw odd-prime vector moment for every candidate target.

## Main artifacts

- [channel-moments.pdf](channel-moments.pdf), eleven-page standalone moment proof; [TeX source](channel-moments.tex).
- [fast-recovery-composition.pdf](fast-recovery-composition.pdf), six-page complete structural and charged algorithm composition; [TeX source](fast-recovery-composition.tex).
- [bounded-channel-moment-theorem.md](bounded-channel-moment-theorem.md), expanded theorem assembly with exact model and induction class.
- [zero-phases.md](zero-phases.md), weighted entropy identity, all finite uniform-coset phases, and strict dimension descent.
- [central-channel.md](central-channel.md), heterogeneous physical-table covariance, maximal lattice, relative tilted local limit estimate, exact weighted reference normalization, concentration, and tail integration.
- [boundary-channel.md](boundary-channel.md), selected active/cancellation certificate, exact conditional forcing, rank comparison, and weighted enumeration.

Both PDFs build in two `pdflatex` passes with no warnings, unresolved references, or overfull boxes. Full source and artifact hashes are recorded in [artifact-manifest.sha256](artifact-manifest.sha256).

## The key repairs are proved explicitly

Inactive quotient channels can have kernels. The boundary proof selects all positive-weight edges incident to the nonzero quotient support, then one inactive cancellation edge at each outside vertex with exactly one selected active support incidence. Selected support degree is at least three and selected outside degree at least two, giving `E-V>=|S|/2`. It places no absence condition on unselected edges. Selected inactive stubs at the support are counted explicitly, and exact forcing couplings control correlation with the restricted kernel. The resulting boundary correction is `O(n^-1/2) E Z_H`, including singleton supports, loops, and parallel edges.

The zero phases can have different root subspaces at different types even when the full type support is nonbipartite. Three active physical omissions force uniform image cosets; active isomorphisms transfer this to every root law, and inactive image subspaces lie in the local output subspace. These finite phases restrict to exactly the same channel class.

The full-uniform prefactor is controlled by the exact identity `K_N E_Q W=1`. Its heterogeneous-space normalization follows from reversibility and symmetric unit-row omission budgets. The central estimate retains full physical-slot tables with their different widths, proves their identical positive covariance and every lattice period, and integrates a relative cubic likelihood ratio under an actual normalized configuration-plus-iid-label probability law.

## Forced-zero examples

The two-type frame `[[0,3],[3,1]]` has degrees three and four; its row budgets force `q_12=1/3` and `q_22=0`. With zero on-site maps it illustrates proper phases `H_2` strictly contained in `H_1`. Its degree groups make its partition easy to detect, so it is used as a phase example.

For a forced-zero model with nontrivial fine fibers, take two copies of `K_3,3` and add one bridge from a left vertex of the first copy to a right vertex of the second. Regard its twelve vertices as types and independently lift each base edge by a uniform matching. Core weights `1/3` and bridge weight zero satisfy the certificate. Summing the first copy's left row equations and subtracting its right row equations forces every certificate's bridge weight to be zero. This connected degree-three/four frame is therefore outside the all-positive class and inside the proved theorem and recovery composition.

## Independent source-bound audits

Three fresh adversarial agents read the actual complete sources. Their module and complete-chain audits are retained:

| Review | Central/lattice reviewer | Zero-phase reviewer | Certificate/assembly reviewer |
|---|---|---|---|
| Own module | [audit-central.md](audit-central.md) | [audit-zero-phases.md](audit-zero-phases.md) | [audit-boundary.md](audit-boundary.md) |
| All modules and master | [audit-full-central.md](audit-full-central.md) | [audit-full-zero.md](audit-full-zero.md) | [audit-full-boundary.md](audit-full-boundary.md) |
| Whole standalone moment TeX | [audit-tex-central.md](audit-tex-central.md) | [audit-tex-zero.md](audit-tex-zero.md) | [audit-tex-boundary.md](audit-tex-boundary.md) |
| Whole recovery composition | [audit-composition-central.md](audit-composition-central.md) | [audit-composition-zero.md](audit-composition-zero.md) | [audit-composition-boundary.md](audit-composition-boundary.md) |

The moment master is frozen at `9248cfd3...`; its only change after the first complete-chain reviews made the strict open-neighborhood choice literal. All reviewers refreshed against that exact final source. The standalone moment TeX is frozen at `cd522c34...`; the composition TeX at `ec3e96da...`. The [primary assembly audit](root-assembly-audit.md) records the final interfaces explicitly: the boundary module's on-site maps are linear, as imposed by the main theorem and standalone TeX.

The composition identifies its actual existing dependencies: the zero-weight one-hot addendum `2db029a9...`, its mixed-degree support and clean-neighborhood closure, and the certified symmetric kernel theorem plus nonsymmetric right-kernel reduction audited at `127b233e...`. The algorithm enumerates the projected complete right kernel, verifies original integer identities, finishes the entire finite candidate search, and charges rare large kernels through the raw moment. It uses one fixed odd prime throughout.

## Scope and provenance

This packet proves fixed-parameter results. It does not extend to weights equal to `1/2`, growing fields or frames, noise, or arbitrary dependent factors. Its algorithmic conclusion depends on the identified existing certified sparse linear-algebra primitive; dense elimination alone would give a cubic cost.

[PROVENANCE.md](PROVENANCE.md) credits graph-cover counting, central and lattice prefactors, nonbinary loop calculus, existing raw cover bounds, and the earlier perfect-code linear-algebra context. The elementary graph-to-linear-system idea and the kernel primitive are not claimed as new.

The candidate, regular-frame packet, positive-omission work, and recovery/linear-algebra dependencies were read without edits. Every research artifact for this session was written only under `spectral-gap/zero-omission-channel-session/`.
