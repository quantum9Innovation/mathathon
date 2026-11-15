# SG-E3 TeX integration handoff

Date: November 14, 2026 Pacific

Owner: manuscript_referee

Recipient and integrator: root

Candidate: mixed-v6.tex

## Content

The replacement leads with the exact envelope and its attained maximum for b=0. It uses the polynomial name mathcal P_j(n,r), distinct from the diagonal factorial correction D_k. The coefficient identity, positive partition weights, color merge, affine reduction and attaining family are derived within the section.

The depleted row-sum recurrence remains self-contained. The count-dependent Gamma bound yields the former beta bound, followed by the general factorial estimate and the optimal square-root-range prefactor. Bordenave and Zhu retain explicit credit for the prior raw factorial estimate in Lemma 2.1, equation (2.3). The exact mixed refinement is not attributed to that source.

The final subsection gives the fixed-h improvement, the growing-h pairing obstruction and the separate-dimension product corollary. No first-discovery or general priority claim is made. The old standalone conditional example is removed because the exact polynomial and attaining family now supply that calculation directly.

## Labels and integration points

All original mixed-section labels are preserved.

- thm:mixed now labels the exact attained-envelope theorem.
- lem:depleted and eq:depleted retain their previous meaning and domain.
- lem:super now states the stronger Gamma bound and its comparison with beta.
- eq:mixedgeneral and eq:mixedmain retain their previous inequalities and now belong to cor:mixedscalar.
- eq:prescribed now labels the exact selected-term identity, which strengthens the old upper bound.
- eq:product, eq:weights and eq:beta retain their meanings.

New labels include eq:mixedexact, eq:depletedpoly, eq:poly-moment, eq:depletedpartitions, lem:mixedmerge, eq:mixedgamma-def, cor:mixedscalar, eq:mixedgamma, eq:mixedfixedh and eq:mixed-dimensions.

In spectral.tex, the direct sentence introducing the square-root bound should cite Corollary cor:mixedscalar in place of Theorem thm:mixed. The other references to the mixed theorem remain valid because the exact theorem gives the required input. The threshold section's recurrence reference remains unchanged. The introduction's multiplicity and larger-range statement remains true.

The contribution discussion should now describe the attained polynomial envelope and Gamma refinement before mentioning beta as a scalar consequence. The existing Bordenave and Zhu priority distinction should remain. No bibliography key or package is added. The section uses the existing CN, DLMF and BZ entries and the existing theorem environments and notation macros.

## Validation and scope

The mathematical dependency is the accepted SG-E3 proof with SHA-256 878a139aee3caf6040debcc0f9b476e5fa0dd283c70c2a75a48ceaaea38d6b4d. Its independent review is mixed-by-saddle-v1.md, SHA-256 e4a0be4fc6bdbabcd4d906f9f2f0cacc8660cb77bc854bdc301a093f818d5b36.

The draft preserves the h=0 full-depletion convention, restricts the first-moment seed to r<n, handles Gamma=0 at a=h=1, and gives the former beta estimate only for a at least two. The exact maximum remains restricted to b=0.

Static checks passed for required labels, duplicate labels, environment balance, bibliography keys and prohibited punctuation. The draft has 251 source lines and targets approximately five manuscript pages. Pagination and the assembled cross-references remain for root's compilation and the independent assembled-revision audit, as assigned. No PDF edit marker was repeated.

No canonical manuscript or frozen source was edited. Replace the mixed section only from the frozen candidate, make the cross-reference adjustment above, then compile and audit the assembled revision.
