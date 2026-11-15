# Review of the almost-regular graph submission

## Assessment

The two central exact contributions are sound:

1. For one degree-$\Delta$ defect in an otherwise $d$-regular tree, the regular essential bulk remains, while an outer discrete pair exists exactly when $\Delta>2(d-1)$, with $\lambda_*=\Delta/\sqrt{\Delta+1-d}$ and sign symmetry.
2. Adding one vertex to a prescribed vertex set $T$ gives the Schur complement characteristic-polynomial identity with the correct signs, and its host-spectrum survival interpretation is valid after using Cauchy interlacing for a vertex deletion.

The resolvent tree calculation properly distinguishes the one-sided branch parameter $r(\lambda)$ from the full Kesten-McKay transform $G_d(\lambda)=r/(1-r^2)$. This explains why the finite-host fixed-point threshold differs from the spectrum of the infinite spiked tree.

The finite-host top-eigenvalue law is explicitly labeled conjectural in the dossier, with hypothesis (H) identifying the missing resolvent estimate. It is not accepted here as a proved result.

## Checks run

- Ran `scripts/exact_secular.py` on all three examples. The symbolic identities passed identically.
- Ran `scripts/spiked_tree_jacobi.py`. Bulk and outer spectral values matched the stated cases to solver precision.
- Independently checked $G_d(d)=(d-1)/(d(d-2))$ and the bulk-edge transform. The threshold $2(d-2)$ follows, rather than the tree threshold $2(d-1)$.
- Independently checked the secular equation and fixed point numerically for $(d,\Delta)=(3,6),(4,7),(5,8)$. See [d3_resolvent_checks.json](d3_resolvent_checks.json).

## Review boundary

I read the full dossier and proof details, but did not independently verify every reference, every numerical random experiment, every multi-spike interpretation, or the control in the narrative about the absence of a bottleneck. Those are not needed to justify the exact tree and secular results, and are not accepted as proved consequences. No exhaustive novelty certification is implied.

The full bulk argument is explicit, including a bounded root residual. Embedded bulk eigenvalues remain honestly unclassified rather than being claimed away.
