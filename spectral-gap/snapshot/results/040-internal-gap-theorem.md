# Batch 040, two-band internal-gap assessment

## State

The concrete source and model check is complete. The deliverable provides a rigorous specialization of quantitative strong convergence for $K_{4,3}$ lifts, not a new optimal tangle theorem.

## Result

For every compact interval $I$ strictly inside $(0,\sqrt3-\sqrt2)$, the probability of a new eigenvalue in $I$ is bounded by $C(K_{4,3},I)/N$. This follows by isolating the interval with a smooth nonnegative function and applying Chen-Garza-Vargas-Tropp-van Handel, Theorem 3.9, to its matrix-valued adjacency polynomial.

Huang-Xu applies because the minimum base degree is three. Its local-law and delocalization statements were read and distinguished from a first-excursion probability. The earlier degree-two subdivision model was rejected as an incompatible shortcut. Zero is explicitly excluded because it is a spectral singularity and every rectangular lift has a forced zero eigenspace.

## Remaining mathematical obstruction

No matching lower bound or optimal exponent has been established. A retained 8-lift has positive inner-gap eigenvalues near $0.22824570$, so the problem is not vacuous. The simplest symmetric $K_{2,3}$ tree-extension calculation gives $(z^2-12)(z^2-10)$, with no positive root below the inner edge. A proof must classify all minimal pruned relative tangles and show how occurrences force a new, rather than old or auxiliary, eigenvalue.

## Artifacts

- [Theorem draft and literature assessment](spectral-research/01-two-band-theorem.md)
- [Exact enumeration script](spectral-research/two_band_checks.py) and [output](spectral-research/two_band_checks.json)
- [Tangle boundary algebra check](spectral-research/theta_boundary_checks.py) and [output](spectral-research/theta_boundary_checks.json)
- [Pseudorandom experiment script](spectral-research/two-band-data/simulate_lifts.py), [summary](spectral-research/two-band-data/summary.json), [verified 8-lift witness](spectral-research/two-band-data/witness-8.json), and [16-lift witness](spectral-research/two-band-data/witness-16.json)

## Next action

Verify the boundary reduction independently and analyze the retained witness's minimal spectral obstruction. Do not present the generic $1/N$ rate as sharp until a matching lower bound is proved.

Swarm `smwgfcleu` is still running separately with its eight original research members. No native DAG was initialized and no additional swarm was launched for this focused batch.
