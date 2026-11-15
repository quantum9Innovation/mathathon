# Batch 020, initial research map

## State

The initial synthesis is complete. Swarm `smwgfcleu` is running independently with eight members. At the last status check six members had registered distinct directions on periodic band edges, degree defects, irregular relative covers, hypergraph gap normalization, binary Cayley character codes, and directed spectra. Two were still selecting directions. No submission has been accepted.

## Deliverables

- [Common spectral-threshold framework](spectral-research/00-threshold-framework.md), including a precise invariant-subspace formulation, the Ihara-Bass and incidence translations, proof architecture, and six research priorities.
- [Source-checking notes](spectral-research/SOURCE-NOTES.md), distinguishing full sections read from abstract-level checks and explaining the novelty boundary.
- [Reproducible baseline script](spectral-research/baselines.py) and [output](spectral-research/baselines.json) for a complete hypergraph, a lattice torus, and degree-defect secular equations.

## Checked conclusions

The Bordenave-Collins random-lift theorem settles the full irregular adjacency threshold and gives Hausdorff convergence of the new spectrum. The Dumitriu-Zhu theorem already handles the usual Feng-Li hypergraph second-eigenvalue analogue. Consequently the stronger remaining problems concern internal bands, rates, new cover models and relative modes, not merely replacing the graph by a hypergraph or dropping regularity.

Exact baseline computations show that the complete 3-uniform hypergraph on six vertices has a simple Perron eigenvalue, and that the square torus has a vanishing adjacency gap. The degree-defect secular equations were corrected in the branch recurrence and include the radial square-summability parameter. Full mathematical certification and exhaustive novelty verification were not attempted.

## Next action

Review each swarm submission independently against its claimed proof, citations and reproducible artifacts. Compare the six priorities with the actual results, then prepare a follow-up synthesis rather than accepting a research claim merely because its program ran.
