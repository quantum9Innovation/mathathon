# Completed critical-law round

November 15, 2026. Task: critical-law-round-01. Sender and integrator: root. Intended recipient: the next spectral research round. Canonical claims: SG-25 and SG-26.

## Inputs and completed objective

The base is the [frozen next-problem packet](input/NEXT_PROBLEM-v1.md), the [run contract](RUN_CONTRACT.json), and the accepted growing-defect and close-pair transition rounds. Their frozen artifacts remain unchanged.

The critical H=0 limiting law is proved on paper and separately reviewed. For fixed d>=3, q=d-1, m/n^(1/3)->c>0 and s=sqrt(m/n), the distance phase is the fractional part of log_q(1/s). Along a phase limit phi, independent Poisson counts have means d c^(3/2)q^(k-phi)/(2q). Each contributes paired levels plus and minus h q^(phi-k), where h=d(d-2)^2/(2q). Add the collective levels plus and minus kappa, where kappa=d(d-2)^(3/2)/(sqrt(2)q).

The full point measure away from zero and every fixed number of upper and lower cluster order statistics converge to this object. Its top distribution is explicit, including the correct value at every lattice atom. Distinct phases modulo one give distinct laws. Weak convergence is equivalent to phase convergence on the circle. Every phase occurs over all admissible sizes, so there is no full-sequence weak limit on that size set.

## Frozen proof revisions

| Artifact | SHA256 |
| --- | --- |
| probability/pair-counts-v1.md | 702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29 |
| root/effective-operator-v1.md | 13b559897d6ed9253a2fc6dd4dede5dd03914c078558d759542afc9c54d28864 |
| root/critical-law-v1.md | e379a0b55e81925276d2c3046ec1cc4b25c21e028d22fef53516f4b5828e48f3 |
| formalization/SOURCE_MANIFEST-v1.json | f03a52bc3edd6bbeb5206a2e721f0a64e3abaad216a4b70021897fea3cef6432 |

All direct premises and exact review bindings are recorded in [EVIDENCE_DAG.json](EVIDENCE_DAG.json). Use the two uniquely named full-law reviews, [independent](reviews/critical-law-independent-v1.md) and [by the probability author](reviews/critical-law-by-probability-v1.md). The generic review path is a preserved duplicate of the latter. The former was recovered after the filename collision, and its hash matches the original frozen review exactly.

## Validation and limits

There are no unresolved mathematical findings in the accepted revision. Both full-law audits accept the probability-to-spectrum truncation and the phase distinction. The formal packet has 30 finite declarations, checked from source twice with pinned read-only dependency caches. It does not encode probability, graph geometry, analytic transfer, full multiplicities or the infinite point process. Dependencies were not rebuilt. Details and the retained independent receipt are in the [formal scope review](reviews/formal-scope-v1.md).

The [evidence check](EVIDENCE_CHECK.json) and four rejection controls pass. The explicit distribution figure passes formula, atom, monotonicity and scaling checks. It is illustrative evaluation of the proved limit, not empirical proof. [VERIFICATION.json](VERIFICATION.json) inventories the final packet and preservation checks.

Priority remains unverified after the bounded primary-source comparison. Poisson approximation, lattice distance limits, Poisson spectral-edge statistics and max-semistable extremes all have substantial prior literature. The candidate contribution is the exact graph-specific critical defect law and its spectral transfer. No universal transition across models or resolved published open question is claimed.

The round did not use the research_lab scheduler. The [orchestration note](root/ORCHESTRATION.md) records actual read-only inspection and current compatibility limits. Native tasks completed the mathematics. A local validator implements frozen dependency and review checks without an archived worker protocol or unattended controller.

## Requested next action

Start a new bounded round from [NEXT_PROBLEM.md](NEXT_PROBLEM.md): determine critical spectral subspace masses and the separate resonance case where a pair level meets the collective level. Begin with the cubic H=0 model. Keep each repeated pair level as a subspace until an additional splitting theorem justifies individual eigenvectors. Do not infer localization or normalized-Laplacian mixing from the present eigenvalue theorem.
