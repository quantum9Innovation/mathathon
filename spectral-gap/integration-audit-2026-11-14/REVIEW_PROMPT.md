# Independent review request

Read the workspace rules and the research collaboration skill. Audit [permutation-proof-v1.md](../audit-2026-11-14/permutation-proof-v1.md) from its formulas, rather than from its stated status. Keep the reviewed revision fixed even if a later revision appears.

The target is a mixed centered permutation-product bound for arbitrary multiplicities, including inconsistent cells and any number of independent permutation colors. Check the inverse-gamma moment identity, its recurrence, the induction constant, compatible-set expansion, the global prefactor and all small-parameter cases. Check the mapping to Proposition 28 of arXiv:1502.04482v4 and Lemma 7 of arXiv:1804.07808v6 directly.

Then independently inspect the source conditioning examples in [source-findings-v2.md](../audit-2026-11-14/source-findings-v2.md). Distinguish a failed intermediate assertion from a failed theorem. Use exact enumeration if helpful, with explicit finite limits. Do not infer literature novelty from a successful proof or an unsuccessful search.

Write your review to a new file named EXTERNAL_REVIEW.md in this directory. Record SHA256 hashes of the reviewed files. Do not edit the reviewed proofs, imported snapshot, coordinator, workflows or skills. No external publication or teammate message is requested. Preserve the selection cutoff of November 15 at 12:21 AM Pacific and return a substantive checkpoint within thirty minutes.

If the argument survives, identify the strongest supported statement and give a brief intuitive explanation of why isolated centered cells gain suppression while conflicting cells do not.
