---
id: 060
title: Establish a secular law for clustered attachment points
state: running
budget_s: 10800
parallel_ok: false
done_when: "A complete added-vertex secular law is proved and reviewed for at least one explicitly clustered attachment family, with exact resolvent coefficients, thresholds, pole bookkeeping and limiting roots, or a precise obstruction is established without altering the separated-case proof."
---

## Goal

Replace the separated-set approximation by the correct off-diagonal resolvent equation
for bounded clustered attachment sets. Start with an adjacent pair and the full
neighbourhood of one vertex. Prove the actual root behaviour and where it differs from
the frozen separated-case theorem.

## Frozen inputs

- `results/050-finite-defect.md` and the accepted proofs in
  `.ultramath/smwgwbyn9/m2/`, `m1/`, `m4/`, `m5/`, and `m6/`.
- Exact source versions and hashes in
  `results/spectral-research/batch-060/FROZEN-SEPARATED-CASE.md`.
- The new target and evidence criteria in
  `results/060-clustered-attachment-target.md`.

The completed separated proof is an input, not an object to rewrite or silently
reinterpret for this new setting. A real defect would require a named erratum and
independent review, not hidden edits.

## Plan

1. Derive exact tree-kernel coefficients for an adjacent pair and $T=N(c)$.
2. Obtain the random-host resolvent limit for rooted bounded clusters, retaining
   old-fibre, pole and separation terms exactly.
3. Prove root location, threshold and limiting-eigenvalue statements, including
   singular or repeating cases rather than assuming simple roots away from $d$.
4. Independently reproduce the unchanged separated case as the disconnected-pattern
   limit, then produce clustered numerical and exact checks.
5. Reserve the final 45 minutes of a three-hour run for adversarial review, the report
   and honest closure. Write `results/060-clustered-attachment.md`.

## Proposed parallel roles

1. Adjacent-pair algebra, root counts and edge cases.
2. Full-neighbourhood kernel, root counts and pole analysis.
3. Rooted-cluster embedding and a rank-one exterior resolvent proof.
4. Independent counterexamples, numerical reproduction, source checking and refereeing.

Use at most four members in one swarm, `deepseek/deepseek-v4.1-flash` at maximum
reasoning effort, if the batch is subsequently authorised to run.

## Status and limits

This is a pending proposal for a three-hour batch, not a running batch or a claim of
completion. No swarm has been started and no clock has been consumed by writing this
target. Later execution requires an explicit go-ahead. The separated proof is not to
be broadened merely because it is now available for a different attachment model.
