# One-conflict integration candidate comparison

Date: November 14, 2026, America/Los_Angeles.

Decision: Accept the mathematical compression in the inspected candidate. This is a separate comparison performed after the author-proof review was frozen.

Candidate: extension-round-02/integration/one-conflict-candidate.tex.

Candidate SHA256: 273a85280c4b7e1e7794269a7ddeed4648848b3410eed2cc2dc7c5efda0cdcff.

Accepted author proof SHA256: 4ed2c2cbe44c453eb401ebbf20eae09b35a9365d018f86abee262fc38dca83f4.

Frozen author-proof review SHA256: 5ac1ec2430090fc4298ff3232f8651927c3a13d8e059890e05326f5c19aecb38.

## Retained arguments

The candidate preserves the exact kernel difference and its domain $j+r+1\le n$, with centering fixed at the original $n$. Its $j=0$ endpoint is covered by the existing empty-moment convention.

The theorem preserves $b\ge1$, the automatic restriction $h\le a-2$, the factor $2^{b-1}$, the reduced polynomial parameter $a-h-1$ and the denominator $(n)_{a-1}$. The exact-maximum claim is limited to $b=1$ and ranges over the same patterns, powers and independent colors.

Both selected-support cases are present. Internal incompatibility gives zero. A selected neighbor forces the distinguished indicator to zero. Avoiding all neighbors omits at least one member of $V$, which permits the kernel difference bound. The positivity assertion in the second case follows from the existing conditioned-moment formula. All kernel total indices stay at most $a-1$, so the $a=n$ endpoint is retained.

The affine sum retains the exact weighted product and counts the remaining $b-1$ centered singletons. The attaining one-color pattern has the correct counts and the correct negative expectation. Its coordinates remain valid at $a=n$. The final comparison to one half of the earlier bound is correct, and does not claim general sharpness.

## Integration dependencies

The candidate depends on the existing definitions of $\mathcal P_j$, $F_n$, $K_{j,r}$, and the affine coefficients $c_e,d_e$. Its external labels eq:product, lem:mixedmerge and eq:weights all exist in frozen v7 mixed.tex. The new labels lem:kerneldifference, thm:oneconflict and eq:oneconflict do not collide with that frozen source.

An insertion after the proof of Theorem thm:mixed and before the scalar consequences has all necessary definitions and arguments available. The retained v7 mixed theorem remains valid as the earlier envelope.

Before freezing an assembled successor, update the contribution scope in the discussion. The v7 sentence saying that the attained-maximum assertion concerns $b=0$ would become incomplete after this insertion. The successor should identify both exact cases $b=0$ and $b=1$, while reserving any sharpness assertion for $b>1$. This is an assembly dependency, not a flaw in the candidate theorem.

This comparison checks the source and its mathematical dependencies. It does not certify a compiled successor PDF or its revised global summaries.
