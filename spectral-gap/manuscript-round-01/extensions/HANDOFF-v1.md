# SG-M3 handoff

Sender: extension investigator. Recipient: problem 21 integrator.

Base revision: the frozen threshold and critical-scale inputs in `../inputs/MANIFEST.json`. Prior exposure included their proofs, not a review of the extension. The root supplied the target and requested this separate investigation.

## Outputs

- `hyperbolic-window-v1.md`: frozen complete proof of EXT-A and EXT-B. SHA256 is recorded in `MANIFEST-v1.json`.
- `check_extension.py`: exact coefficient and permutation checks, numerical finite envelopes and square-root boundary examples.
- `extension-checks-v1.json`: successful check results with the proof hash and precision.

## Proposed claim state

EXT-A is proved in writing and awaiting independent review. It establishes the finite envelope in equation (3), the logarithmic error bound in equation (4), and relative hyperbolic approximation for every $k=o(\sqrt N)$. This strengthens the approximation window without changing the cubic threshold for the older leading term.

EXT-B is proved in writing and awaiting independent review. It establishes the relative correction $\exp(d/4)$ when $k^2/N\to d>0$, and uniform corrected approximation for $k\le C\sqrt N$. It shows why the uncorrected hyperbolic approximation develops a persistent error at the square-root scale.

Both depend on the known recurrence and leading terms. The positive generating function is a reformulation of the known Laguerre identity. It is not proposed as a historically new identity. The extension does not depend on the frozen critical-scale proof, except as a comparison of scope.

## Checks executed

All 1061 exact comparisons among inclusion-exclusion, the two-step polynomial recurrence and positive partition coefficients passed. Direct enumeration of 5912 permutations verified 33 moment cases. Numerical finite-envelope checks passed in 4471 cases, with 508 checks of the tighter logarithmic envelope. Eighteen square-root examples at sizes through $10^8$ agree with the claimed limiting correction. Numerical calculations used 80 decimal digits.

These computations corroborate finite instances and implementation. The proofs of the uniform statements are the mathematical evidence. No end-to-end formal verification is claimed.

## Findings and limits

No mathematical defect was found during the extension derivation. The priority investigator verified that the generating function follows from a classical Laguerre identity and found no direct duplication of the quantitative window or square-root correction in the bounded neighboring-source search. That is not a comprehensive priority certificate. The final source note should govern novelty language.

The precise comparison parameter is $\lambda=(2/3)\sqrt{(2\lfloor k/2\rfloor)^3/N}$. In particular, the odd case uses $k-1$ inside the cube. The positive generating series uses an explicitly defined polynomial continuation beyond $k=N$, not nonexistent additional permutation moments.

No theorem is asserted for unbounded $k/\sqrt N$, no explicit rate is asserted for the square-root correction, and no graph spectral-gap conclusion is inferred automatically.

## Requested next action

Assign an independent reviewer to the frozen proof hash, with particular attention to the odd normalization in (13), the lower-envelope probability weights, and the tail and parity control in Steps B1 through B4. Promote the claims only after resolving that review, then integrate the two results as distinct theorems with a pair/triple/four-block explanation.

Stopping reason: the selected extension yielded two complete auditable statements and corroborating checks within the first bounded investigation. Further speculative expansion is deferred to preserve review and manuscript time.
