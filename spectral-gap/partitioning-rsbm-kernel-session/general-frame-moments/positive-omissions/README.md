# Positive-omission mixed-degree moment packet

Completed derived proofs with fresh actual-source audits. Historical novelty is not certified. Every source in the parent regular-frame packet remains frozen; its complete hash manifest was rechecked unchanged.

## Exact scope

Let `F=(d_ij)` be a fixed connected reversible nonnegative integer frame with fixed positive type proportions. Its total degrees `d_i=sum_j d_ij` may differ. Require symmetric weights on **every active factor**, including internal factors:

```
0<theta_ij=theta_ji<1/2,
sum_j d_ij theta_ij=1 for every old type i.
```

These conditions imply `d_i>=3`. The factors are independent uniform internal stub pairings and cross-stub bijections, optionally conditioned directly on simplicity at sizes where the simple factors exist.

**Theorem.** For every fixed prime field, fixed target dimension, and matrix `R`,

`sup_N E #{Y:AY=YR}<infinity`.

The bound includes all admissible scale residues, singular maps, repeated physical slots, internal degrees zero or one, and unequal individual type sizes. Bipartite mixed-subspace phases are handled by a closed two-space induction.

**Recovery consequence.** In the independent uniform simple-factor law, the existing certified right-kernel algorithm and strict-weight one-hot structural theorem now give unconditional expected `soft-O(n^2)` bit work for blind recovery at fixed class and degree bounds. Input is only `A,K,D`; the algorithm does not know the frame, sizes, or weight certificate. The external certified-linear-algebra and identifiability inputs are explicitly identified and source-hash audited.

## Covered classes and exclusions

- All common-total-degree-at-least-three frames, with `theta=1/d`.
- Every connected frame with at least two types and all internal degrees `h_i>=2`, including unequal total degrees. Choose `epsilon=1/(4D)`, all active cross weights `epsilon`, and `theta_ii=(1-epsilon b_i)/h_i`, where `b_i` is the cross total.
- No-internal independent lifts of `K_5` minus one edge: weights `1/3` between its degree-three and degree-four groups, and `1/6` inside the degree-four group.

There is **no active-zero-weight claim**, no half-weight boundary claim, and no assertion for all minimum-degree-three frames. In particular, the `N`-lift of `K_(3,12)` has real and modular nullity at least `9N`, so its zero-eigenvalue moment is exponential. Its unequal bipartite side sizes forbid the required certificate.

## Reviewable artifact

- [positive-omission-moments.pdf](positive-omission-moments.pdf): nine-page standalone proof and charged recovery composition.
- [positive-omission-moments.tex](positive-omission-moments.tex): final SHA256 `f6d65ea8a2cc997f8ba137641610a953dde2fbbaa24843bb0ccd251dccda659a`.
- PDF SHA256 `2b6eea2c161e934b753843b9667c864dc504c251f05263f8433bd31b7ecaa593`.

The final nine-page build has no warnings, unresolved references, or overfull boxes. Three independent agents read the complete actual TeX. Two final scope clarifications were checked before binding the final hashes: recovery is explicitly in the uniform simple-factor law, and the internal-degree-at-least-two example explicitly requires at least two types.

## Expanded proofs and audits

- [positive-omission-theorem.md](positive-omission-theorem.md): full moment assembly, induction, examples, and recovery composition.
- [central-positive.md](central-positive.md): actual local-`d_i` covariance, maximal lattices, uniform tilted relative LLT, loop-aware reference concentration, and tail integration. It retains the exact normalizer factor and proves its cancellation.
- [boundary-positive.md](boundary-positive.md): weighted entropy identity, all-positive phase classification, mixed-degree sparse certificate/forcing bounds, and closed dimension induction.
- [full-chain-positive-audit.md](full-chain-positive-audit.md): fresh complete-source audit with exact dependency hashes and the separately charged recovery inputs.
- [audit-positive-boundary.md](audit-positive-boundary.md): additional independent complete master/module audit.
- [audit-tex-positive-chain.md](audit-tex-positive-chain.md), [audit-tex-positive-central.md](audit-tex-positive-central.md), and [audit-tex-positive-boundary.md](audit-tex-positive-boundary.md): fresh whole-TeX audits at the final hash.

The crucial mixed-degree normalization is proved rather than assumed: weighted symmetry, unit rows, and reversibility give equality of the **total physical vertex counts** on the two bipartite sides. This makes the two-space legal/independent reference normalizers coincide. Positive weights on every physical omission force every omission correlation defect to vanish at zero entropy, retaining the finite common-subspace/even-walk phase structure.

## Additional scalar consequence

[scalar-positive.md](scalar-positive.md) and the standalone proof also extend the sharp scalar formula to nonbipartite support in this positive-omission class:

`E_config |ker_Fp(A-lambda I)|=2p^{dim ker_Fp(F-lambda I)}+o(1)`

for each fixed odd prime. For a fixed integer eigenvalue, choosing primes avoiding a nonzero old rank minor gives the inherited real multiplicity with high probability, including exclusion when the quotient has no such eigenvalue. The sharp finite-field constant is not asserted unchanged after simplicity conditioning; the real probability conclusion transfers by its prime-independent positive simplicity probability. No polynomial real failure rate or uniform growing-prime estimate is claimed.

These are mathematical audits, not proof-assistant verification or historical-priority certification. No simulation is used as proof. All new artifacts were written only in this subdirectory.
