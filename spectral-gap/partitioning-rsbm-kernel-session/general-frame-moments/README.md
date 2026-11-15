# General regular-frame moment packet

**Completed derived proofs, independently audited against the actual sources.** Historical novelty is not certified. The fixed-prime moment limits are not uniform growing-prime estimates, and no polynomial real failure rate is asserted.

## Results

1. **All fixed regular frames.** For a connected reversible nonnegative integer frame of common total degree at least three, fixed positive type proportions, independent internal stub pairings, and independent cross-stub bijections,

   `sup_N E #{Y:AY=YR} < infinity`

   for every fixed prime field, target dimension, and matrix `R`. The bound transfers directly to independent uniform simple factors. Internal degrees zero or one, repeated physical slots, unequal individual type sizes, singular maps, and bipartite mixed-subspace phases are included.

2. **Exact scalar moment.** On connected nonbipartite type support, for each fixed odd prime,

   `E |ker_Fp(A-lambda I)| = 2 p^{dim ker_Fp(Q-lambda I)}+o(1)`

   in the configuration model, along every admissible size sequence. The exact constant is obtained by finite compatible-lattice coset equidistribution under the normalized weighted reference law.

3. **The full original RSBM target.** For every fixed `d1>d2>0`, including `(2,1)`, at every admissible block-size sequence,

   `ker_R(A-(d1-d2)I)=span{sigma}`

   with high probability in the requested independent uniform-simple model. Fix an odd prime avoiding `d2`, use the scalar moment `2p+o(1)` and the deterministic planted modular line, take size limits, and then let fixed primes increase. Direct simplicity conditioning has a positive degree-dependent probability independent of the prime. No outlier gap is required.

This supersedes the parity and low-degree limitations in the earlier parent-session notes; those older artifacts were not edited.

## Main artifact

- [regular-frame-moments.pdf](regular-frame-moments.pdf): eight-page standalone proof of the vector theorem, scalar sharpening, and full RSBM corollary.
- [regular-frame-moments.tex](regular-frame-moments.tex): source, SHA256 `ef7b862873f7501149dcf0525eaa18b8fd6e16ecbfe77fd12746e57b3f26ba42`.
- PDF SHA256 `e276858cf236b00b38ed7f695818d82086b10935f2f80bb7e3db44cad0d6b845`.

The final eight-page build has no warnings, unresolved references, or overfull boxes. The TeX was read in full by three independent agents; the final two formatting-only command fixes were checked against the audited source.

## Expanded proof modules

- [bounded-frame-moment-theorem.md](bounded-frame-moment-theorem.md): complete vector-moment assembly and precise induction class.
- [central-frame.md](central-frame.md): exact physical-slot `P/Q` normalizers, positive identical covariance, maximal lattices, uniform tilted relative LLT across a fixed neighborhood, loop-aware martingale concentration, and cubic-ratio tail integration.
- [boundary-frame.md](boundary-frame.md): repeated-slot entropy zeros, even-walk subspaces, bipartite two-space closure, exact internal-pairing/bijection forcing, correlation-safe kernel-rank bounds, and support-one certificate enumeration.
- [scalar-regular-frame-theorem.md](scalar-regular-frame-theorem.md): full sharp scalar theorem and all-parameter RSBM deduction.
- [scalar-central-equidistribution.md](scalar-central-equidistribution.md): fixed-translation invariance and finite-coset equal mass, independently including the congruence-image calculation.
- [scalar-lattice-rank.md](scalar-lattice-rank.md): independent compatible-lattice rank proof, retaining internal parity and degrees divisible by the prime.

The size vector can be chosen primitive positive integral, since connected reversibility fixes rational proportions. Configuration admissibility includes internal stub parity. The simple-model statements restrict to sizes at which the simple factors exist, as well as that parity condition.

## Source-bound audits

- [full-chain-audit.md](full-chain-audit.md): fresh audit of the complete bounded-moment proof and the charged algorithm composition, with exact dependency hashes.
- [scalar-full-chain-audit.md](scalar-full-chain-audit.md): fresh complete scalar/master/standalone audit at the final source hashes.
- [audit-scalar-central.md](audit-scalar-central.md) and [audit-scalar-boundary.md](audit-scalar-boundary.md): two additional independent complete scalar-assembly audits. Their initial assembly hashes predate only the explicitly recorded lattice-wording clarification; the final-source audits below cover that clarification.
- [audit-tex-central.md](audit-tex-central.md) and [audit-tex-boundary.md](audit-tex-boundary.md): fresh whole-TeX audits at the final hash.

These are mathematical audits, not formal proof-assistant verification or priority determinations. No simulation is used as proof.

## Algorithmic scope

The vector theorem bounds all fixed exponential powers by applying it to block-diagonal repeated targets. The full-chain audit composes it with the existing certified nonsymmetric sparse right-kernel routine and bounded-class one-hot structural theorem: at fixed class and degree bounds, complete candidate listing and recovery of the finest bounded-class planted frame have unconditional expected near-quadratic bit work under the previously established charged algorithm model. This composition depends on those separate certified linear-algebra and identifiability inputs; the moment theorem alone does not provide either.

For the original RSBM, exact rational nullspace elimination already gives polynomial bit-time recovery from the one-dimensional-kernel corollary. The extension does not concern noisy observations, adaptive graph factors, growing frames or fields, total degree two, or unequal total degrees across old types.

All artifacts for this extension were written only in this new directory. No frozen manuscript or other session directory was edited.
