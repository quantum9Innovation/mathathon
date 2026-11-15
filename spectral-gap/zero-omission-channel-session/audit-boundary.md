# Adversarial audit: selected sparse certificates and boundary induction

Reviewer: the fresh `certificate_assembly` adversarial agent, 2026-11-15. This review derives the boundary argument directly, rather than accepting the candidate's conclusion or invoking its resemblance to the regular-frame packet. The proof module and this audit were written only in the new zero-omission directory.

## Verdict and exact source scope

**PASS for the boundary theorem and the selected-certificate repair.** I found no counterexample to Section 5 of the root candidate. The result is conditional only on the phase data explicitly stated in equation (2) of the new module. Its induction use additionally needs the separately proved complete zero-phase classification and bounded central contribution. This audit alone is not a certification of those separate inputs or of an algorithmic corollary.

Sources read in full for this review:

| Source | SHA256 |
|---|---|
| `../zero-omission-channel-moment-root.txt` | `fbc5df08244c013a5e5102fc3af486047559d0b98319a70ff807b3d118925442` |
| `boundary-channel.md` | `2e6add1ce91ac01ca68c0fe6261ce934594c3d1b72283c6a03a5530fe4bc52fc` |
| `../partitioning-rsbm-kernel-session/general-frame-moments/boundary-frame.md` | `cbfd5c6c8372bbbb1a4e2ef01426bfd93225e54cc7842e9efadc7802fe07f5e4` |
| `../partitioning-rsbm-kernel-session/general-frame-moments/bounded-frame-moment-theorem.md` | `6c6da08c6d944e1f9cd76706f08b660fb9be82579549fbae347404e8b99e7e0b` |

The earlier regular-frame packet is used as a comparison source, not as a theorem covering the changed hypotheses. The new module supplies all certificate and counting details for the heterogeneous class.

## Attempts to break the argument

1. **An inactive quotient channel kills a nonzero defect.** This does break the earlier argument that an exterior support neighbor always makes a nonzero contribution. The new argument never uses that assertion. It starts with a unique *active* support incidence, whose quotient channel is an isomorphism. Its nonzero contribution forces some inactive support contribution to be nonzero; that specific edge is selected. A merely existing inactive edge with zero contribution would not suffice, and the proof selects the nonzero one.

2. **The active type graph is disconnected, or root quotient dimensions differ across the two ends of an active edge.** The certificate needs neither connectedness nor equal root dimensions at the edge endpoints. At the exterior endpoint the map from the support endpoint's quotient root space to the exterior quotient output space is an isomorphism. This is the precise fact needed. Different root/output dimensions elsewhere do not alter it.

3. **An outside vertex has no active support incidence but has one or more inactive ones.** Such a vertex is deliberately omitted from the certificate. No counting assertion is made about it. Selecting it unnecessarily would weaken the excess bound and is avoided.

4. **Loops, double edges, and support size one.** Physical stubs are the counted incidences. A selected support loop contributes two to support degree and one to `E`; repeated boundary edges can supply the two required incidences at one outside vertex. The inequality `E-(s+t)>=s/2` remains valid. The sum begins at `s=1`, so a possible one-vertex modular kernel vector in the multigraph model is not discarded.

5. **Inactive support stubs are not saturated, so the old enumeration no longer applies literally.** This is a real detail absent from the proposal's short derivation. Section 5 of the new module explicitly chooses the selected support-stub subset, costing at most `2^(D s)`. Together with the outside-stub choices it costs `2^(D(s+t))=C^s`, since `t<=Ds/2`. The selected pairs have no absent-edge condition. The exact conditional law in the forcing argument therefore still applies.

6. **Rare dense certificates correlate with a large restricted kernel.** The proof uses an explicit conditional-uniform switching coupling, not independence. Cross switches have exactly `m` preimages; internal switches have exactly `m-1`. At most four physical row blocks change per forced pair. A rank difference bound for rectangular operators gives the conditional expectation factor `p^(4 r_out E)`.

7. **A phase representative is not an exact ambient solution.** The constant quotient assignment is exact because the last condition in (2) holds modulo `K_i`. Every lift fiber is empty or an affine translate of the restricted homogeneous kernel. It is not necessary for the ambient constant assignment to solve the system.

8. **Summing small supports loses a polynomial factor or fails at `s=1`.** The derivation keeps `s!t!`, bounds pairings by `(2Ds)^E`, and uses the exact identity in (8). The excess yields `(s/n)^(s/2)`; the remaining factorial ratios sum to `e^(2s)`. The at most `Ds+1` edge counts fit in `(D+1)^s`. Thus (9) has a fixed exponential prefactor, and an explicit term-ratio bound sums it to `O(n^(-1/2))` from `s=1`.

## Assembly conditions checked

The restricted channels remain injective; active restrictions remain isomorphisms. The restricted on-site maps target `K_i`. Hence, if a proper phase strictly lowers total root dimension, the boundary theorem applies at that lower induction level with no quotient injectivity assumption. The all-zero-dimensional base has one assignment. A root-coset neighborhood has at most `epsilon n` defects, and the boundary theorem counts its full solution contribution regardless of its detailed star profiles.

The final theorem must still provide: a complete finite classification of entropy-zero phases, a central bound for the heterogeneous alphabets, and the exact entropy/type formula for the mixed-degree model. Those are not inferred from this boundary result. An expected near-quadratic recovery corollary also needs its separately certified algorithmic and structural inputs.

This is a mathematical audit, not a proof-assistant verification or a claim of historical priority.
