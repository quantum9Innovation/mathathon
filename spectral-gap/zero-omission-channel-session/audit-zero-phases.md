# Fresh adversarial audit: weighted entropy and heterogeneous zero phases

Auditor: `/root/zero_phase`, independent delegated session, 2026-11-15.

**Verdict: PASS for the entropy/zero-phase/induction-closure module.** This verdict does not by itself establish the full bounded-moment theorem or its algorithmic composition; those need the central and sparse-boundary estimates and complete assembly.

## Exact audited sources

```
fbc5df08244c013a5e5102fc3af486047559d0b98319a70ff807b3d118925442  spectral-gap/zero-omission-channel-moment-root.txt
1eb6b7fde716997292b5c32e1f1243a80bc3f39fa6e0dae9d6e5c885e9d59004  spectral-gap/zero-omission-channel-session/zero-phases.md
cbfd5c6c8372bbbb1a4e2ef01426bfd93225e54cc7842e9efadc7802fe07f5e4  spectral-gap/partitioning-rsbm-kernel-session/general-frame-moments/boundary-frame.md
6c6da08c6d944e1f9cd76706f08b660fb9be82579549fbae347404e8b99e7e0b  spectral-gap/partitioning-rsbm-kernel-session/general-frame-moments/bounded-frame-moment-theorem.md
```

The zero-phase proof was independently rederived, not imported by saying that the positive-weight proof is analogous. The original general-frame and positive-omission sources were not edited.

## Adversarial points checked

1. **Only active omissions vanish.** An inactive slot with `q=0` has no `J` equality. The proof never applies the all-omissions lemma to such a slot. Instead it uses precisely three active omissions and then derives the inactive subspace inclusion from an independent retained-sum support calculation.

2. **Why three active slots exist.** Their physical weights sum to one, with each strictly below one half. Two slots cannot supply that budget. Repeated old targets count as distinct physical coordinates, so three active slots need not mean three neighboring old types.

3. **Heterogeneous neighbor alphabets.** The three-coordinate lemma is applied after the maps into the one local output space `U_i`. It does not compare unrelated root vector spaces or identify their subspaces. Equality `L_ij(H_j)=K_i` is asserted only after this common-output transformation, and only on active factors.

4. **Conditional support events.** When every other coordinate is conditioned, its event is positive by one of the three retained-product laws. Each of the remaining pair laws stays equal to its original product law by the corresponding active omission. Thus the fixed-sum three-variable lemma has all its hypotheses; no unsupported conditioning assertion is used.

5. **Uniformity proof rather than support-only proof.** Reflection identifies all three support-difference spaces. Varying a support point in a third coordinate produces translation invariance under the entire difference space. This forces uniform measure on the full coset, not just support containment in a coset.

6. **Every root law is covered.** Symmetry of `q`, reversibility of present incidence counts, and the unit row imply that every type occurs as an active neighbor somewhere. The active support may be disconnected. Connectedness of the active support and any common-subspace/parity-subspace conclusion are not used.

7. **Inactive images.** After root uniformity has been proved globally, each image law is uniform on the image subspace coset. Omitting an active coordinate retains another active uniform `K_i` variable. The support of the independent sum is a coset of `K_i + sum inactive L_ij(H_j)` and must also be a coset of `K_i`. This establishes every inactive inclusion separately. No claim that inactive quotient channels remain injective is made.

8. **Internal factors and the coefficient one half.** The entropy calculation uses `w_ii=alpha_i d_ii/2`, while its pair entropy has two copies of the same root entropy. This gives exactly `w_ii(1-2q_ii) I_ii`; a missing half would invalidate the cancellation. The written calculation retains both copies. Physical internal incidences also remain present in the offset sum.

9. **Unsymmetrized stars.** The exact exponent includes the nonnegative symmetrization loss. A zero of the original exponent must have zero loss because all terms on the resulting right-hand side are nonpositive. Strict concavity makes the original law symmetric, so no asymmetric zero phases are lost.

10. **Converse and uniqueness.** Any active omission is a bijection between legal stars and the freely specified root/retained tuple. This makes the uniform legal-star law independent of which active slot is solved. All active retained tuples are product laws, every pair is independent by choosing a different active omission, and repeated-target symmetry follows from invariance of the legal affine support. Hence the listed conditions are sufficient as well as necessary, and define a unique zero star law.

11. **Closure of a genuinely heterogeneous class.** Restricted channels all map `H_j` into `K_i`; they remain injective. Active ones map onto `K_i`. Restricted `T_i` maps `H_i` into `K_i`. This is the exact same structural class, rather than the common-space class valid only in older positive-weight packets.

12. **Strict descent and base.** A phase with all root subspaces full forces all output subspaces full by an active isomorphism in every row. It is the unique full uniform phase. Every other phase lowers `sum_i dim V_i`. At zero total root dimension the same active-isomorphism condition makes all output dimensions zero, leaving one assignment. No ambient maximum-dimension induction is substituted for this strict sum descent.

13. **No characteristic restrictions.** The entropy weights are real averaging coefficients. The group argument uses additive finite-field structure, and the offset sum has the actual integer incidence multiplicities reduced in the field. The proof divides no field element by a degree or by an omission weight.

14. **Finite phase list.** Every root coset and difference subspace, and each local image difference subspace, is uniquely determined by the marginal law. All spaces are finite. Hence the parametrization produces a finite set of laws and no residual continuum of zero marginals.

## Scope of this verdict

The candidate's Sections 1--3 are valid as stated once “active” is read as positive omission weight rather than merely a present factor. The new module states that convention explicitly. The weaker classification “one common subspace, or two parity-side subspaces” is not asserted for zero-weight factors. The necessary warning about noninjective inactive quotient channels remains essential for the boundary argument.

This is a mathematical source audit, not proof-assistant verification or a historical-priority claim.
