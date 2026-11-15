# Fresh adversarial audit of the heterogeneous central estimate

Reviewer: `/root/central_lattice`, 2026-11-15. The candidate was checked directly and a full central proof was independently written in this directory. This is a mathematical source audit, not proof-assistant verification or a priority determination.

**Verdict: PASS for the central theorem in `central-channel.md`.** This verdict alone does not prove the complete bounded moment; it requires the independent zero-phase and boundary modules for that conclusion.

## Exact source scope

```
fbc5df08244c013a5e5102fc3af486047559d0b98319a70ff807b3d118925442  spectral-gap/zero-omission-channel-moment-root.txt
da20fe1cc2196732527922469d12e6a5086979186ee9d7b738866a4acc039a43  spectral-gap/zero-omission-channel-session/central-channel.md
e64d46ae873a6ce568b76784788b1605a38e249c2f8983451372486eff0315a7  spectral-gap/partitioning-rsbm-kernel-session/general-frame-moments/central-frame.md
```

The regular-frame source was read as a comparison. It is not invoked as a theorem with changed hypotheses. The new proof explicitly handles every heterogeneous step.

## Adversarial checks

1. **The alphabets at different slots have different sizes.** The correct real table-space dimension is `(A_i-1)+A_i sum_s(B_i,s-1)`, not the common-width formula. The proof uses a direct null-variance argument under the unrestricted law to prove covariance positive on this entire space. It never imports the common-width covariance matrix.

2. **Legal-star covariance could fail under inactive injections.** Fixing a root and two arbitrary slots still leaves one of the at least three active slots free. Its isomorphism absorbs the sum, making the root and those two labels independent uniform. This establishes every relevant second moment under `P,Q`, regardless of inactive image codimensions or repeated target types.

3. **The normalizer could carry an exponential factor when total degrees differ.** Direct counting gives `K_N E_Q W=product_i(|V_i|/|U_i|)^(n_i)`. The exact `q`-weighted reversibility identity in equation (7) makes this factor exactly one. Equal total degrees, equal total bipartition sizes, and a common alphabet are not used.

4. **Weighted `Q` need not coincide with the random graph and iid roots.** At the ordered-star level its weight is `product_i |U_i|^(-n_i) W`, which equals `product_i |V_i|^(-n_i) W` by the same exact identity. This is precisely the root-label probability times the graph realization probability. Thus the concentration argument applies to the exact measure needed for the moment sum.

5. **Additional inactive-slot lattice periods.** Three active coordinates force one common additive output character at each root. Varying an inactive label and compensating in an active coordinate forces its character function to be the pullback of that same output character. This excludes hidden characters on proper inactive images. Root-specific characters remain independent because a transfer in one active slot surjects onto the output group at that root alone.

6. **Only a necessary congruence might have been established.** The full character calculation and real full rank show that the legal lattice is exactly the kernel of the stated congruence map. A strict finite-index inclusion would yield an additional character, contradicting the classification. Hence the maximal index is exactly `|U_i|^(|V_i|)`, not merely bounded by an unspecified finite constant.

7. **A local central limit theorem might be used beyond its relative-error window.** The proof exponentially tilts at each target mean in a fixed neighborhood. Fourier inversion on its maximal-lattice torus has a uniform spectral gap off zero and a uniform Gaussian expansion near zero. It yields a relative positive estimate at every relevant affine lattice point. Matching covariance then bounds the rate-function difference by a cubic displacement. No absolute-error central-window theorem is extrapolated to linear deviations.

8. **Lattice cosets might be empty at some admissible sizes.** The upper bound needs no compatible-coset mass lower bound. Legal affine lattices lie in the unrestricted affine lattices, and the relative estimate ensures positive unrestricted probabilities near the mean when the legal numerator is nonzero. Incompatible pooled tables simply receive weight zero. Thus all admissible residue classes are covered.

9. **Loops might move the weighted-reference mean by order `N`.** The exact internal self-partner probability is `(d_ii-1)/(n_i d_ii-1)`, yielding only bounded total mean bias in each slot table. A transposition affects at most four physical incidences even when physical owners coincide. Exposing iid roots affects at most `2D` incidences per label. The martingale concentration therefore has the required `exp(-ct^2/N)` scale.

10. **An annulus might retain a polynomial prefactor.** The relative `P/Q` ratio has only a fixed factor and a cubic exponent. On a sufficiently small fixed neighborhood the cubic is dominated by a small quadratic. Integration against the exact weighted-reference subgaussian tail sends the entire annulus beyond `sqrt(N)log N` to zero without a polynomial factor.

11. **Singleton spaces.** The real dimension and lattice factors reduce correctly. If the output is zero-dimensional, all neighbor spaces must be zero-dimensional by the injections, while a nontrivial root law is still allowed. Then `P=Q` for that local table law and the lattice factor is one. Fully deterministic coordinates require no determinant convention beyond the empty determinant being one.

## Auxiliary exact finite check

As an arithmetic check independent of the proof, I enumerated a local system over `F_2` with root alphabet `F_2`, output `F_2^2`, three active output-isomorphism slots of size four, and one inactive slot of size two injected as a line. The on-site map sends the root into that same line. There are exactly 256 unrestricted stars and 64 legal stars. In integral coordinates for the full table lattice, the real rank is 21; all first and second moments agree exactly; the Smith diagonal is seventeen ones followed by four twos, giving index 16, equal to `4^2`. The theorem does not depend on this check.

The central proof is valid for the class stated in the candidate. Its full-table neighborhood still must be connected to the entropy-zero coverage in the master assembly; the next audit checks that connection.
