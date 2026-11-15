# Fresh audit of the complete standalone TeX

**Verdict: PASS for mathematical fidelity and the stated theorem scope. No mathematical error or missing proof dependency was found in the actual standalone TeX.**

Audit time: 2026-11-15, approximately 11:52–11:55 UTC. The entire source was read from the document preamble through `end{document}`. This was not an audit only of the scalar delta or of the Markdown notes. No TeX or theorem source was edited by this reviewer.

## Exact bound artifacts

| Artifact | SHA-256 |
| --- | --- |
| `regular-frame-moments.tex` | `ef7b862873f7501149dcf0525eaa18b8fd6e16ecbfe77fd12746e57b3f26ba42` |
| `regular-frame-moments.pdf` | `e276858cf236b00b38ed7f695818d82086b10935f2f80bb7e3db44cad0d6b845` |
| Current scalar Markdown assembly | `50bf9df8032bab7817a0239e5fe850ff0a0b4640a3a684c0206d94fae755b80d` |

The full initial TeX read had SHA-256 `a14526c519cc78ae3f69ccd1c6b79745eaa3d49ddcb369ee8bab305104bdf09d`. It contained two purely typographical missing-backslash errors: literal `quad` in the cross-weight display and literal `qquad` in the concentration display. The author corrected those two macros. An exact in-memory comparison confirmed that the final source differs from the fully read initial source **only in those two expected backslash insertions**. The final TeX and PDF hashes were then checked directly. The current build log contains no LaTeX warnings, undefined references, errors, or overfull boxes.

## 1. Statements and model

The standalone statements agree with the proved frame model: a fixed connected reversible integer degree frame, positive integer size multipliers, common total degree at least three, independent internal stub pairings and cross-stub bijections, all admissible internal-pairing residues, and adjacency loops counted twice.

The vector theorem is for each fixed field and target dimension, with a constant uniform over the finite family of target matrices. The optional simple-model bound is restricted to sizes where the simple factors exist; at all sufficiently large admissible sizes the fixed-degree simplicity probability is bounded below. This qualification removes the small-size existence issue.

The sharp scalar theorem correctly restricts to odd primes and connected nonbipartite old support. The exact `2p^t+o(1)` moment is stated for the unconditioned configuration law only. The RSBM corollary is for every fixed `d1>d2>0`, every admissible block-size sequence, and the original independent uniform-simple random factors. No arbitrary deterministic-cross extension is claimed by this new all-parameter result.

## 2. Ordered-star count, entropy identity, and phases

The TeX retains the exact cross factorial and internal double-factorial weights, including internal symmetry and even pooled diagonal. The root multinomial appears exactly once. Its type exponent has the correct one-half factor for internal pools.

The repeated-slot symmetrization only permutes slots with the same target type, so it preserves pooled pairings and the local equation. The omitted-slot equation has coefficient one over every characteristic. Averaging over omissions gives precisely the `(d-2)/d` weighted mutual-information term and the `1/d` conditional-total-correlation term. The root entropy cancellation uses the actual reversibility weights and common degree.

The finite-group lemma and its conditional application preserve all zero phases. Uniform affine cosets are common on even-walk components. An internal factor is correctly treated as a self-incidence; it forces the connected old support into the one-space, nonbipartite induction class. The bipartite two-space class, including zero-dimensional sides, is explicitly retained and is closed under restriction.

The TeX's compressed proof still states the needed sufficiency and uniqueness of the zero star laws. It does not replace the boundary or prefactor estimate by an entropy-only inference.

## 3. Exact normalizer and local-limit proof

Both exact identities are present: `E Z=K_N E_P W` and `K_N E_Q0 W=1`. For a common alphabet the normalizer is immediate. For two side alphabets, the TeX explicitly establishes equality of total physical side sizes from regularity and reversibility before invoking it. Unequal individual type sizes therefore do not create an exponential normalizer error.

The full physical-slot covariance is the correct positive operator on the common-row-margin space. It agrees under legal and unrestricted laws because any two neighbor slots are independent uniform conditional on the root when degree is at least three. Repeated target types do not affect this calculation.

The maximal legal lattice is characterized completely by the root-row group congruences; the character argument includes every period. The unrestricted and legal laws use the same Euclidean span, and their affine-lattice containment is explained. The compact-tilt Fourier argument supplies a **relative** local estimate with the lattice covolume, positive covariance determinant, positive local probabilities, and uniform error. This is sufficient for the fixed-neighborhood cubic likelihood comparison and its sharper logarithmic-window ratio. It is not merely an absolute-error CLT.

The weighted reference law is exactly configuration plus iid root labels. Stub-permutation transpositions and label changes have the stated bounded effects, including loops. The exposure martingale and finite-dimensional union bound give the subgaussian tail, with only a bounded loop shift in centering. The cubic exponent is integrated against this exact normalized law after shrinking the neighborhood. The TeX correctly retains the no-polynomial-loss step that is needed for a bounded moment.

## 4. Boundary count and vector induction

All support stubs are prescribed in the certificate, so no hidden absent-edge conditioning is introduced. Multiplicity is retained in the exterior cancellation test; loops count once as internal edges and twice in degree. The excess lower bound is correct, and singleton support is not incorrectly excluded.

The cross image-swap and internal two-edge-switch procedures have the correct uniform preimage counts and preserve earlier prescriptions. Their coupled output is the exact conditional factor law. The changed-row rank charge bounds the conditional homogeneous kernel moment, so the rare certificate is not assumed independent of that kernel.

The certificate enumeration has the correct factorial placement factors and power `(s/N)^{(d-2)s/2}`. The retained factor `ds` covers the finite edge-count choices. Choosing a sufficiently small defect neighborhood makes the sum geometric from `s=1`. Proper phases reduce the correct induction dimension, and the finite phase family together with the central neighborhood covers every entropy zero. The compact complement therefore has strictly negative entropy and a vanishing total contribution.

The finite number of on-site maps and the finite number of small admissible sizes justify the final uniform supremum. Direct bounded-cost simplicity conditioning, rather than qualitative contiguity applied to an unbounded moment, is the correct final step.

## 5. Scalar compatible translations and rank

The exact compatible lattice includes internal parity. A fixed compatible translation preserves the unrestricted full-table affine lattice. In the logarithmic window its local probability ratio tends to one uniformly. Cross factorial powers cancel by zero pool-total shift; internal double-factorial powers cancel by one half of the full symmetric pool-total shift, with even diagonal shifts preserved. Entries stay positive of order `N` under fixed shifts.

The concentration estimate makes the fixed-width outer shells negligible. Finite coset translations therefore equidistribute the actual compatible integer quotient, yielding the exact central coefficient `I_*/J_*`. This avoids any unchecked pooled Gaussian determinant or reduction-modulo-prime saturation statement.

The scalar annihilator proof uses actual integer directions. Cross interactions force affine coefficient functions with alternating slopes. Twice the symmetric internal interaction preserves even diagonal and forces constants in odd characteristic; an odd cross cycle does the same for alternating slopes. The free-root-margin construction in the TeX uses twice arbitrary integer margins, cross anchor tables, even internal diagonal tables, and physical-slot decomposition. This is valid even when a degree multiplicity or a type-size multiplier is divisible by `p`. The residual condition is correctly `(Q-lambda I)c=0`, and the congruence-image rank is exactly `kp-t`.

The exact central coefficient is consequently `p^t`. The scalar field has only the zero and full subspaces, so the only other phases are the `p^t` exact old-type point maps. Their disjoint small neighborhoods contribute `p^t+o(1)` by the audited boundary estimate, while the compact complement vanishes. This proves the exact scalar moment as printed.

## 6. RSBM corollary and algorithmic limits

For the RSBM degree matrix at `lambda=d1-d2`, every fixed odd prime not dividing `d2` has old kernel dimension one. The modular planted line is deterministic. The stronger printed bound

`limsup P_config(real nullity>=2)<=1/(p-1)`

is valid: subtract the planted `p` vectors from the moment `2p+o(1)` and divide by `p^2-p`. Real excess nullity forces modular excess by vanishing integer minors. Sending fixed admissible primes to infinity is in the correct order. The simplicity probability is independent of the chosen prime, so direct conditioning transfers the result to the independent uniform-simple factors at all admissible sizes, including `(2,1)` and odd block size with even internal degree.

Exact rational kernel elimination is polynomial in bit complexity by the stated fixed-degree minor bound. The note correctly asserts no outlier requirement and no polynomial real simplicity failure rate. The near-quadratic charged-algorithm paragraph remains explicitly conditional on a separately certified primitive and identifiability theorem; it does not claim those are supplied by the moment theorem itself.

## Final verdict

**PASS for the final TeX/PDF hashes above.** The only new issues found during TeX conversion were the two corrected spacing macros. No change in mathematical claim or proof logic was needed. Historical novelty, a growing-prime estimate, and a polynomial real failure rate are outside this audit.
