# Independent audit: complete recovery and expected-work composition

Auditor: `/root/zero_phase`, delegated adversarial agent, 2026-11-15.

**Verdict: PASS for the entire recovery composition at the exact source hashes below.** The integrated bounded-moment proof and the complete new composition source were read in full. The actual named zero-weight structural sources, the symmetric full-kernel primitive, and the nonsymmetric right-kernel supplement and audit were also read. No correction to the frozen sources is required by this auditor.

The result is an unconditional expected nearly quadratic **bit-work** theorem for the stated fixed bounded frame family, with expected nearly linear working storage, a complete per-input candidate list, and high-probability recovery of the planted finest partition. It uses the identified existing certified symmetric kernel primitive; this audit makes no claim to have invented a sparse linear-algebra primitive or established historical priority.

## Exact sources read

Paths below are rooted at `spectral-gap/` unless indicated otherwise. SHA256 values were recomputed against the actual files.

```
ec3e96da5add3fb07699ce491927dc166361df6f7fba08448a441a005023b5d5  zero-omission-channel-session/fast-recovery-composition.tex
cd522c3421cd7ebe63ddaa2c103627b5b13a9d51fda03be1555415df8864630c  zero-omission-channel-session/channel-moments.tex

bb6ec1086a2d46f4a1d0b66c69aadc2d120b07157ba8e95f3c08ffb187843473  partitioning-dynamic-session/rsbm-full-kernel/certified-full-kernel.tex
cb893b0def524ba101a4419adf922f0dec60ad3156348c8e91d600887e743df9  partitioning-dynamic-session/rsbm-full-kernel/intertwiner-extension.txt
127b233ee065d4ab158f251f57a33ea771ac101a3fc2e1637fc7e09273bd8c09  regular-frame-fast-algorithm-root-audit.txt

2db029a9d3058122f939ccec2d190172c439d70ab0d4f72579f19bfbc49adc8d  partitioning-frontier-session/nonregular-fibers/strict-q-recovery/zero-omission-addendum.tex
0042ca4067451330f955c9621bc741694369f4743ee4823c70f16f6a87d4c634  partitioning-frontier-session/nonregular-fibers/strict-q-recovery/strict-q-blind-frame-recovery.tex
b0c449292c23e63e09cdb958ba24430cd594acf1533f9882c12999f6197bd017  partitioning-frontier-session/nonregular-fibers/strict-q-recovery/support-audit/mixed-degree-small-support.tex
```

`audit-tex-zero.md` records the separate whole-source audit of `channel-moments.tex`, including its exact configuration/simple-law moment conclusion and fixed powers. That proof is not being replaced here by an entropy-only or scalar-moment assertion.

## 1. Model and candidate scope

The true frame is fixed, has at most supplied `K` classes and maximum degree at most supplied `D`, is connected in its off-diagonal support with the one-type case allowed, and is sampled through independent uniform-simple internal/cross factors. The symmetric certificate allows zero weights and has all weights strictly below one half. Every true total degree is therefore at least three.

Connectedness and positive integer balance fix the type proportions. A path of length at most `K-1` bounds any positive size ratio by `D^(K-1)`, giving the stated lower population bound `rho=1/(K D^(K-1))`. Every present factor pool has linear size uniformly over the bounded frame family.

The search family contains **all** nonnegative integer targets with at most `K` rows and row sums at most `D`. It imposes no candidate symmetry, omission certificate, connectedness, feasibility, or lower class-mass condition. Every actual nonempty equitable partition of an undirected graph of maximum degree `D` has such a target. In particular nonsymmetric balanced targets and unequal candidate classes are not lost. The integer acceptance checks, rather than an unproved feasibility filter, decide which candidates survive.

## 2. The zero-weight one-hot gap

I checked the new source's reconstruction against the actual zero-omission addendum, not only its theorem statement.

Repeated-target symmetrization preserves legality and root/pair laws and increases entropy. After symmetrization, the weighted lossless-omission identity has positive mutual-information coefficients on **all** present factors, including zero-weight factors. The divergence from the retained root/neighbor product law is exactly `kappa_it=J_it+sum_(s!=t) I(X;Z_s)`. Its omission-weighted average is

`A_q=J_q+2 sum_(i<=j) w_ij(1-q_ij)I_ij <= (2/c)L`.

The factor two is correct internally as well as across cross factors. No reciprocal of an omission weight is used.

For each occupied root value, the candidate row has total mass equal to the true local degree by the integer one-hot equation. The product reference uses the same root marginal, so this remains true under that reference even when other candidate rows are unused. Both nonnegative vectors in the squared-distance statistic have total mass `d_i`, giving the actual bound `0<=f_it<=2D^2`. Its actual expectation is `V_it`, and its independent expectation is `S_i-V_it+B_i`. Range total variation plus Pinsker therefore gives precisely the displayed `sqrt(2) D^2 sqrt(kappa_it)` comparison, including boundary laws.

Averaging with the omission weights gives `sum_t q_it Delta_it>=c S_i`, because `1-2q_it>=c` and `B_i>=0`. Weighted Cauchy--Schwarz has total weight one. Detailed balance gives `sum_i alpha_i S_i=sum_j alpha_j d_j(1-||rho_j||_2^2)>=3 delta`. The stated result follows with the exact constant

`gamma=9c^3/(4D^4)`.

The initial symmetrization extends it to every original star law. This is a quantitative gap for real integer one-hot laws; it is not confused with the subspace-valued zero phases of the finite-field moment proof.

The exact ordered-star factorial formula applies to these one-hot profiles, with fixed finite alphabets, a polynomial number of profiles, and a uniform polynomial remainder. It therefore gives the exponential expected count away from every old-type point map. Direct bounded-cost simplicity conditioning gives that same estimate under the actual simple-factor law. Unused labels and arbitrarily small candidate classes cause no loss of the gap or of this count.

## 3. Small supports and clean closure

The source uses the ordinary total-support certificate for `AV=VR`, rather than the active-edge certificate needed by heterogeneous quotient phases in the moment proof. This distinction is correct: at an outside zero row with exactly one support incidence, the coefficient in `AV` is exactly one and the row cannot vanish, in every field and every width.

The all-support-stub witness obeys `E-s-t>=(d_min-2)s/2`, including loops and multiplicities in the unconditioned model. The linear pool-size lower bound gives at most a fixed constant over `n` per prescribed pair for the chosen small support range. Support/exterior vertices, exterior stubs, and pairings are counted by the displayed upper bound; there is no omitted choice of support stubs because **all** support stubs are fixed here. The factorial sums and fixed degree bound give a summable `C^s(s/n)^((d_min-2)s/2)` upper bound. In a simple graph a singleton cannot be bad, so the sum begins at two and yields `O(n^(-(d_min-2)))`. Conditioning costs only the established reciprocal simplicity probability.

The resulting graph event is simultaneous over every field, width, and target. No union over coefficients is needed.

On the macroscopic and support good event, each accepted indicator differs from a nearest old-type point map on fewer than `eta n` rows. The closed neighborhood of those changes has fewer than `(D+1)eta n<n_i` vertices, leaving a clean vertex in **every** old type. Its exact integer equation proves `QT=TR` row by row, even when the point map is non-surjective. Subtracting gives the row-sparse equation over the rationals, to which the simultaneous support event applies. Hence the accepted indicator equals that point map exactly. This proves that every accepted equitable partition is a compatible coarsening, without a candidate-class mass assumption.

Taking the finite union of the macroscopic expectation bound and the single support event gives the stated high-probability structural conclusion. The proof neither assumes this good event for runtime nor uses a real spectral gap.

## 4. Raw vector moment at the correct prime and law

The new moment theorem applies at `p=3`, in every fixed vector dimension and for every target matrix, including reductions of infeasible or nonsymmetric integer candidates. The omission certificate is required only of the **true** random frame. Its simple-model conclusion is a direct expectation bound obtained by simplicity conditioning.

Thus it supplies exactly `sup_n E_simple p^(h_R(A))<infinity` for every target in the fixed finite search family, for the same odd prime used by the primitive. It supplies this raw count including deterministic planted vectors and rare exceptional graphs. No binary-to-odd-prime inference, scalar-to-vector inference, division by planted kernel size, or qualitative-contiguity transfer is used.

## 5. Complete certified right kernels

The actual symmetric primitive is per matrix, returns the entire base-field kernel, and has a deterministic rank certificate. Its order/corank/workspace parameters remain valid for singular exceptional matrices. I checked its theorem/interface, unconditional shifted-recurrence rank lower bound, capped trial/retry work, canonical base-field descent, exact verification, and extension-field bit-cost passages. The source's already audited primary preconditioning/Wiedemann ingredients remain identified dependencies; the composition does not claim a new primitive.

Column vectorization gives exactly `K_R=I_r tensor A-R^T tensor I_n`. The transpose on `R` is correct. Both `K_R` and its transpose have linear sparse product cost at fixed `K,D`. The symmetric block matrix has order `2m`, nonzero count `2w`, rank twice the rank of `K_R`, and corank `2h_R`. Applying the **per-input** primitive therefore gives conditional expected work `soft-O(n^2(h_R+1))`, without needing a moment for that doubled matrix.

Bottom projections of a complete doubled kernel basis span the full right kernel: every `(0,v)` with `K_R v=0` lies in that full space. The source selects independent projected columns before pivot normalization; it does not assume that arbitrary first projected columns are independent. The primitive has already descended to the base field. Projection, selection, and normalization cost `O(mh^2+h^3)`, bounded by `O(m^2(h+1))` because `h<=m`. Their storage remains within the stated kernel bound.

The compact final right certificate is sound. Regenerating the true shortest shifted finite recurrence gives `ell<=rank S_R=2 rank K_R` on **every** draw. Verified residual and pivot identity give the reverse rank inequality after requiring `ell=2(m-h)`. Hence the source's integer rank chain proves completeness. There is no division by two inside the field, and full-rank/zero-rank boundary cases are covered. Verification uses only linear-many sparse products, quadratic recurrence work, and residual/pivot checks, all within `soft-O(n^2)` bit work. No dense fallback or isotropic Gram-kernel identity is used.

## 6. Complete enumeration and its exact charge

Only the projected `h`-dimensional right kernel is enumerated. The unused left kernel is never enumerated. A base-`p` odometer/Gray update changes `O_p(p^h)` digits over the whole traversal, each requiring one basis-column update of length `m=O(n)`. This proves `O_p(n p^h)` total generation work, including the `h=0` case. A fresh basis multiplication per state and an unbounded `h p^h` expectation are avoided.

Each matrix must have exactly one residue one and all others zero per row; a modular row-sum test alone is not used. Nonempty classes are checked, then the original integer identity is verified with bounded-degree neighbor counts. This costs only `soft-O_(K,D)(n)` bit work per state, including counters. Every genuine one-hot integer candidate reduces to a vector in this kernel and is therefore listed; every modular artifact fails the integer test. The enumeration is complete on every input, even a graph with extra real eigenspaces or exceptionally large modular corank.

The primitive terminates almost surely per fixed input; a finite number of targets and a finite deterministic enumeration preserve almost sure completion. The claimed maximum is selected after all enumerations finish, so an unfinished search is never used as a certificate.

## 7. Unconditional expectation, memory, output, and recovery

For each fixed graph and target the complete conditional expected bit charge is exactly of the form

`soft-O_(K,D)(n^2(h_R+1)+n p^(h_R))`.

It includes the primitive's bad trials and retries, field arithmetic and construction, certificates, descent, right projection, enumeration, and integer checks. The corresponding working storage is `soft-O(n(h_R+1))`; retry bookkeeping is harmless within this bound in expectation. The raw moment and `h_R+1<=p^(h_R)` therefore give unconditional `soft-O(n^2)` expected work and `soft-O(n)` expected working storage. These expectations are taken over all graphs and all algorithmic randomness, without conditioning on structural recovery. Rare high-corank graphs are fully charged.

The target family is finite, so linearity of expectation preserves all bounds without independence assumptions between runs. Reusing workspace or bounding its maximum by the finite sum gives the expected storage claim. At most `p^(h_R)` candidates can be accepted for a target, and each has `O_(K)(n)` output bits, giving `O(n)` expected total output over the finite family. Streaming or retaining just the best partition avoids accumulating the full output in working memory.

The true planted indicator is always present in the list. On the structural good event every accepted nonempty indicator is an onto compatible coarsening and has at most `k` classes. The true indicator has `k`, so a completed maximum has exactly `k` and its point map is a permutation. Thus it recovers the partition, quotient, and unknown class count up to names.

Finally, at fixed `K,D` there are finitely many qualifying connected integer frames, each fixing its positive proportions. Choose one strict certificate per qualifying frame. The finite minimum of their positive `c` values and finite maxima of their moment/support/simplicity constants justify the claimed family uniformity, without requiring the algorithm to know any certificate.

The complete new main-plus-composition chain therefore passes at the hashes above. This is a mathematical source audit, not proof-assistant verification or a practical sparse-memory benchmark.
