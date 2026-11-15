# Actual-source audit of the assembled strict-weight recovery theorem

15 November 2026. **PASS: no mathematical defect found.**

The entire source `strict-q-recovery/strict-q-blind-frame-recovery.tex` was read and independently reconstructed. This audit binds exactly SHA-256

`0042ca4067451330f955c9621bc741694369f4743ee4823c70f16f6a87d4c634`.

No edit to that source or to a frozen predecessor was made. This is a mathematical audit, not a historical novelty determination. The theorem retains its model promise: fixed supplied bounds `K,D`, a fixed connected reversible integer true frame, admissible sizes, independent uniform simple factors, and a strict symmetric omission certificate. It makes no boundary-feasible or minimum-degree-only recovery claim.

## Strictness, exact count, and entropy

The certificate is assigned per physical slot: `Σ_j d_ij q_ij=1`, symmetry, and `0<q_ij<1/2` on every active factor. This implies integer total degrees at least three. An internal factor has weight `α_i d_ii/2` in the undirected edge sum and coefficient `1−2q_ii`; absent factors contribute nothing. Both minimum margins used in `C_κ` are positive. No internal slot is required, and internal degree one is included.

The star multinomial assigns the root labels once. Internal opposite categories contribute factorials, internal diagonal categories contribute pairings, and cross categories contribute bijections. The denominators are those of the independent uniform typed configurations. Reversal, internal symmetry, and even internal diagonal entries are exactly the required compatibility conditions. Loops count twice in adjacency and degree, consistently with the local sum equation.

The uniform factorial remainder and type count yield the stated polynomial exponent `B`. Within-neighbor-type symmetrization preserves legal sums and pooled pair laws. The weighted deletion identity cancels every root entropy coefficient by symmetry and normalization; no exchange of slots of different old types occurs. This proves the modular first moment over the vector alphabet, including characteristic two and rare large kernels. Simplicity conditioning gives the stated product of uniform simple factors. Degree-zero internal factors are omitted rather than incorrectly assigned a negative simplicity exponent.

The real one-hot gap was checked separately from the modular calculation. The retained-law KL identity remains finite when marginals have zeros. The global KL sum is bounded by `J_0+2(D−1)E≤C_κ L`, comparing its two coefficients against their respective parts of the loss. The auxiliary variance calculation has a single `B_i≥0` for all omissions. Its test function has range at most `2D²`, since every occupied row has mass `d_i` under both actual and auxiliary laws. Pinsker and weighted Cauchy–Schwarz give

\[
 \sum_i\alpha_i(d_i-2)S_i\leq D^2\sqrt{2D C_\kappa L}.
\]

Reversibility makes this left side at least

\[
 \sum_j\alpha_j d_j(1-\|\rho_j\|_2^2)\geq3\delta.
\]

Squaring therefore gives exactly `γ_Q=9/(2D⁵ C_κ)`. The constant needs no candidate-class mass lower bound or old-block minimum mass. Unused labels contribute zero root mass; occupied labels automatically have the correct total degree by integer legality. Repeated or singular rows of `R` cause no problem. Zero defect forces deterministic old-type labels, and legality becomes the integer relation `QT=TR`.

The macroscopic count uses this real one-hot gap with normalized exponent `nΦ`. Alphabet padding introduces only zero-mass categories and an upper bound on the polynomial remainder. It also covers `r=1`. The finite union over integer candidates includes disconnected quotients and unused labels, so no needed boundary case is discarded.

## Mixed degrees and closure of small defects

Connected balance gives the old-block bound `α_min≥ρ=1/(K D^(K−1))`; it is applied to true blocks and stub pools, not to candidate classes. For a bad vertex set, the exact relation is `2a+b=Σ_(v∈S) d_v`. Together with `b≥2w` this gives `e−s−w≥cs`, with `c=(d_min−2)/2≥1/2`. Thus equal total degree is not used.

Every actual witness is included in the stated overcount: choose `S,W`, choose stubs at `W`, and pair the selected stubs. All stubs at `S` are fixed by the chosen vertices. Invalid typed prescriptions safely contribute zero. The size restriction ensures every internal pairing or cross-bijection denominator is at least `ρn/2`. The factor `(s/w)^w≤exp(s/e)` and the stated conservative `C` cover all `w,e` choices, including `w=0`.

The chosen radius `η≤1/(4eC²)` indeed works uniformly over mixed minimum degrees. Since `c≥1/2`,

\[
 C e^c\eta^c\leq C(1/(4C^2))^c\leq1/2.
\]

Hence the sum beginning at `s=2` is `O(n^(−2c))`. Singleton bad sets are impossible after conditioning on a simple positive-degree graph. The resulting graph event excludes small row supports simultaneously for every field, width, and coefficient matrix, so no union over coefficients is omitted.

For a candidate of defect less than `η`, the minimizing old-type map may be non-surjective. The changed vertices and their neighbors occupy at most `(D+1)|S|<ρn/2`, leaving a clean vertex in every old class. Its integer equation yields each row of `QT=TR`. Consequently `V=Y−JT` is an actual intertwiner with the small changed-row support, and the graph event forces it to vanish. The macroscopic event and this local closure exhaust all candidates. No positive limiting candidate mass is used in either part.

## Blind enumeration and charged bit work

Every accepted nonempty equitable candidate has a nonnegative integer quotient with row totals at most `D`, so the finite enumeration contains all candidates as well as `(J,Q)`. Binary kernels can include false parity solutions; the original integer equation is explicitly checked before acceptance. Standard basis row labels remain distinct over the vector binary alphabet.

On the structural event, every accepted candidate is a planted coarsening. Nonempty classes make the old-type map onto and imply `r≤k`. The true `k`-class candidate is present. At maximum class count `r=k`, the map is a permutation, recovering both the fibers and the integer quotient. This proves the unique-finest conclusion only within the explicitly bounded class family.

The cost estimates and cap are consistent. For each of finitely many candidates, elimination costs `O(n³)` and each enumerated vector costs at most `O(n²)` bit work, including class-size counters and integer verification. Since `B≥1`, the unconditional moment gives base expectation `O(n^(B+2))`, absorbing elimination. The looser untruncated total estimate `O(n^(B+3))` is valid.

The cap uses **the sharper base expectation**: a threshold of `n^(B+4)` base bit operations gives interruption probability `O(n^(−2))`. A capped binary work clock has `O(log n)` bits and costs at most that factor per charged base operation. Thus actual capped work is `O(n^(B+4)log n)⊆O(n^(B+5))`. The larger actual-work bound is not incorrectly substituted for the base expectation in Markov's inequality. Clock space and the current/best labeling fit within the stated `O_K(n²)` bit space. Explicit abstention avoids certifying an unfinished maximum.

## Uniformity and final scope

For fixed `K,D`, the eligible connected integer true frames form a finite family, each determining its positive block proportions. Choosing one strict certificate per qualifying frame supplies a uniform positive margin and hence a uniform entropy rate. The factor simplicity thresholds can also be maximized over this finite family. The blind algorithm never needs those certificates or the hidden frame.

The `K_5` minus an edge example satisfies the certificate exactly: degree-three vertices receive three weights `1/3`, and degree-four vertices receive two weights `1/3` plus two weights `1/6`. Its statement about every positive lift size is consistent with admissibility without an even-size restriction; recovery remains the theorem's asymptotic high-probability assertion. The `K_{3,12}` obstruction stays outside the certificate class and does not conflict with the theorem.

All requested gates pass for the exact source hash above. No further mathematical repair is required by this audit.
