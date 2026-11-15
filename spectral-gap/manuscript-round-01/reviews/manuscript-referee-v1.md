# Mathematical referee report, frozen manuscript v1

Date: November 14, 2026 Pacific

Task: independent audit of the assembled manuscript and five-page reading guide

Reviewer: manuscript-referee

Recipient and integrator: root

## Decision

**Accept the main mathematical results. Request the five minor repairs below before accepting all explanatory prose literally.** I found no unsupported inference in the proof chain for the optimal mixed-product prefactor, exact cubic threshold, parity-dependent critical limits, relative hyperbolic window, or square-root correction. None of the findings below changes those results.

The earliest boundary blemish is the unconditional display of the seed `mu_1 = r/(n-r)` at full depletion. The first false statement in the explanatory graph chain under the preceding multigraph context is the vertex-only definition of non-backtracking. Both have local repairs. There is no need to weaken any main theorem.

This decision applies only to frozen v1. Later edits require a delta review.

## Inputs, independence, and scope

I read every manuscript section, the main file, the complete guide, and the figure-building source from `frozen-manuscript-v1`. All 16 manifest entries match their SHA-256 values. The manifest hash is recorded below. I did not read prior reviews or use their conclusions as evidence.

During this audit the integrator named planned editorial corrections and supplied the location of the published Collins and Nagatsu PDF. I checked the affected frozen-v1 passages and the primary pages myself. This disclosure does not extend the decision to the planned corrections.

The audit reconstructs the mathematics from the supplied source. It does not certify literature-wide novelty or every later step in the cited graph proofs. The manuscript appropriately distinguishes its probability estimate from graph enumeration and tangle control.

## Findings requiring local repair

### MRF-V1-01, full depletion needs only the empty product

Location: `manuscript/sections/mixed.tex`, line 60. The guide repeats the unqualified seed at line 56.

The allowed endpoint `r=n` leaves no symbols. Only `mu_0=1` exists there, while the displayed formula for `mu_1` has zero denominator. The recurrence itself has an empty index range, and the supersolution already treats `h=0` separately. Thus this is an endpoint explanation defect, not a gap in the bound.

Minimal repair: say that `mu_1=r/(n-r)` is used only when `r<n`, and that full depletion uses the empty product alone. The guide can simply attach `r<N` to its first-moment seed.

Status in frozen v1: open. Main theorem impact: none.

### MRF-V1-02, regular-graph illustration requires degree at least two

Location: `manuscript/sections/spectral.tex`, lines 52 to 56.

The regular-graph paragraph does not assume `d>=2`. At `d=1`, a single edge has adjacency eigenvalues `1,-1` but a zero non-backtracking matrix. Its adjacency eigenvalues are outside the displayed degenerate interval, yet it has no non-backtracking root outside the radius-zero circle. At `d=0`, the displayed radius is not real.

Minimal repair: begin the regular-graph illustration with `d>=2`. The later biregular calculation already has the corresponding degree assumption.

Status in frozen v1: open. Main theorem impact: none.

### MRF-V1-03, an odd partition need not contain a triple

Location: `guide/reading-guide.tex`, line 135, page 4.

The sentence claiming that odd orders need at least one triple is false for the full partition sum. A single size-five block contributes `96N` to `Q_5` and contains no triple. The intended statement about the leading term is correct.

Minimal repair: replace the sentence with: “The leading odd contribution uses one triple and otherwise pairs.”

Status in frozen v1: open. Main theorem impact: none.

### MRF-V1-04, distinguish pair depletion from a positive fraction of labels

Location: `guide/reading-guide.tex`, line 144, page 4.

The claim that triples consume a noticeable fraction of the available pair choices can suggest a positive limiting fraction of pairs or labels being used. In the square-root proof, `s/m` tends to zero. What remains nonzero is the logarithmic loss in the number of available pairings, because `s^2/(2m)` tends to `d`.

Minimal repair: say that triples use a vanishing fraction of labels, but their cumulative effect on the number of pairings remains nonzero. This explains the mechanism more accurately than a resource-exhaustion interpretation.

Status in frozen v1: open. Main theorem impact: none.

### MRF-V1-05, define non-backtracking by edge reversal in a multigraph

Location: `manuscript/sections/spectral.tex`, line 34.

The preceding configuration model can have parallel edges. In that setting, a step from `u` to `v` along one edge followed by a step from `v` to `u` along a different parallel edge is non-backtracking. The displayed condition `y!=u` excludes it. That condition is correct for a simple graph.

Minimal repair: define the entry from oriented edge `e` to oriented edge `f` by matching the head of `e` to the tail of `f` and requiring `f` to differ from the reverse of `e`. Then state the vertex-only formula as the simple-graph specialization.

Status in frozen v1: open. Main theorem impact: none.

## Reconstruction of the main proof chain

### 1. Depleted recurrence and mixed products

The conditioning event fixes exactly `r` compatible arrows and has probability `1/(n)_r`. Every consistent centered singleton avoids all requested rows and columns of its color, so none is accidentally exposed. The remaining row sum for `Z=nU-1` is exactly `r`. The used-column identity removes one or two factors with the stated coefficients, giving the displayed recurrence with a positive denominator for every nonempty remaining moment.

The quadratic identity for `beta` is exact. With `r+j<=a`, the recurrence is dominated by the geometric supersolution. The affine coefficient calculation is valid for every allowed multiplicity. In particular, the bound for an odd repeated exponent uses `p>=3`, while the even case uses `p>=2`. The coefficient `d_e` is nonnegative for `n>=2`.

The cross-color factorial correction is handled correctly. The inequality `F_n(u)F_n(v)<=F_n(u+v)` follows by matching the second set of factors to later, larger factors in the product for `F_n(u+v)`. There is no constant raised to the number of colors. Under `a^2<=n`, the logarithmic correction is at most `1/2`. The compatible, entirely uncentered family at `n=a^2` approaches `sqrt(e)` and proves optimality for exactly the stated class of mixed products.

### 2. Cubic threshold and optimal lower constant

Rescaling the depleted recurrence at `r=0` gives the stated moment recurrence. Substitution of both parity-dependent leading terms gives the displayed error recurrences, including the special initialization at orders two and three.

Dropping the nonnegative term from the even recurrence is legitimate. Summing its forcing polynomial gives the stated `C_e(m)`. The odd induction polynomial satisfies its displayed first-order identity. The comparisons with `2k^3/27` hold at the smallest allowed orders as well as asymptotically.

For the upper bound, the coefficient sums are bounded by `1+3j^2/N` when `2k<=N`. The product bound then proves the required exponential estimate. Every sequence with bounded `k^3/N` eventually satisfies this domain restriction. Both equivalences therefore have the stated quantifiers, including bounded orders. The sharpness argument uses growing odd orders with `k^3/N` tending to zero, where the critical-approximation remainder is smaller than the cubic term by a factor of order `1/k`.

### 3. Critical approximation and parity

The auxiliary seeds are harmless because both coefficients of `o_0` vanish at the first step. Differentiating the proposed hyperbolic functions gives exactly the two comparison equations. The power series control the apparent singularity at zero.

The local even residual contains the potentially larger term of size `m^4/N^2`. The assumption `m^3/N<=T` reduces this to `O_T(m/N)`. For the odd residual, the coefficient after substituting the comparison equation is exactly `-3/[m(2m+1)]`, whose product with `E_m-O_m=O_T(m^3/N)` has the same required size. The positivity-based stability product is bounded on a fixed cubic window, and summing the residuals gives `O_T(M^2/N)`.

The limiting statement is correctly made separately along the two parities. For positive critical parameter the limits differ. An alternating sequence is not silently assigned a common limit. At parameter zero both limits equal one.

### 4. Exact availability normalization

Let `S` be the labels in nonpair blocks and let `V` denote their product of coefficient weights before the factors of `x` are inserted. At even order, the pair count is `m-S/2`, and direct cancellation yields

`Q` contribution divided by `Lcal = (m)_(S/2) (2/N)^(S/2) V`.

Since `x^2=2m/N`, this is precisely the even availability formula.

At odd order, set `t=(S-3)/2`. The pair count is `m-1-t`, and cancellation yields

`Q` contribution divided by `Lcal = [3/(2N)] (m-1)_t (2/N)^t V`.

Using `lambda=(2/3)N x^3` gives exactly the displayed `1/lambda` factor and the odd availability factor. There is no missing factor of `m`, `N`, or three. Zero extension removes every pattern with too many consumed pairs.

Also `R_k=D_k Q_k/Lcal_k` is correct for both parities. The normalization cannot be interchanged with `Q_k/Lcal_k`, since `D_k` contributes the positive `d/2` term at square-root scale.

### 5. Finite relative window

Removing availability factors is valid because the partition coefficients are nonnegative. The even and odd parity projections give `exp(A_*) cosh(B_*)` and `exp(A_*) sinh(B_*)/lambda` respectively. The geometric bound controls the sum of all extra block weights, not just a fixed list of block sizes.

For the lower bound, the falling-factorial loss remains valid beyond its support because the left side is defined as zero and the claimed lower bound is nonpositive. The parity-restricted Poisson second moments give the stated even and odd losses. In particular, the odd numerator is `9 lambda^2 - 3 lambda coth(lambda) + 3`. Restoring `D_k>=1` and treating a negative lower-envelope factor by positivity completes the bound. The logarithmic inequality holds throughout the advertised smaller range.

### 6. Square-root correction, tails, and convergence in mean

With `k^2/N` tending to positive `d`, one has `lambda` tending to infinity, `lambda_4` tending to `3d/4`, and

`sum_(j>=5) lambda_j <= N x^5/(1-x) = O(N^(-1/4))`.

Thus the probability of any block of size at least five tends to zero. This is the required aggregate tail control. A bound for each fixed size separately would not suffice, but the manuscript does not make that mistake.

On the complement of this event, the availability argument is `3C_3/2+2C_4+O(1)`. Concentration of `C_3`, tightness of `C_4`, and `lambda^2/m -> 8d/9` give `s^2/(2m)->d`, `s/m->0`, and `s^3/m^2->0`. The logarithmic falling-factorial expansions therefore give the limit `exp(-d)`.

This convergence need only hold after multiplication by the appropriate parity indicator. The factors are bounded by one, so the resulting error converges to zero in mean. The Poisson parity probabilities both tend to `1/2`. No independence of parity and availability is assumed or needed. The odd normalization cancels the same `lambda` appearing in `sinh(lambda)/lambda`.

The three logarithmic contributions are `3d/4`, `-d`, and `d/2`, giving `d/4`. This applies along either parity and hence along sequences mixing them.

### 7. Compactness gives the advertised uniformity

If uniform convergence on `k<=C sqrt(N)` failed, an offending sequence would have a subsequence on which `k^2/N` converges in `[0,C^2]`. At a positive limit the square-root result applies. At zero the finite relative window applies, and the extra correction also tends to one. The relevant domain `k<=N/4` holds eventually in the zero-limit case. Both alternatives contradict a fixed positive error. This proves uniformity without asserting an unproved rate.

## Primary-source checks

- Bordenave's [arXiv version 4](https://arxiv.org/pdf/1502.04482v4) contains the stated Proposition 28 and equation (62), with the displayed conditioning on images and preimages. The two examples refute that displayed intermediate assertion. They do not refute the proposition. The manuscript preserves this distinction.
- The [published Collins and Nagatsu article](https://doi.org/10.5802/alco.480) was checked in the supplied primary PDF, printed pages 471 to 473. Proposition 3.3 contains the leading terms, equation (16) is the recurrence, and the normalized error recurrences are present in its proof. Remark 3.4 asks about the optimal cubic scale. Remark 3.5 identifies the Kummer function. The manuscript's attribution is accurate. The primary PDF has SHA-256 `c5b124655a495c03017b3866542ebd1f3289921cc4ed053244cc885cb8db017e`.
- Brito, Dumitriu and Harris [preprint version 6](https://arxiv.org/pdf/1804.07808v6) identifies the half-edge block as a permutation matrix of size `L` and derives Lemma 7 from Proposition 28. The [published article](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/spectral-gap-in-random-bipartite-biregular-graphs-and-applications/FF0544B9780460143733B7A5317D6CC1) numbers that statement Lemma 5.6. The graph application in the manuscript has the correct dimension and centering.
- The [Laguerre generating identity](https://dlmf.nist.gov/18.12.E13), with parameter `-N-1` and argument `-N`, gives the stated generating function. The [finite polynomial formula](https://dlmf.nist.gov/18.5.E12) supports this formal interpretation even at the negative integral parameter. The manuscript separately derives the identity and does not depend on an unjustified orthogonality domain.

## Executed checks and limits

The owned supporting program `manuscript-referee-checks.py` produced `manuscript-referee-checks.json`. It verified all manifest entries, 1,770 exact depleted-moment cases, 221 exact partition totals, 1,833 individual availability contributions, and 4,950 exact cubic lower bounds. It also checked 2,401 finite numerical upper bounds and enumerated both four-symbol conditioning examples. Numerical corrected ratios at increasing matrix sizes approach one along both parities. These finite checks corroborate normalization and examples. They are not the basis for the general proof decision.

Rebuilding the exact frozen sources produced a 20-page manuscript and a five-page guide. The final manuscript pass had no reported cross-reference or overfull-box warnings. I inspected all five rendered guide pages and the relevant printed primary-source pages. I read the full manuscript source and extracted text, but this report is not a page-by-page visual production audit of the manuscript.

## Explanation-reader assessment

The guide gives a usable route from two-cell cancellation to compatible conditioning, the cubic transition, partition weights, and the graph application. Its distinction between requested cells and a realized permutation is helpful. The source-proof issue is scoped correctly. The graph page explicitly leaves counting and tangles outside the proved claim.

The five guide pages render legibly with no clipping in the inspected images. The page-four partition table adds a concrete normalization check. The two substantive reader hazards are MRF-V1-03 and MRF-V1-04. Once repaired, the mechanism will correctly communicate that a vanishing label fraction can still cause a finite multiplicative depletion. The bounded literature-search qualification should remain.

## Reviewed hashes

Manifest SHA-256: `0874feff7a40e382f699f05eb65b14d7f972762d2747c8222d42943b1a5e1dfd`

| Frozen-v1 path | SHA-256 |
| --- | --- |
| `manuscript/main.tex` | `31a4198b0e78ea598357aa6c2b9e4db93e09cc9815ee5c45ac08461dbd4ab9de` |
| `manuscript/sections/introduction.tex` | `0b9f98891c319b437b42572007887ca69b32e0d2155e6063c609e3c352858c97` |
| `manuscript/sections/mixed.tex` | `d0c89f37b6753437c96a5c830ac8df3ead54640c125558605829843fd9eafb84` |
| `manuscript/sections/threshold.tex` | `5c97925a3df35fc94f48eb360ddebdf4abb9d9747cb98fc94b6d7b579b8e09f7` |
| `manuscript/sections/critical.tex` | `1b0efa9d0a536c12e479020c57171b8af4ef27431cb067b3a7c3966eaea95a93` |
| `manuscript/sections/extensions.tex` | `5b18cfa092ff105a44ec3cc394e09d204a1267663d14383de3d354eacb83a668` |
| `manuscript/sections/spectral.tex` | `344fc60866115f2510836e9eb4ec63503e31770f7630248494da2bc167fbd9b7` |
| `manuscript/sections/conditioning.tex` | `0b8143ec1f5c80454d62f16d1c466bcaf597132e46c4b8b66cd65a9a87bd66ad` |
| `manuscript/sections/discussion.tex` | `1632949b923c0678b260cec4be373c2be2008e910d97cd458ef4101dfdc3e6a1` |
| `guide/reading-guide.tex` | `a0a047b7c73744ddbc8010347be0e550b3e5cda8636ee7399206f727b26cebd1` |
| `figures/build_figures.py` | `885434dc789d80d2885d961030c97803624c34297eda61bf2a15dd9040b5ded6` |
| `figures/cell-patterns.pdf` | `3905c4546c6417d2ac76f76d479ea44c0905cba452481cad4b1dadbcfc3ca114` |
| `figures/cell-patterns.png` | `902b138df4da6da762f34f8a9a70260a7211a523e17e3956ce91311db0d77cab` |
| `figures/moment-regimes-data.json` | `7ba790fdf8450ec3d4ed739f3e4d3cb8e11271e941251f42b51a274925408bc4` |
| `figures/moment-regimes.pdf` | `d8bf0d5e11a3d48df33fac54e634391a98b9ced726a66f1df2e29e02fc2cf585` |
| `figures/moment-regimes.png` | `86eec647046ad2edb7c61b76374ff9c07c4b09f44a7853581150043261b7e80f` |

## Handoff

The main quantitative claims are accepted at frozen v1. Findings MRF-V1-01 through MRF-V1-05 remain open for that exact revision. The integrator should make the local repairs in a new revision and request a delta review before recording acceptance of the complete manuscript and guide. No canonical source was edited during this audit.
