# Problem 21 speaker notes

The deck has 14 main slides and two optional backups. The planned speaking time is 17 minutes 40 seconds, leaving 2 minutes 20 seconds within a 20-minute slot. The title block uses the team and author names supplied by the user. Affiliations are omitted. The deck uses `N` for the original permutation size, including where the report's mixed-product section uses `n`.

Source anchors below are section or result names in the submission report. They remain valid after editorial reordering. The historical workspace path for the frozen mathematical source is `manuscript-round-01/frozen-manuscript-v10/manuscript/sections/`. The mathematical text is included inline in the delivered `report.tex`.

| Slide | Time | End time | Purpose |
| --- | --- | --- | --- |
| 1 | 0:35 | 0:35 | State the probabilistic task |
| 2 | 1:10 | 1:45 | Show what centering saves |
| 3 | 1:15 | 3:00 | Define the counts |
| 4 | 1:00 | 4:00 | State the scalar target |
| 5 | 1:30 | 5:30 | Condition on compatible matches |
| 6 | 2:00 | 7:30 | Derive the row-sum recurrence |
| 7 | 1:40 | 9:10 | Bound the positive moments |
| 8 | 1:20 | 10:30 | Handle powers and conflicting cells |
| 9 | 1:45 | 12:15 | Assemble the mixed bound |
| 10 | 1:05 | 13:20 | Recover Proposition 28 |
| 11 | 1:10 | 14:30 | Identify the biregular matching size |
| 12 | 1:40 | 16:10 | Locate the estimate in the spectral argument |
| 13 | 0:55 | 17:05 | State the exact no-conflict refinement |
| 14 | 0:35 | 17:40 | Disclose tools and verification scope |

## 1. Why centering helps a random matching

Say: A random permutation is a one-to-one matching. The task is to control expectations of mixed products of matching entries, including centered entries. This estimate is the probability input behind Proposition 28 in Bordenave's random-lift proof and the matching lemma used by Brito, Dumitriu and Harris.

The talk proves that input directly. It does not reproduce every graph-level counting argument. The three guiding moves are to preserve the centered singleton factors, condition exactly, and sum a remaining row.

Source: report, “The question and the proof mechanism” and “Where the estimate enters spectral-gap arguments”.

## 2. Two cells reveal cancellation

Point first to the separate cells. Two prescribed compatible matches occur with probability `1/[N(N-1)]`. After centering both entries, the terms simplify to `1/[N^2(N-1)]`. This is of order `N^(-3)`.

Then point to the same-row cells. Their indicators cannot both be one, so their centered product has expectation `-N^(-2)`. The extra inverse power in the first pattern comes from cancellation, not independence. Taking the absolute value of each summand before adding would obscure it.

Clarify that the dots mark requested cells. They do not assert that all dots are ones in the same permutation.

Source: report, “The question and the proof mechanism”, two-cell identity.

## 3. Which centered factors earn a gain?

A cell contains a color, a row, and a column. Each color labels one independent uniform permutation. Within a color the entries are dependent. Across colors the permutations are independent.

The exponents are nonnegative integers with `p_e + q_e >= 1`. The set `E` contains distinct cells and is nonempty. The general report theorem assumes `a <= N`. Repetitions are encoded by the exponents, so the number of factors can exceed the number of distinct cells.

A centered singleton has exactly one centered copy and no raw copy. It is consistent if no other requested cell of its color shares either its row or its column. Count these by `h`. Count the other centered singletons by `b`. A repeated centered factor does not count as a singleton.

Consistency is measured against the entire requested set, before selecting terms in any expansion and before sampling the permutations.

Source: report, “An attained envelope for mixed products”, definition preceding the theorem.

## 4. The product estimate

Read the formula by factors. `N^(-a)` is the basic matching cost. The factor `2^b` allows for conflicting centered singletons. Every consistent centered singleton earns the additional factor

`beta = sqrt(a-1) / [sqrt(N) - sqrt(a-1)]`.

For `2 <= a <= sqrt(N)`, this is at most `2 sqrt(a/N)`. The universal scalar prefactor is `sqrt(e)`. The proof will explain why it appears once after all colors have been merged.

Do not describe `sqrt(e)` as a newly discovered factorial estimate. Its raw factorial role is already recorded by Bordenave and Zhu. The report separately proves that no smaller universal prefactor works for this class by taking `N=a^2` and `a` compatible raw cells.

Source: report, Corollary “Scalar mixed bounds” and its optimal-prefactor argument.

## 5. Condition on compatible matches

This is the exact conditioning operation used in the proof. A prescribed set of `r` cells with distinct rows and columns occurs with probability `1/(N)_r`, where `(N)_r` is the falling factorial. Delete exactly those rows and columns. Every matching on the remaining rows and columns has the same number of completions, so the remaining block is a uniform permutation of size `N-r`.

The centering remains the original `1/N`. With `Z=NU-1`, each remaining row sums to `N-(N-r)=r`. This nonzero row sum is essential. Replacing the center by `1/(N-r)` would change the quantity being estimated.

The illustrated example removes two matches from a six-by-six board. It illustrates the deletion operation and makes no numerical approximation.

Source: report, “Exact depleted moments”. The conditioning issue in a source proof is reserved for backup slide 15.

## 6. A row sum gives the recurrence

Define `mu_j` using `j` remaining cells with distinct rows and columns. Relabel them to diagonal positions. Multiply the last row sum by the previous `j-1` diagonal factors, then take expectations.

There are `N-r-j+1` columns not used by the previous diagonal factors. Each contributes `mu_j` by symmetry.

There are `j-1` used columns. At column `i`, the two indicators in that column cannot both equal one. Expanding `Z_ii Z_ji` gives `-Z_ii-Z_ji-1`. After multiplication by the other diagonal factors, these three terms contribute `-mu_(j-1)`, `-mu_(j-1)`, and `-mu_(j-2)`. The second term uses a row relabeling.

Move those negative terms to the other side of the row-sum equation. The displayed recurrence follows. Its denominator is positive for `j+r <= N`. At `j=1`, the last term is omitted, giving `mu_1=r/(N-r)`. At full depletion `r=N`, only the empty moment `mu_0=1` is used.

Credit Collins and Nagatsu for the `r=0` recurrence after rescaling. The proof here uses the depleted form to handle mixed products.

Source: report, Lemma “Depleted row-sum recurrence”. Collins and Nagatsu, Proposition 3.3, equation (16).

## 7. Positivity gives a scalar bound

All coefficients of the recurrence are nonnegative. Starting from the two initial values therefore proves nonnegativity of every permitted depleted moment.

For `r+h <= a`, the denominator at any step through `h` is at least `N-a+1`. The two numerator coefficients are at most `2(a-1)` and `a-1`. Choose `beta` so that its geometric sequence solves the corresponding constant-coefficient equality.

The base case is valid because `r <= a-1` whenever `h>=1`, and

`mu_1 = r/(N-r) <= (a-1)/(N-a+1) <= beta`.

Substitute the inductive bounds `mu_(j-1) <= beta^(j-1)` and `mu_(j-2) <= beta^(j-2)` into the recurrence. The defining quadratic then gives `mu_j <= beta^j`. For `h=0`, use the empty moment instead.

The report proves a sharper, composition-dependent scalar factor `Gamma` when `h<a`. The simpler factor shown here is enough to recover Proposition 28.

Source: report, Lemma “A geometric supersolution”.

## 8. Repeated factors become affine

Now set aside the `h` consistent centered singletons. An indicator satisfies `M^2=M`, so every other factor reduces to a constant plus a multiple of `M`.

If a raw copy is present, `c=0` and `d=(1-1/N)^p`. With no raw copy, `c=(-1/N)^p` and `d=(1-1/N)^p-(-1/N)^p`, which is nonnegative. These formulas yield the displayed coefficient-weight bounds.

Expand the remaining factors. Selecting `dM` asks for that match to occur. Selecting `c` does not prescribe a match. Any selected set containing a conflict has probability zero. The consistent singleton set avoids all exposed rows and columns in every surviving selection.

Each nonisolated centered singleton can cost at most two in the affine sum. Repeated powers have weight at most one, regardless of multiplicity.

Source: report, proof of Theorem “An attained mixed-product envelope”, coefficient-weight inequality.

## 9. Merge colors and sum the terms

This slide packages the exact conditioning probability and depleted moment into `K_(j,r)`. For a compatible selected set, independence across colors gives the exact displayed product of kernels.

If asked why merging is valid: clearing the moment denominator gives a positive partition polynomial. A block of size `ell` has weight `((ell-1)N+r)(ell-1)!`. Joining partitions from two disjoint label sets and increasing the parameter to the sum of the two depletion counts gives the polynomial comparison. The falling-factorial inequality `(N)_u (N)_v >= (N)_(u+v)` completes the kernel comparison. All merged indices total at most `a<=N`.

Merge colors first, then increase the total depletion count to `a-h`. Take absolute values only of the affine coefficients and sum their weights. This produces `2^b N^(-a) F_N(a-h) mu_h(N,a-h)`.

The final two estimates are the geometric moment bound from slide 7 and

`log F_N(q) <= q(q-1)/[2(N-q+1)] <= 1/2`

when `q<=a<=sqrt(N)`. There is one global factorial factor, which is why the prefactor is `sqrt(e)` rather than one such factor per color.

Source: report, Lemma “Monotonicity and merging”, proof of the mixed envelope, and Corollary “Scalar mixed bounds”.

## 10. Recovering Proposition 28

Choose an orientation for every undirected base edge in a random lift. That edge's permutation is a color. Traversing it in reverse uses its inverse permutation, or equivalently the transposed matrix entry after orienting the factor consistently. The reverse direction is not a new independent color.

Distinct requested lift edges are the cells of the product, and the consistency definition agrees. Bordenave's `a_1` is exactly `h`. Since `a<=k<=sqrt(N)`, the displayed inequalities recover the Proposition 28 form with a smaller consistent-singleton factor. The `a=1` case is handled directly: an isolated centered singleton has expectation zero, and other allowed one-cell factors have absolute expectation at most `1/N`.

The proposition is a known result. The contribution presented here is the direct proof through compatible conditioning and positive depleted moments, together with the stronger finite envelope described in the report.

Source: report, “Random lifts: one permutation per base edge”. Bordenave, Proposition 28, printed page 1426.

## 11. Biregular matching uses half-edges

The bipartite configuration model has `n_L d_L` left half-edges and `n_R d_R` right half-edges. These numbers agree and are denoted by `L`. A uniform matching from the left set to the right set is exactly a permutation of `L` objects.

Its symmetric matching matrix has the displayed off-diagonal permutation blocks. Orient each nonzero matching factor from left to right and apply the product theorem with `N=L`. Same-side entries are zero, including in the centered matching matrix.

The normalization is `1/L`. It is not the reciprocal of either vertex count. This identifies the input in Brito, Dumitriu and Harris, preprint Lemma 7 and published Lemma 5.6. An unrestricted perfect matching of one half-edge set is a different model.

Source: report, “Biregular graphs: the size is the half-edge count”.

## 12. The bridge to the adjacency spectrum

A non-backtracking walk never immediately traverses the same edge in reverse. The matrix indexed by oriented edges need not be normal, so control its path matrices through the positive trace `tr((CC*)^s)`.

Expanding that trace yields products of matching entries. The theorem in this talk bounds each fixed cell pattern. The rest of the graph proof sums over patterns and controls local tangles. Those ingredients are external to this product estimate.

The determinant identity of Ihara and Bass connects non-backtracking roots to adjacency eigenvalues. For the biregular bipartite adjacency block `X`, the displayed relation applies to a positive singular value `s_X`, with `d_L,d_R>=2`. Set `x=z^2` to obtain

`s_X^2 = x + alpha gamma/x + alpha + gamma`.

If `s_X > sqrt(alpha)+sqrt(gamma)`, the quadratic has a positive root `x>sqrt(alpha gamma)`, hence a root `z` outside the stated circle. This is how a non-backtracking bound excludes positive adjacency outliers after the graph estimates are in place. Rectangular nullspaces can also give zero adjacency eigenvalues, which are outside this positive-singular-value calculation.

Do not claim a new second-eigenvalue theorem or an end-to-end audit of the cited graph arguments.

Source: report, “Why isolated centered factors help a trace expansion” and “The algebraic bridge back to adjacency”.

## 13. An exact maximum without conflicts

The scalar bound discarded information by replacing a depleted moment with a geometric estimate. Keeping that moment yields an exact maximum when `b=0`, for every nonempty support size `a<=N`, with `N>=2`.

The first values of the positive polynomial, if useful verbally, are `P_0=1`, `P_1=r`, and `P_2=r^2+r+N`. The compatible diagonal pattern on the slide attains the bound by conditioning on its `a-h` raw matches.

The report also determines exact maxima for one or two conflicting centered singletons and proves diagonal asymptotic refinements. Those are extensions of the probability analysis, not automatic improvements to the graph spectral theorem. No exact extremum is claimed for more than two conflicting singletons.

Source: report, Theorem “An attained mixed-product envelope”, Theorem “One inconsistent singleton and a stronger general bound”, and Theorem “The exact two-conflict envelope”.

## 14. Tool use and verification scope

Read the disclosure plainly. OpenAI Codex assisted drafting, coding, exploration and internal review. Python exact finite computations checked the recorded finite cases, including the recurrence, normalization and conditioning examples. LaTeX and rendering tools produced and visually checked the artifacts.

Finite verification does not prove the general statement. Internal review is not external peer review. The submission does not claim an end-to-end formal verification or a full audit of either cited spectral proof. The report gives the expanded disclosure.

End here for the timed talk.

## 15. Backup: two exposed arrows

Use this slide only if asked why a replacement conditioning argument is needed. The relevant source is equation (62) in Bordenave's published article, printed page 1428.

With requested cells `(1,1)` and `(2,2)`, the displayed conditioning exposes `sigma(2)=3` and `sigma^(-1)(2)=4`. Thus two arrows are fixed. The two remaining rows are 1 and 3, and the two remaining columns are 1 and 4. There are two equally likely completions, so the tested conditional probability is one half.

The source denominator counts only one exposed image and produces one third. The example does not contradict Proposition 28. It contradicts an intermediate conditional assertion under its displayed conditioning. Our proof exposes a compatible prescribed set and therefore knows the remaining dimension exactly.

Source: report, “Two checks on a conditioning formula”, example “Images and preimages remove two arrows”.

## 16. Backup: sources and attribution

Use this page for attribution or source questions. All links reproduce the report's verified bibliography. Bordenave supplies the proposition being proved. Brito, Dumitriu and Harris supply the biregular application. Collins and Nagatsu supply the undepleted recurrence and diagonal leading terms. Bordenave and Zhu already record the elementary raw-factorial `sqrt(e)` bound.

The report gives the wider literature comparison and its limits. A bounded source search is not a priority certificate.

## Rebuild and visual review

From the `slides` directory, run `bash build.sh`. It compiles the editable Beamer source twice, writes the final PDF next to the source, and renders all 16 pages under `renders/`. Compilation logs remain in `build/`. The renderer is Poppler's `pdftoppm`. No external image assets are needed because all diagrams are native TikZ.
