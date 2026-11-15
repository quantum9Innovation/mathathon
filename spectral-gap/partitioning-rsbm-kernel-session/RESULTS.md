# RSBM planted-eigenvalue kernel session

The all-parameter **one-dimensional real kernel** target has not been proved or falsified. A later type-counting argument does, however, give polynomial-time exact recovery for every fixed `d1>d2>0` in the original random-cross RSBM, without requiring one-dimensionality. The real-kernel result has the following scope, using Mészáros's established mixing theorem and known contiguity:

| Internal degree and block sizes | Result |
| --- | --- |
| `d1>=3`, even `N` | `dim ker_R(A-(d1-d2)I)=1` with high probability |
| Even `d1>=6`, odd `N` | Same conclusion, by the separate vertex-insertion addendum |
| Odd `d1>=3` | Admissibility forces even `N`, hence all admissible sizes are covered |
| `d1=4`, odd `N` | Unresolved by these arguments |
| `(d1,d2)=(2,1)` | Real-kernel simplicity remains unresolved |

All degrees are fixed, `d1>d2>0`. The proved conclusions are **uniform over every prescribed simple `d2`-biregular cross matrix**, chosen independently of the two random internal graphs. They also hold for an independent random cross graph. No assertion is made for a cross graph chosen adaptively after seeing the internal graphs.

The imported results and the planted-eigenvector identity are not claimed as new. Zhu–Zhu Lemma 9.1 already contains broader simplicity wording; its cited gap proof does not justify that wording inside the bulk. The present proofs give an explicit independent derivation in the stated scope. Novelty is not established here.

## Reviewable proof artifacts

- `rsbm-kernel-even-blocks.tex` and `rsbm-kernel-even-blocks.pdf`: five-page frozen even-block theorem and proof, including the full model transfer and exact polynomial-bit recovery conditional on simplicity.
- `rsbm-kernel-odd-addendum.tex` and `rsbm-kernel-odd-addendum.pdf`: five-page odd-block extension for even `d1>=6`.
- `rsbm-boolean-rigidity.tex` and `rsbm-boolean-rigidity.pdf`: five-page self-contained Boolean-rigidity proof for `d1>=3`, all-parity polynomial finite-field kernel moment for `d1>=2`, and the polynomial enumeration algorithm. The `(2,1)` case invokes the separately proved low-degree rigidity count.
- `meszaros-even-block-proof.md`: detailed original derivation of the finite-field first moment.
- `odd-block-finite-field.md` and `odd-block-surgery.md`: expanded conditional first-moment and distributional calculations for the addendum.
- `kernel-literature-audit.md`: exact primary-source scopes, Zhu–Zhu citation issue, recent regular-graph/lift results, exponential conditioning obstruction, and prior algebraic detection work.
- `deterministic-reductions.md`: deflated kernel, signed matrix-tree criterion, exact rational recovery, and an estimate excluding eigenvectors supported on at most a small fixed fraction of the vertices.
- `low-degree-identifiability.md`: full `(2,1)` partition-count proof, switching motif, and a finite exact counterexample to “partition uniqueness implies kernel simplicity.”
- `boolean-rigidity-macroscopic.md` and `boolean-rigidity-near-plant.md`: independently audited detailed counts and the explicit macroscopic entropy gap, plus the direct near-plant corollary of the small-support estimate.

The three PDF builds completed without LaTeX warnings, unresolved references, or overfull boxes. The primary Mészáros and Nguyen–Wood PDFs used to check the imported statements are saved in `literature/`. Independent agents checked the even-block proof, its standalone TeX, the odd-block algebra and sampling-law transfer, and the Boolean macroscopic and near-plant arguments. These are mathematical audits, not formal proof-assistant verification.

## All-parameter recovery by polynomial enumeration

For the original independent uniform random internal and cross factors, exact star-profile counting gives a first-moment exponent

`Phi=H(star+)+H(star-)-d1/2[H(internal+)+H(internal-)]-d2 H(cross)`.

Deleting one internal-neighbor coordinate through the eigenvector constraint and using conditional entropy subadditivity gives `Phi<=0` over every fixed finite alphabet whenever `d1>=2`. Over a fixed odd prime field, the polynomial number of types and uniform Stirling prefactors therefore imply

`E |ker_Fp(A-(d1-d2)I)| <= C N^kappa`.

Markov's inequality bounds the finite-field kernel dimension by `O(log N)` with arbitrarily prescribed polynomial tail, by choosing a sufficiently large fixed logarithmic cutoff. Enumerating signs on an injective set of kernel coordinates takes `2^r poly(N)` time for kernel dimension `r`. Exact integer verification discards false modular candidates.

For `d1>=3`, the sign-vector type count has a strict macroscopic gap; a variance argument makes its zero phases exactly the two planted assignments. Near-plant alternatives are suppressed by the support estimate. Thus the probability of a second sign vector is `O(N^{-(D-2)(delta+1)})`, with `D=d1+d2` and `delta=d1-d2`, at every admissible block size. The separate `(2,1)` count supplies the remaining case with error `Theta(N^-2)`. Together these give a worst-case polynomial-time recovery algorithm with polynomially small failure probability for every fixed `d1>d2>0`.

This conclusion is separate from the stronger one-dimensional-kernel target. Its type count depends on the random cross factor and does not assert the uniform-prescribed-cross scope of the partial simplicity theorems. Root independently found a conditional-variance version of the macroscopic gap that also covers `(2,1)` directly; this session's compiled proof instead retains the independently established low-degree counting argument for that pair.

## What the main calculation establishes

For each fixed odd prime `p` not dividing `d2`, the matching-model expected finite-field kernel size has limiting upper bound `2p`. Real nullity at least two forces finite-field nullity at least two, so its limiting probability is at most `2/p`. Sending fixed primes to infinity proves the qualitative high-probability conclusion. No growing-prime uniformity is used, and no effective or polynomial failure rate is obtained from this argument.

For odd block sizes with even internal degree `k>=6`, insert one vertex into an even-size graph by deleting `k/2` disjoint edges and joining their endpoints to the new vertex. The surgery output is within `O(1/N)` total variation of uniform simple regular graphs. In an auxiliary colored sampling law, every selected-edge pattern leaves at least `k/2>=3` independent untouched matchings. The conditional finite-field argument is applied **before** conditioning the original graph on simplicity; subsequent TV comparison, bounded-cost simplicity conditioning, contiguity, and surgery transfer are performed in that order.

## The `(2,1)` conclusions and obstruction

The exact counting argument proves

`P(second admissible balanced partition)=Theta(N^-2)`.

An eight-vertex local switch also gives

`P(dim ker_R(A-I)>=2)=Omega(N^-2)`.

This is compatible with a high-probability simplicity theorem and prevents a superpolynomial error claim for this model. The real-kernel upper bound has not been proved. A certified example with `N=8` has real nullity two but only the two planted sign vectors, so partition rigidity cannot settle the real-kernel target by itself.

All session artifacts were written only in this directory. No frozen paper or other research directory was edited.
