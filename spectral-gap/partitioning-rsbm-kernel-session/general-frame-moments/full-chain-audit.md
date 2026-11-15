# Independent full-chain audit: bounded moments for regular configuration frames

Prepared November 15, 2026 by `frame_chain_audit`. Only this file is written by this audit task. The existing lift packet, model theorems, algorithms, and frozen manuscripts were not edited. Historical novelty is not certified.

**Verdict: PASS for the bounded raw configuration-model moment, its direct transfer to the independent uniform-simple frame law, and the stated composition with the existing certified full-kernel algorithm.** I independently reconstructed the proof before reading the two new modules, then checked their actual complete sources. The conclusion is not inferred from nonpositive entropy alone.

## Sources and scope

New actual sources read in full:

- `central-frame.md`, SHA256 `e64d46ae873a6ce568b76784788b1605a38e249c2f8983451372486eff0315a7` (reread after its section-reference correction; no mathematical delta).
- `boundary-frame.md`, SHA256 `cbfd5c6c8372bbbb1a4e2ef01426bfd93225e54cc7842e9efadc7802fe07f5e4`.
- Root proposal `spectral-gap/regular-frame-bounded-moment-extension-root.txt`, SHA256 `18e65839025a1ffffc040f80db9428862ec976a927896eaf943891200ca73ff7`.

I also read the full prior simple-base-lift packet, including its central, zero-phase, sparse-boundary, and assembly notes. Its earlier PASS labels were not used as mathematical premises: the frame extension changes the model and requires the new arguments audited here.

For the algorithmic composition, actual sources read include:

- `spectral-gap/partitioning-dynamic-session/rsbm-full-kernel/certified-full-kernel.tex`, SHA256 `bb6ec1086a2d46f4a1d0b66c69aadc2d120b07157ba8e95f3c08ffb187843473`.
- Its nonsymmetric supplement `intertwiner-extension.txt`, SHA256 `cb893b0def524ba101a4419adf922f0dec60ad3156348c8e91d600887e743df9`.
- The prior regular-frame structural modules `THEOREM_AND_COMPOSITION.txt`, `SUPPORT_AND_ALGORITHM.txt`, and `rigidity/all-slot-onehot-rigidity.tex` under `spectral-gap/partitioning-sparse-session/regular-no-internal-audit/`, respectively at hashes `943dcf7e8df492b79ba1b0a21ab1dbc22b9ce42af72484d986c1cf8c4cf28bea`, `00c55b74296b9049008cca207f2f26a53315d560767fe26f3becaec0218bd8fa`, and `20b0d3740949db74ae26e372fd29706ea2107b08fe1bd857f63aa0d99d46e6df`.

The new mathematical moment theorem is as follows. Fix a finite connected reversible nonnegative integer frame `Q=(q_ij)` with every row sum the same `d>=3`. Type sizes have fixed positive proportions and obey `n_i q_ij=n_j q_ji`; each internal stub count `n_i q_ii` is even. Internal factors are independent uniform pairings of labeled stubs, and cross factors independent uniform stub bijections. Loops count twice in adjacency. For fixed prime `p`, fixed dimension `r`, and fixed matrix `R` over `F_p`,

`sup_(admissible sizes) E #{Y in F_p^(n by r): AY=YR} < infinity`.

The constant may depend on the fixed frame, field, and dimension. It can be uniform over `R`, since there are finitely many matrices at these fixed parameters. No growing-frame, growing-field, degree-two, noisy, adaptive-factor, or unequal-total-degree assertion follows.

Connectedness makes the size ratios rational and fixes them. A primitive positive integer size vector therefore permits the central note's parameterization `n_i=a_i N` along every admissible size. Equivalently one may use total size `n` with fixed positive rational weights. This is a change of scale, not an extra arithmetic restriction.

## 1. Exact full-slot count and reference normalizer

The physical slots must be retained in the local probability models. A type-`i` vertex has `q_ij` individually labeled slots aimed at old type `j`. Pooling only within a graph factor is appropriate for the pairing weight, but pooling the probability vector before comparing covariances would lose legitimate fluctuations.

For a prescribed assignment of root and neighbor labels, let `m_ij(x,y)` be the pooled category counts. A cross factor has exactly

`prod_(x,y) m_ij(x,y)! / (n_i q_ij)!`

as its matching probability. An internal factor has exactly

`[prod_x (m_ii(x,x)-1)!! prod_(x<y) m_ii(x,y)!] / (n_i q_ii-1)!!`.

It is zero unless its table is symmetric with even diagonal. Cross tables must reverse. Zero factors are omitted. These are exact labeled-stub counts, including loops and repeated edges. A loop is compatible only when both of its stubs request the label of their common root, already enforced by the stub categories; it needs no correction outside these factors.

In a single vector alphabet of size `q`, the legal local-star count is `q^d`; its root and any `d-1` neighbor labels determine the last one. The independent-star count is `q^(d+1)`. A graph configuration and a root labeling determine all physical neighbor labels uniquely. Thus, writing `W` for the exact pooled graph probability,

`E Z = q^(dn) E_P W`,

`q^(dn) E_Q W = 1`.

The root-label choices occur once, not twice. The second identity is an exact normalization, not a Gaussian approximation.

For a bipartite support, the induction needs two spaces of sizes `u,v` and type-dependent maps into the opposite space. Common total degree and reversibility give `n_L=n_R` exactly, even when individual old type sizes differ. The legal count is the product of `u v^(d-1)` on the left and `v u^(d-1)` on the right. It equals `(uv)^(d n_L)`, the reciprocal of the independent-neighbor expected weight. Therefore the same exact normalization holds. One-point spaces cause no problem. This equality would not automatically hold for unequal total degrees, and the proof does not claim that extension.

## 2. The new central comparison really controls a fixed neighborhood

The covariance statement in the new central source checks directly. Conditional on a root, any two distinct neighbor labels under the uniform legal star are independent uniform because `d>=3` leaves another coordinate to absorb the constraint. The same pairwise law holds under the independent-star reference. Covariance of the physical-slot table vector therefore agrees between `P` and `Q` and is positive on the full common-root-row real space. On its common-row modes the eigenvalue is `d/(|V_i||U_i|)` and on the other modes `1/(|V_i||U_i|)`. Singular on-site maps and `p|d` do not change this real covariance.

The independent support differences generate the full integer common-row lattice. The legal support differences have finite index `|U_i|^{|V_i|}` at type `i`. The additive-character calculation uses three physical slots and remains valid for repeated old neighbor types. It identifies every modulus-one Fourier point, rather than merely displaying necessary congruences. Legal affine support lattices are contained in independent affine support lattices for every size because every legal star is also an independent star. If pooled graph compatibility fails at a residue, the weight is zero; the upper comparison needs no residue assumption.

The fixed-epsilon tilted estimate has the needed uniformity. Finite support with positive covariance gives an analytic inverse mean-to-tilt map on a neighborhood of the common mean. Shrink to compact neighborhoods inside both convex supports. Tilted probabilities then stay uniformly positive, covariance eigenvalues stay uniformly bounded away from zero, and all relevant derivatives stay bounded. On the maximal-lattice torus, the characteristic-function modulus is uniformly below one away from zero. Near zero its logarithm has the uniform quadratic expansion and a cubic remainder. Fourier inversion at the tilted mean gives a *relative* local estimate with the exact covolume and determinant, uniformly over that compact tilt set. In particular it proves positive mass at every relevant affine lattice point for all sufficiently large sizes; no unproved lattice-support saturation premise is hidden.

Because the means and covariance matrices agree, the two rate functions agree through quadratic order. Thus, on the legal affine lattice throughout a sufficiently small fixed neighborhood,

`P_N(M=m)/Q_N(M=m) <= C I exp(C ||m-mu_N||^3/N^2)`,

where `I=prod_i |U_i|^{|V_i|}`. On the `sqrt(N) log N` window the sharper ratio is `I(1+o(1))`. Positive fixed proportions are enough to multiply the typewise estimates with scale `n_i`; no equal-size assumption is used.

The normalized weighted `Q` law is exactly a configuration sampled first, followed by independent uniform labels. Its concentration proof also checks:

- A uniform internal pairing is generated by a uniform stub permutation paired consecutively; each pairing has the same `2^(L/2)(L/2)!` preimages.
- A permutation transposition changes at most two edges and four physical incidences, including loops.
- A root-label change affects at most `2d` directed incidence indicators.
- Exposing permutation images admits a one-transposition completion coupling. Hence the scalar table entries have bounded-range Doob martingale increments over `O(N)` exposures; a fixed-dimensional union bound gives subgaussian table deviations.
- Cross-slot means equal the independent means exactly. An internal physical stub returns to its own vertex with probability `(q_ii-1)/(n_i q_ii-1)`, creating only an `O(1)` total mean correction per table. Thus concentration holds about the common iid-law mean, after adjusting fixed constants.

The resulting tail is `C exp(-c t^2/N)` for all `t>=C0 sqrt(N)`, not just inside the fixed neighborhood. Choosing epsilon so that the cubic likelihood-ratio exponent is at most `(c/2)||Delta||^2/N` makes the surrounding tail integrable under this normalized law. Integration removes the region outside `sqrt(N)log N` with error `O(exp(-c' log^2 N))`, with no polynomial loss. The central window is at most `I+o(1)` by the exact normalizer. This establishes the bounded full-uniform contribution for the general frame model. It avoids the unproved pooled precision calculation that the proposal was designed to replace.

## 3. Entropy zeros and repeated-slot symmetrization

The exact star/pair exponent has internal weight `w_i q_ii/2` and cross weight `w_i q_ij`. Symmetrize physical slots only within a fixed old neighbor type. This preserves the pooled tables and local equation and increases star entropy. Strict concavity shows that an unsymmetrized zero must have zero symmetrization loss and therefore already equal its symmetrization.

For a symmetrized law, average lossless deletion of each of the `d` physical slots. The common row sum and reversible edge balance cancel every root entropy. The exact identity is

`Phi=-(d-2)/d sum_(undirected factor types) edgeweight*I`

`     -(1/d) sum_i w_i sum_t J_it`.

Internal self-incidences have the necessary one-half in `edgeweight`; no absent internal factor contributes a term. Both coefficients are positive for present terms when `d>=3`.

At zero, every edge pair is independent and every retained neighbor tuple is a conditional product independent of the root. The finite-group lemma used in the source is valid: condition `d-2` coordinates to support points; each remaining one-coordinate marginal remains unchanged by the retained-product property. Their fixed-sum relation identifies their laws by reflection. Varying a third coordinate supplies translation invariance by the common support-difference subspace. Hence every marginal is uniform on a full affine coset.

All physical neighbors of an old type have the same difference subspace, even when slots repeat an old neighbor type. Therefore these subspaces are constant on even-walk components of the old type support. An internal factor gives an old self-incidence, hence an odd walk. Connected nonbipartite support leaves one common subspace; bipartite support leaves one on each side. The on-site map inclusions and quotient point-map equations in the new source are exactly necessary and sufficient. The zero star law is uniquely uniform on its legal affine support. The set of phases is finite at fixed field, dimensions, and old frame.

This classification includes the mixed bipartite phases, zero-dimensional sides, singular maps, and characteristics dividing the common degree. None can be discarded merely because it is absent in a scalar nonzero-eigenvalue example.

## 4. Sparse phase neighborhoods and exact conditioning

After quotienting by a proper phase, subtract its old-type coset point map in the quotient. It is an exact quotient solution on every configuration because the frame neighbor counts are fixed. The resulting defect solves a homogeneous quotient system. No exact lift of the quotient point map is required.

For any fixed quotient assignment, the original lifts form an affine fiber, empty or a translate of the lower-dimensional homogeneous kernel. Its size is at most that kernel count. This reduction is valid for the two-space problem as well: left equations are quotiented by the right subspace and conversely.

A quotient support `S` cannot have an exterior vertex receiving exactly one edge from `S`, counting multiplicity. Parallel edges may cancel in the field but then contribute at least two incidences, exactly as required by the certificate. If `s=|S|`, `i` edges are internal to `S`, `j` go outside, and `t` exterior vertices are touched, then

`ds=2i+j`, `t<=j/2`, and `E-(s+t)>=((d-2)/2)s`.

Loops count once as an edge and twice in `ds`. A certificate prescribing every incident support stub automatically prescribes all edges from `S`; no extra absent-edge event is needed.

The correlation with the homogeneous kernel is handled by actual conditional-law couplings. For a cross bijection, forcing a new pair by an image swap gives the same number of preimages for every permitted output. For an internal pairing with `m` currently unused stubs, forcing `{u,v}` replaces `{u,x},{v,y}` by `{u,v},{x,y}` unless already paired. Every output has `1+2(m-2)/2=m-1` preimages. Thus each operation gives the exact uniform conditional law, preserves prior prescribed pairs, and changes at most four vertex rows. After `E` operations the restricted operator differs in rank by at most `4r_*E`. Consequently

`E[Z_H | certificate] <= p^(4r_*E) E Z_H`.

This is an exponential-in-support constant factor, not an independence assumption.

The weighted certificate enumeration in the actual source retains the correct powers. The support/exterior choices cost at most `n^(s+t)/(s!t!)`; exterior stub choices cost `2^(dt)`; selected stub pairings cost at most `(2ds)^E`. Each prescribed pairing or bijection factor is at most `(C_frame/n)^E` when `s<=epsilon n`. The rank-comparison factor and quotient values are absorbed into a constant to the power `s`. The identity

`s^E n^(s+t-E)/(s!t!) = (s/n)^(E-s-t) (s^s/s!)(s^t/t!)`

then yields the stated `ds L^s(s/n)^((d-2)s/2)` bound. Summing the exterior count costs at most `exp(s)`. The displayed fixed choice of epsilon makes successive support terms geometric.

Unlike the simple-base-lift proof, the sum must start at support one in the configuration model. The new source does so. This gives a vanishing boundary correction `O(n^{-(d-2)/2})` times the restricted moment, which is sufficient. Using the old lift correction `O(n^{-(d-2)})` without excluding configuration singleton supports would be unjustified.

## 5. Closure of the full moment induction

Induct on the single ambient dimension for nonbipartite support, and on the sum of the two side dimensions for bipartite support. Every proper phase strictly lowers this parameter, and restricted maps remain within the stated type-dependent linear-map class. The all-zero-dimensional instance has exactly one assignment.

By induction, each lower-dimensional raw moment is bounded. The sparse proposition bounds its whole proper-coset neighborhood by that moment times `1+O(n^{-(d-2)/2})`. There are only finitely many phase centers. The full-uniform center is handled independently by the new central theorem in full physical-slot tables.

Choose open neighborhoods of these finitely many centers inside the corresponding controlled regions. On the complementary compact feasible-type set, the continuous original entropy exponent is strictly negative, because all its zeroes were classified. Exact factorial counting with its fixed polynomial number of types and Stirling prefactors makes this complement exponentially small. This proves a finite limsup of the raw configuration moment. The finitely many smaller admissible sizes have finite moments, giving the stated supremum.

The use of full physical-slot tables matters here: the central source does not merely control a pooled neighborhood. The unique full zero phase has full physical-slot product tables, so a neighborhood in the actual full type space is covered. Proper zero phases are covered by their continuous root-coset leakage neighborhoods. The compactness step therefore leaves no unexamined zero-entropy directions.

## 6. Direct simplicity transfer

Each active fixed-degree internal pairing factor and cross-biregular factor has a positive limiting probability of being simple at fixed positive type proportions. Degree-zero factors are absent. Internal degree one and cross `(1,1)` factors are already simple. The product over finitely many independent factors remains bounded below along every admissible sequence.

Conditioning these factors on simplicity gives exactly independent uniform simple regular/biregular graphs: every simple factor has the same number of labeled-stub realizations. Therefore the raw bound transfers directly by

`E[Z | all factors simple] <= E Z / P(all factors simple)`.

This argument applies to the unbounded random variable `Z`. Qualitative contiguity would not suffice and is not used. All small admissible simple-model sizes can again be included by increasing the finite constant.

## 7. Charged unknown-frame recovery composition

The bounded moment is the missing stronger input to the existing algorithm packet. Its precise composition requires the following steps; omitting any of them changes the conclusion.

Fix class and degree bounds `K,D`. There are finitely many true connected frames of order at most `K` and common degree between three and `D`, and finitely many nonnegative integer candidate matrices `R` of order `r<=K` with row sums at most `D`. Connected degree balance fixes each true frame's positive proportions; their minimum is bounded below uniformly over this finite family. Taking maxima of the proved moment constants therefore gives uniform bounded moments for every candidate family needed by the blind search.

For a candidate `R`, column vectorization gives the generally nonsymmetric operator

`K_R=I_r tensor A - R^T tensor I_n`.

The transpose on `R` is essential. Its dimension is `m=rn=O(n)` and it has `O(n)` nonzeros at fixed bounds. Both it and its transpose apply in `O(n)` field operations. No division by candidate cell sizes or reversible weighting in the finite field is used.

Use the existing certified symmetric-kernel primitive on

`S_R=[[0,K_R],[K_R^T,0]]`.

Its corank is `2h_R`, while its certified per-input expected work is only linear in that corank factor: `soft-O(n^2(h_R+1))` bit work. Project the returned complete kernel basis to the *right* kernel of `K_R`, select independent projected columns, and canonically normalize on pivot rows. This costs at most the same order and gives a complete base-field basis. The auxiliary left kernel is never enumerated.

Now enumerate only the `p^{h_R}` right-kernel vectors with an odometer/Gray update, maintaining the current full vector. The total number of digit changes is `O_p(p^{h_R})`, so generation and integer one-hot verification cost `O(n p^{h_R})` up to fixed-field bit factors. There must be no extra `h_R p^{h_R}` charge silently averaged using only `E p^{h_R}`. For unknown cell sizes require nonempty one-hot columns, but impose no supplied size vector; the original integer equation `AY=YR` is checked directly.

The actual certified algorithm source supplies a Las Vegas per-input expected basis cost valid at every rank, including nilpotent and exceptional inputs. Its extension-field construction, preconditioner trials, complete-kernel rank certificates, bounded bad-trial work, and descent to the fixed base field are charged. In particular, its use does not assume that a high-probability small-corank event permits a cheap fallback on the complement.

The new raw moment gives `E(h_R+1)<=C` and `E p^{h_R}<=C`. Averaging the valid per-input bound yields unconditional expected `soft-O(n^2)` bit work over the frame law and computational randomness, with expected `soft-O(n)` basis workspace and `O(n)` output bits for each fixed finite candidate family. Enumeration of the doubled kernel would instead require the larger-target bound `E p^{2h_R}=E Z_diag(R,R)`. The present general theorem also supplies that bound at fixed target dimension `2r`, so doubled enumeration is not invalid under the full theorem; it is merely unnecessary. The stated right-kernel composition uses only the smaller single-target moment.

The separately proved all-slot real one-hot rigidity and no-small-support theorem apply to precisely this independent simple regular-frame model, including zero/one internal degrees and odd admissible sizes. They state that with high probability every bounded-class integer equitable partition is a planted coarsening. The planted quotient is among the finite candidates. Selecting a fully enumerated accepted partition with the largest class count then recovers the true classes up to names and the unknown quotient by exact neighbor counts. Multiple coarse quotients are harmless. Without that structural theorem the bounded moment would prove fast complete listing, not identification of which partition was planted.

For a random simple-base lift, no simplicity conditioning is needed, and this specializes to all lift sizes. For general fixed frames the direct conditioning above is the required bridge. The scope is the finest equitable partition among at most the supplied fixed `K` classes; it is not a claim about the unbounded singleton partition, arbitrary graph-cover recognition, or growing bases.

The classical black-box primitive's published preconditioning theorems were already source-audited in the prior packet. This audit reread the actual certified-kernel manuscript and verified its hypotheses and the new composition, including the nonsymmetric block reduction. It is not a new independent proof of every cited classical finite-field preconditioner.

## Final limits

No counterexample or unresolved mathematical defect was found within the stated fixed, connected, common-total-degree-at-least-three frame class. The main caveats are substantive scope limits, not gaps to fill by entropy inference:

- The graph factors must be the independent uniform configuration factors, followed if desired by direct simplicity conditioning.
- The common degree must be at least three. Degree two removes the entropy coercivity and supplies cycle phenomena outside this proof.
- Bipartite mixed-subspace phases require the enlarged two-space induction.
- The field, ambient dimensions, frame, and class/degree bounds are fixed. The constants and thresholds are not claimed uniform in growing parameters.
- A bounded intertwiner moment does not by itself imply minimal real eigenspace dimension, exact old/new eigenvalue noncollision, or noise robustness.
- Near-quadratic expected recovery uses the separate fully charged certified sparse-kernel primitive and the earlier one-hot structural rigidity theorem, with the right-kernel projection and enumeration order just stated.

Under those hypotheses the new two-module argument supports the proposed general-frame bounded raw moment and the expected near-quadratic recovery/listing application.
