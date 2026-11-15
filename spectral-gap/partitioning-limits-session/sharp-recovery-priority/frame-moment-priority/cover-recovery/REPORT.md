# Primary priority audit: bounded frame moments and blind cover recovery

Date: 15 November 2026. This is a source-specific comparison, not a historical firstness certificate or an independent verification of the new mathematical proof.

**The strongest newly located predecessor is a 2023 public-key attack that actually recovers the four fibers of sampled cubic `K4` covers by linear algebra. The average-case fiber-recovery question itself appears explicitly in Fellows–Koblitz (CRYPTO 1992 proceedings, published 1993). These must be credited. Neither inspected source proves the present arbitrary-frame bounded raw moment or an unconditional expected near-quadratic bit bound.**

## 1. Target and current proof boundary

The target is a fixed reversible integer frame `d_ij`, sizes `n_i=a_i N`, independent uniform cross-stub bijections and internal pairings, and a symmetric certificate

`0 <= q_ij < 1/2`, `sum_j d_ij q_ij = 1`.

The strongest current moment assertion includes forced zeros. For every fixed prime `p`, dimension `r`, and `R`, it bounds the **raw** expectation

`sup_N E #{Y in F_p^(n by r): AY=YR} < infinity`,

including deterministic planted solutions and rare configurations. The full channel extension allows typed finite domain/output spaces, injective present channels, isomorphisms on positive-weight factors, and arbitrary on-site linear maps. All parameters are fixed as `N` grows. Direct conditioning on all factors being simple preserves the upper bound at admissible sizes where simple factors exist.

I read the actual current master `spectral-gap/zero-omission-channel-session/bounded-channel-moment-theorem.md`, SHA256 `9248cfd3b1791d8276d80e4b16de5bfdb49ca9eea662a016086747eac85320bf`, and the complete root audit `spectral-gap/zero-omission-channel-root-audit.txt`, SHA256 `22ec12120c5bba523cd9a9e7d7ad4d50a30b3e2c12d368263fa1a8d5bdff8396`. The latter passes the four actual proof modules, but expressly does **not** certify an algorithmic recovery composition. This supersedes the earlier status in which zero weights were merely a proposal.

I also read the regular-frame root moment audit, the positive-omission proposal and actual positive theorem, the earlier zero-weight proposal, and `regular-frame-recovery-priority.txt`. The positive theorem's Section 6 spells out the intended recovery composition. Extending its conclusion to the new zero-weight class still requires checking the separate one-hot identifiability/closure theorem and the certified kernel primitive under that exact class. A moment theorem alone is not that recovery theorem.

## 2. Direct historical predecessor: the `K4`-cover question

**Michael Fellows and Neal Koblitz, “Kid Krypto,” in E. F. Brickell (ed.), Advances in Cryptology—CRYPTO '92, LNCS 740 (1993), pp. 371–389.** Publisher citation and DOI: [10.1007/3-540-48071-4_27](https://link.springer.com/chapter/10.1007/3-540-48071-4_27). The [author bibliography](https://mike-fellows.net/wordpress/bibtex/) independently gives 1993. The inspected scan's 1998 footer is not the publication year; Springer’s later online dates are not the original proceedings date.

Primary full text: [scanned paper, Section 4.5, printed p. 385 / PDF page 15](https://static.aminer.org/pdf/PDF/000/120/007/kid_krypto.pdf#page=15). It partitions `4m` vertices into four `m`-sets and places a bijection on each of their six pairs. Every fiber is a perfect code. It explicitly discusses recovering this partition from a graph promised to cover `K4`, asking about difficulty “in the sense of average-case complexity.” It separately cites worst-case recognition hardness. This is an explicit earlier question, not a proved average-case hardness result.

Distribution precision: the prose says the six correspondences are random; it does not formally state independent uniform sampling. Taking six independent uniform bijections gives exactly the canonical random `K4`-lift ensemble. Identify that law as the precise interpretation, rather than attributing a distributional theorem to this paragraph.

Section 4.4, printed p. 384, breaks certain ciphertexts by solving coefficient equations. That attack does not recover the graph fibers.

## 3. Direct algebraic algorithm ancestor: actual public-key recovery in 2023

**Cottaar et al., Report on evaluation of KpqC candidates**, report dated 31 October 2023; [Cryptology ePrint 2023/1853](https://eprint.iacr.org/2023/1853), received 2 December and approved 4 December 2023. Primary full text: [authors’ report PDF](https://math.deweger.net/reports/%5B2023%5DKpqC.pdf#page=23). Exact anchor: Chapter 3, Section 3.1, **“Details of the second attack,” PDF page 23**, printed p. 17. The attack is attributed within the chapter to Daniel J. Bernstein, Jolijn Cottaar, and Tanja Lange.

The public graph has four hidden 64-sets and six random pairwise correspondences. The second attack uses `(A_G+I)v=1`, echelon reduction, and equality of the resulting affine coordinate formulas. Seven of ten tested keys yielded the four fibers exactly. Three yielded cell sizes `1,1,63,63,64,64`, with either 64-cell sufficient for decryption. Section 3.2 separately identifies edge-order leakage and says sorting edges would not prevent this second attack.

This is a **fiber-recovery algorithmic predecessor**, not merely ciphertext recovery. The passage gives experiments and discusses further ambiguity; it does not supply an asymptotic success theorem, specify the elimination field, control nullspace tails, or establish expected near-quadratic bit work.

**Our mathematical comparison, not a theorem attributed to that report.** For `Q=J_4-I_4`, each one-hot fiber column solves the displayed affine perfect-code system. Its homogeneous differences lie in `ker(A_G+I)`. Grouping equal coordinate functionals on the complete affine solution space recovers fibers when no extra kernel directions distinguish vertices inside a fiber. The present general intertwiner enumeration keeps the same basic linear-relaxation idea, while permitting extra kernel directions and charging the enumeration through raw exponential-nullity moments. Thus “first recovery of graph-cover fibers by linear algebra” would be untenable; the broader moment theorem and proved average-time guarantee are the defensible distinction to examine.

The original [IPCC specification](https://www.kpqc.or.kr/images/pdf/IPCC.pdf), Section 3.2, Algorithm 4 Steps 2–3, PDF pp. 7–8, confirms equal four-way partition and a random one-to-one correspondence on every pair. Its notation and prose still do not formalize independence/uniformity as an asymptotic probability theorem. The attack report concerns actual generated keys, not all fixed bounded frames.

## 4. A close title that does not supply the target theorem

**Michael Scholkemper and Michael T. Schaub, “Blind Extraction of Equitable Partitions from Graph Signals,” ICASSP 2022**, [arXiv:2203.05407](https://arxiv.org/pdf/2203.05407).

Exact anchors: Section 2 identifies the objective as the **coarsest** equitable partition; Section 4, Algorithm 1, proves exact extraction using a controlled linear graph-filter oracle. Its finer-partition discussion on PDF p. 3 assumes an appropriate starting vector. Section 5, Theorem 1, PDF p. 4, analyzes noisy low-rank graph-filter observations: known class count, a globally minimizing `k`-means solution, bounded samples, and a positive covariance spectral separation enter the statement. The full proof is Section 9.2.

This is neither the same observation model nor a theorem about arbitrary-frame fiber recovery. In a regular graph, the coarsest equitable partition is one cell, whereas the target includes nontrivial bounded fibers. No theorem there gives unconditional expected soft-`n^2` bit work across the present frame family. Its synthetic locally colored configuration model is relevant experimental context, not a substitute for those missing quantifiers.

## 5. The omission certificate is classical fractional-factor geometry

For a loopless simple base or realization, put `x_e=2q_type(e)`. Then

`sum_(e incident v) x_e=2`, `0<=x_e<1`.

These are the degree constraints and strict upper-capacity part of the classical **fractional 2-factor LP**. A primary explicit formulation is Bagaria–Ding–Tse–Wu–Xu, [Hidden Hamiltonian Cycle Recovery via Linear Programming](https://arxiv.org/pdf/1804.05436), Equation (6), PDF p. 4; published in Operations Research 68(1) (2020), 53–70, [DOI](https://doi.org/10.1287/opre.2019.1886). Their Theorem 1 concerns an independently weighted complete graph with different edge-measurement laws on/off a planted Hamiltonian cycle. It is not a theorem for the present unweighted frame ensemble. The shared LP vocabulary does not make the statistical models interchangeable.

Here are precise algebraic consequences for this audit; these are not priority assertions:

1. For an arbitrary reversible frame, a certificate gives the same feasible `x` on **every** realization, assigning weights by old edge type. Internal loops use two incidences in the degree equation, consistent with the configuration adjacency convention.
2. Conversely, average any feasible realization's `x_e` over each old edge type. For `i!=j`, define `q_ij=(sum_(E_ij) x_e)/(2n_i d_ij)`; reversibility makes the reverse definition equal. Internally define `q_ii=(sum_(E_ii) x_e)/(n_i d_ii)`, including loop multiplicity in the incidence budget. Summing vertex budgets yields `sum_j d_ij q_ij=1`. Strict upper bounds survive averaging. Positive lower bounds survive as well when imposed on every edge. Thus the type certificate is exactly this averaged strict-capacity feasibility condition, not an unrelated notion of “balance.”
3. The zero-weight theorem permits `x_e=0`; the positive theorem requires `0<x_e<1` on every present type. Neither permits an upper-saturated edge `x_e=1`. Ordinary fractional 2-factor feasibility allowing upper saturation is a larger class.
4. Equivalently, the strict-upper certificate can be rescaled into a fractional `tau`-factor for some real `tau>2`: if `c=max_e x_e<1`, then `y=x/c` has degrees `tau=2/c>2` and `0<=y<=1`; conversely a fractional `tau`-factor gives `x=2y/tau<1`. Apply this to the fixed type weights, so the slack is independent of `N`.
5. This condition is stronger than merely having a fractional perfect matching and does not follow from minimum degree three. Any bipartite feasible realization must have equal physical side sizes by summing the two degree budgets. In particular `K_(3,12)` lifts fail it and have a deterministic large zero eigenspace. Feasibility of the fixed finite certificate is an LP question; feasibility alone proves no bounded finite-field kernel moment.

There is also directly relevant older random-lift enumeration. **Greenhill–Janson–Ruciński, “On the number of perfect matchings in random lifts,” CPC 19 (2010), 791–817**, [primary author PDF](https://web.maths.unsw.edu.au/~csg/papers/lifts.pdf), [DOI](https://doi.org/10.1017/S0963548309990654), Section 3. Their Eq. (3.1) is an exact annealed matching-count sum over the fractional-perfect-matching lattice; Eq. (3.4), Lemma 3.2, and Theorem 3.6 supply entropy, maximizer, and lattice-Laplace asymptotics for regular bases. This is strong prior art for the counting machinery. Its observable is the number of perfect matchings, whose expectation is exponential, rather than all finite-field solutions of `AY=YR`; it does not recover unknown fibers. No claim that fractional matching conditions or lattice-Laplace counting were introduced here is warranted.

## 6. Normalized rank results do not imply the needed raw moment

**van der Hofstad–Müller–Zhu, “The asymptotic rank of adjacency matrices of weighted configuration models over arbitrary fields” (2025)**, [arXiv:2508.02813](https://arxiv.org/pdf/2508.02813). Precise anchors: Assumptions 2.1 and 2.3, Definition (2.4), Theorem 2.4 and its uniform strengthening Theorem 3.1. They treat configuration models with a prescribed degree distribution, fixed independent-of-graph nonzero edge weights, and normalized rank; Assumption 2.3 is log-concavity of the second derivative of the degree generating function. Formula (2.4) removes loops and collapses multiple edges. Theorem 2.4 gives convergence of `rank(A_n)/n` to a variational constant over any field.

It is not the block-constrained independent-factor law, an arbitrary on-site matrix intertwiner statement, or a bounded raw solution-count theorem. This is nevertheless an essential recent comparison when describing general-degree finite-field results.

The logical distinction is elementary but decisive. With `h_R=dim ker(I_r tensor A-R^T tensor I_n)`, the count is `p^h_R`. A normalized rank limit may permit `h_R=sqrt(n)`. Even `h_R=O(1)` with high probability does not bound `E p^h_R`: a variable equal to `n` with probability `p^(-n/2)` and zero otherwise converges to zero in probability but has exponentially growing `E p^h_R`. A qualitative contiguity result likewise cannot transfer this unbounded expectation without quantitative domination or uniform integrability.

For repeated edges, pooled configuration factors also differ from independent matchings assigned separately to each edge of a multigraph base. Pure simple-base lifts with cross degrees zero or one coincide with the usual cover law; the general reversible frame need not. Any proposed prior theorem must match the actual pools, or supply an appropriate quantitative change-of-measure argument.

## 7. What the expected-time consequence must add

The new positive theorem's proposed composition uses a finite candidate family of quotient matrices `R` (class count and degrees bounded), a certified **complete right**-kernel primitive with per-input expected work soft-`O(n^2(h_R+1))`, and full enumeration/verification costing soft-`O(n p^h_R)`. Under a raw bounded moment both terms have bounded expectation. The integer one-hot test prevents accepting merely modular solutions. A separate structural theorem is needed to ensure every accepted bounded partition is a planted coarsening, after which maximum class count recovers the true unknown frame.

This explains the exact distinction from the old cubic attack. A theorem controlling all fixed `p,r,R` and the rare large-kernel contribution can establish unconditional expected bit work; observing that a linear system often has only four coordinate formulas cannot. It also explains why the separate identifiability and certified linear-algebra inputs must be included before stating a zero-weight recovery corollary. The current zero-channel master appropriately stops at supplying the moment input.

The pre-existing `regular-frame-recovery-priority.txt` already checks general-frame spectral recovery, lift detection, uniqueness under stronger degree assumptions, coarsest fibrations, and worst-case cover recognition. I did not duplicate its generic searches. None of the **newly inspected** primary sources supplies the conjunction of the present sampling law, all fixed fields/targets, raw bounded count, and unconditional expected near-quadratic unknown-frame recovery. This scoped search result is not proof that no such result exists.

## 8. Remaining primary-access limitation

The related 2021 paper by **Sujin Kwon, Ju-Sung Kang, Yongjin Yeom**, “Analysis of public-key cryptography using a 3-regular graph with a perfect dominating set,” TENSYMP 2021, pp. 1–6, [DOI](https://doi.org/10.1109/TENSYMP52854.2021.9550868), is confirmed by the publisher record, Crossref publisher metadata, proceedings contents, and IPCC references. Its full text was not accessible in this audit. I therefore do not assert what algorithms or theorems it contains. This is an explicit unresolved earlier lead, although the directly inspected 2023 public-key attack already establishes the important algorithmic ancestry.

Recommended framing: credit the earlier `K4` average-case question and algebraic public-key/fiber attack; describe the candidate contribution as a fixed-frame, all-target **raw moment theorem** under a strict fractional-factor certificate, and, only after composition is verified, its proved expected-time recovery consequence. Do not claim firstness for graph covers, equitable partitions, fractional-factor feasibility, linear-algebraic fiber recovery, or annealed lattice enumeration.

## 9. Local primary evidence

Downloaded originals and text extracts are in `sources/`. The key source hashes are:

- Fellows–Koblitz scan: `641103bdcdc4d022ce0879833d60cedb95cd830991ecb133755de84bf40dac95`.
- KpqC 2023 report: `4a6d8ac38e6b8b5ea3737c7b4aa27e25224cf45ae12badf92792bf25451bd27b`.

`sources/kid-15.png` shows the original `K4` paragraph with printed page 385. `sources/kpqc-second-attack-page.png` shows the complete actual second-attack passage on PDF page 23. The source list and PDF hashes are independently recheckable; the source access limitations above are not hidden by metadata-only citations.
