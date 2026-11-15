# Bounded primary-source audit: all fixed assortative degree pairs

Checked 2026-11-15. This extends `recovery-priority-audit.md` from the
cubic case to the theorem for every fixed `a>b>0`.

## Finding and recommended claim

The theorem's scope matches the two equal-block, noiseless,
fixed-degree efficient-exact-recovery conjecture stated by Barucca.
I found no independently established prior all-parameter recovery proof
in the primary sources checked below. That is a bounded search result,
not a historical-priority certificate.

Use this description:

> An independent proof of polynomial-time exact recovery in the uniform
> simple two-community RSBM for every fixed pair of integer degrees
> `a>b>0`, along every admissible block size. The polynomial exponent may
> depend on the fixed degrees. Historical priority is not asserted.

Do not say that the all-parameter spectral conclusion was never stated:
Zhu–Zhu's Lemma 9.1 does state unrestricted planted-eigenvalue simplicity.
Its cited argument does not establish that unrestricted scope, and the
same paper explicitly leaves full recovery open. The current proof
should stand independently of that lemma.

The theorem here proves exact recovery; it does not prove general real
eigenvalue simplicity or noise robustness. The algebraic eigenvector
identity, colored-star enumeration, and low-dimensional Boolean
enumeration are prior or elementary ingredients. The relevant derived
argument combines a polynomial binary kernel moment, an explicit Boolean
entropy gap, and verification of the affine candidates.

## Precise theorem comparison

Put `d=a+b`, `Delta=a-b`. In the table, a parity hypothesis on **a** is
different from the inherent admissibility condition `aN` even on block
size **N**.

| Primary source | Exact applicable scope | Relation to the new proof |
|---|---|---|
| Brito et al., SODA 2016 / arXiv v4, Theorems 1–3 | Partition uniqueness for `a>b>d0` for an unspecified sufficiently large constant; efficient exact recovery for `Delta^2>4(d-1)` and even a; a separate majority bootstrap assumes `a>b+4`. The paper globally assumes `min(a,b)>=3`. | Does not establish all fixed pairs, cubic recovery, or the general bulk-eigenvalue case. |
| Barucca, PRE 2017, Section IV.A | Proposes recovery via eigenvector extendedness, supplies numerical evidence, and conjectures full efficient recovery for all `a>b>0` with two equal blocks. | Establishes the conjecture and conceptual recovery idea, not the needed rigorous rank/nullity estimate. |
| Bandeira et al., COLT 2021, Remark 3 | Polynomial distinguishing of the noiseless equitable model from uniform regular graphs at all parameters by algebraic eigenvector structure. | Distinguishing is already recognized; exact partition recovery requires more. |
| Zhu–Zhu, arXiv v3, Theorem 3.10(3), Corollary 3.11 | Exact spectral recovery under `Delta^2>4(d-1)` and even a. Remark 3.12 leaves removing parity as future work; the introduction says full efficient recovery remains open. | Their displayed recovery theorem remains restricted. Their broader Lemma 9.1 has the citation issue described below. |
| Dembo–McKenzie, arXiv 2603.04386, Theorem 1.8 | General fixed expanding degree matrices, including the RSBM's matrix, but the eigenvector is randomly selected from a sufficiently slowly shrinking spectral window. | Does not control one fixed planted eigenspace, give logarithmic nullity, or give an exact recovery algorithm. |
| He–Huang–Wang, arXiv 2610.08127 | Fixed-energy microscopic universality and eigenvector moment estimates for uniform simple d-regular graphs, fixed `d>=3`. | The distribution is not the block-conditioned ensemble; no RSBM recovery theorem is stated. |
| OpenAI, September 23 / October 5, 2026 | Fixed-energy GOE universality for uniform simple fixed-degree regular graphs, and an extension with sufficiently weak fixed iid uniform diagonal disorder. | Neither manuscript states an RSBM or logarithmic-nullity recovery result. |
| Huang–Xu, arXiv 2610.37463 | Local law and delocalization for lifts of a fixed connected simple base of minimum degree three. | Mesoscopic spectral information and a different written model, not prescribed-point simplicity or all-parameter recovery. |

## Primary references and the important qualifications

**Brito et al.**
[Recovery and Rigidity in a Regular Stochastic Block Model,
arXiv:1507.00930v4](https://arxiv.org/pdf/1507.00930v4), PDF pp. 2–4.
Definition 1 is exactly the independent uniform-simple-factor model
used here. Theorem 2 has both the separating inequality and even-a
hypothesis. Theorem 1's uniqueness statement requires sufficiently large
cross degree; its unrestricted extension is not proved there. The
source explicitly distinguishes exhaustive-search recovery from its
efficient algorithm.

**Barucca.**
[Spectral partitioning in equitable graphs, PRE 95, 062310
(2017)](https://lims.ac.uk/wp-content/uploads/barucca2017spectral-1.pdf),
Section IV.A, PDF p. 5. The concluding conjecture in that section is for
two equally sized communities and all integer `cin>cout>0`. The source
acknowledges that rigorous recovery was established only in a restricted
parameter region. Its inverse-participation-ratio proposal and numerical
examples precede the present proof.

**Bandeira–Banks–Kunisky–Moore–Wein.**
[Spectral Planting and the Hardness of Refuting Cuts, Colorability, and
Communities in Random Graphs, COLT
2021](https://proceedings.mlr.press/v134/bandeira21a/bandeira21a.pdf),
Remark 3, PDF p. 7, concerns distinguishing at all parameters. The added
rewiring noise in their hardness formulation is necessary to suppress
the noiseless algebraic signal. Their statement must not be paraphrased
as an all-parameter exact-recovery theorem.

**Zhu–Zhu.**
[Non-backtracking eigenvalues and eigenvectors of random regular graphs
and hypergraphs, arXiv:2312.03300v3, dated 25 September
2026](https://arxiv.org/html/2312.03300v3), Section 1.3, Theorem 3.10,
Corollary 3.11, Remark 3.12, and Lemma 9.1. The lemma's unrestricted
simplicity assertion would imply all-parameter recovery if independently
proved. Its proof cites Brito et al., Section 4, whose argument requires
the conditions above and obtains simplicity by separation from the new
spectrum. This is an assumption gap in that citation, not evidence that
the unrestricted assertion has already been justified. The displayed
recovery corollary itself retains the separating inequality and even a.

**Dembo–McKenzie.**
[The Gaussian Wave for Graphs of Finite Cone Type,
arXiv:2603.04386v1](https://arxiv.org/html/2603.04386v1), Definition 1.6,
Theorem 1.8, discussion immediately following it, and Section 3. This is
particularly relevant prior work: its degree-matrix model contains the
two-block RSBM, and its multitype star/edge entropy counting framework is
close to the enumeration used here. However, it explicitly permits
exceptional planted eigenvectors and explains why individual
eigenvectors cannot generally be controlled. Its generic theorem samples
an eigenvector from a shrinking window, and its covariance assumption
cannot be silently imposed on an arbitrary fixed planted eigenspace. No
finite-field logarithmic-nullity or Boolean-recovery conclusion appears.

**He–Huang–Wang.**
[Bulk universality of random regular graphs,
arXiv:2610.08127v1](https://arxiv.org/html/2610.08127v1), main theorem and
Theorems 1.1–1.2. These theorems concern the uniform simple regular law.
The paper contains no planted/equitable model application. Its
uniform-model conclusions cannot be transferred to a prescribed
equitable partition merely by conditioning: that event has exponentially
small probability. This is a model distinction, independent of the
strength of its uniform-model conclusions.

## Specifically requested OpenAI/math inspection

I downloaded both complete primary PDFs and searched their full extracted
text, then read their model statements, main theorems, and entropy
counting sections:

1. [GOE bulk universality for fixed-degree random regular graphs,
   September 23,
   2026](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/GOE-bulk-universality-for-fixed-degree-random-regular-graphs-September-23-2026/paper.pdf).
2. [Fixed-energy universality for weak Anderson disorder on random
   regular graphs, October 5,
   2026](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Fixed-energy-universality-for-weak-Anderson-disorder-on-random-regular-graphs-October-5-2026/fixed-energy-universality-weak-anderson-disorder-random-regular-graphs.pdf).

Neither full text contains the terms RSBM, equitable, planted, Barucca,
finite field, or nullity. Their occurrences of “kernel” refer to
analytic kernels or auxiliary linear-map kernels; their recovery wording
concerns recovering spectral observables in intermediate arguments.
There is no affine/pivot Boolean-recovery algorithm or logarithmic-
eigenspace trick in either manuscript.

The September manuscript does contain the general colored-star
configuration count, Lemma 3.2, and explicitly credits the
Backhausz–Szegedy framework. Thus that combinatorial entropy framework
should be cited as existing machinery. The manuscript's use is to
derive Gaussian eigenvector moments for uniform regular graphs, rather
than the binary kernel-moment/recovery conclusion here. The October
manuscript adds independent continuous diagonal disorder and adapts the
analytic entropy argument; it also does not claim RSBM recovery.

For an additional bounded check, I searched the complete `preprints/`
filename tree at repository commit
`4eaee87548250b2682affda7d05d947c05554bae`. The API returned 13,578 entries
and `truncated=false`. No filename with the RSBM, equitable, community,
or communities terminology appeared. This filename search is not a
full-content search of every manuscript, so it is not a claim of an
exhaustive repository-wide priority audit. The catalog's family 219 also
describes only regular-graph universality with weak disorder.

Local evidence is retained in `openai-primary-metadata.json`,
`openai-tree-priority-search.json`, the two `openai-*.pdf` files, and
their extracted `.txt` files. The scope comparison is complete; no
sweeping historical-first claim follows from these checks.
