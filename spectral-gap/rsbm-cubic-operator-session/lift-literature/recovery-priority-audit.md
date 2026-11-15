# Primary-source priority audit for cubic polynomial recovery

Checked on 2026-11-15. This is a bounded literature audit, not a guarantee
that no earlier result exists. Searches covered the RSBM and equitable
graph terminology, prescribed-eigenvalue multiplicities, finite-field
rank/nullity, low-dimensional Boolean-kernel enumeration, and perfect
matching cuts in cubic graphs.

## Conclusion

I found no earlier **proved** polynomial-time exact-recovery theorem for
the uniform-simple `(d1,d2)=(2,1)` RSBM, nor the specific polynomial-kernel-
moment to logarithmic-nullity argument. The existing spectral recovery
idea and the planted adjacency eigenvector are clearly prior work. The
deterministic pivot-coordinate enumeration of Boolean vectors in a
logarithmic-dimensional rational subspace is elementary and should not be
presented as a novel algorithmic primitive.

The defensible contribution of the current derivation is the rigorous
logarithmic nullity bound for this exact ensemble, combined with a
rigorous Boolean-rigidity bound to complete polynomial recovery. Until a
wider expert review, say that this proves the stated special case and
avoid an unqualified historical-priority claim.

## 1. Brito–Dumitriu–Ganguly–Hoffman–Tran

[Recovery and Rigidity in a Regular Stochastic Block Model,
arXiv:1507.00930v4](https://arxiv.org/pdf/1507.00930v4), PDF p. 2,
imposes `min(d1,d2)>=3` for the rest of the article. Its efficient
recovery statement is in the spectral separation regime; see the
statements near the beginning and the Section 4 argument. Thus its
rigidity and efficient-recovery results do not prove the cubic `(2,1)`
case. The latest version of this primary source is substantially more
precise about its degree range than some later informal summaries.

## 2. Barucca's exact-recovery proposal and conjecture

[Spectral partitioning in equitable graphs, Physical Review E 95,
062310 (2017)](https://lims.ac.uk/wp-content/uploads/barucca2017spectral-1.pdf),
Section IV.A, PDF pp. 5–6, proposes identifying the planted eigenvector
using its inverse participation ratio. It explicitly gives the broader
efficient-full-recovery claim as a conjecture and says the rigorous
parameter region remains restricted. Its numerical figures include
`c=3,r=2`, precisely the within/cross degrees `(2,1)` considered here.
Therefore even this narrow parameter case had already been numerically
demonstrated and conceptually proposed for spectral recovery. It contains
no rigorous logarithmic-dimensional eigenspace bound or pivot-sign
enumeration argument.

## 3. The 2026 Zhu–Zhu paper

[Non-backtracking eigenvalues and eigenvectors of random regular graphs
and hypergraphs, arXiv:2312.03300v3](https://arxiv.org/abs/2312.03300v3)
and its [journal version](https://www.sciencedirect.com/science/article/abs/pii/S0012365X26004747)
say the full efficient exact-recovery conjecture remains open. Their
proved application uses the separating condition
`(d1-d2)^2>4(d1+d2-1)`; `(2,1)` violates it. Their Lemma 9.1 asserts
unrestricted planted-eigenvalue simplicity but cites Brito et al.,
Section 4, which does not supply that unrestricted assertion. This
citation cannot replace the argument required here. The contemporaneous
open-problem statement is supportive context for priority, but does not
by itself establish that every individual special case was open.

## 4. Earlier algebraic distinguishing is not recovery

[Bandeira–Banks–Kunisky–Moore–Wein, Spectral Planting and the Hardness of
Refuting Cuts, Colorability, and Communities in Random Graphs, COLT
2021](https://proceedings.mlr.press/v134/bandeira21a/bandeira21a.pdf),
Remark 3, PDF p. 7, explicitly recognizes polynomial-time distinguishing
of the noiseless equitable model at all parameters by exploiting the
planted eigenvectors, with a citation to Barucca. This is important prior
work for the algebraic viewpoint. The remark states distinguishing, not
a proved all-parameter exact-recovery algorithm, and does not give the
finite-field moment/nullity argument used here.

## 5. Distributed averaging results still require spectral separation

[Becchetti–Clementi–Natale–Pasquale–Trevisan, Find Your Place: Simple
Distributed Algorithms for Community Detection](https://par.nsf.gov/servlets/purl/10041976),
Section 3, analyzes averaging when the community eigenvalue dominates the
remaining nontrivial spectrum by a fixed margin. Its RSBM application
therefore does not cover the cubic bulk eigenvalue 1. Some thesis and
survey abstracts use broad language about recovering across the full
permitted range; the primary theorem hypotheses retain a spectral gap.

## 6. General sparse-rank theorems do not immediately subsume this model

[Coja-Oghlan et al., The rank of sparse random
matrices](https://onlinelibrary.wiley.com/doi/full/10.1002/rsa.21085)
determines asymptotic normalized rank for nonsymmetric random matrices
with prescribed row and column degrees. Its model and normalized-rank
conclusion do not provide the needed `O(log N)` nullity bound for the
symmetric shifted, planted-block-conditioned adjacency matrix here.
Consequently it is a methodological relative, not a direct application
that already gives this recovery theorem.

## 7. Perfect matching cuts: avoid an erroneous deterministic shortcut

For a cubic graph, a Boolean eigenvector `Av=v` gives exactly one edge
across the sign cut at every vertex, so its cutset is a perfect matching.
This deterministic equivalence is elementary. Ordinary matching cuts in
subcubic graphs are easier, but they need not meet every vertex and are
not the target here.

[Bonnet–Chakraborty–Duron, Cutting Barnette graphs perfectly is
hard](https://perso.ens-lyon.fr/edouard.bonnet/publi/pmc-barnette-journal.pdf)
prove NP-completeness of Perfect Matching Cut even for 3-connected cubic
bipartite planar graphs. Thus there is no existing generic polynomial
algorithm for all cubic inputs to which one could reduce this planted
case without an additional probabilistic or structural argument. This
worst-case result is entirely compatible with polynomial recovery in the
present random ensemble.

## 8. Lift literature remains insufficient

[Bordenave–Collins, Eigenvalues of random lifts and polynomials of random
permutation matrices, Annals of Mathematics 190
(2019)](https://annals.math.princeton.edu/2019/190-3/p03)
proves strong asymptotic freeness and global spectral location. The
target eigenvalue 1 lies inside the cubic-tree spectral band, so those
conclusions give no prescribed-point collision bound.

[Huang–Xu, Local Law and Eigenvector Delocalization for Random Lifts,
arXiv:2610.37463v1](https://arxiv.org/html/2610.37463v1)
assumes a fixed connected simple base graph of minimum degree at least
three. Theorems 1.2–1.3 give mesoscopic counting and delocalization, not
bulk universality or exact collision exclusion. The two-vertex quotient
with internal loops is outside its written simple-base hypotheses.
Furthermore, an oriented-permutation 2-factor ensemble needs the explicit
change-of-measure analysis in `permutation-to-uniform-transfer.md`; it is
not contiguous to the uniform simple 2-factor law.
