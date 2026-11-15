# Bounded primary-source comparison

Checked November 15, 2026. This is a limited source check, not a proof of
historical priority. The mathematical result in this directory is derived
from the exact finite-field moment argument, not imported from these
papers. No claim of firstness is certified.

## Sources actually inspected

[Bordenave and Collins, Eigenvalues of random lifts and polynomials of
random permutation matrices, Annals of Mathematics 190 (2019)](https://annals.math.princeton.edu/wp-content/uploads/annals-v190-n3-p03-s.pdf).
I inspected the abstract, setup of the constant-vector complement,
Theorem 2, and its explanation by two spectral inclusions. The theorem
gives convergence of the new spectrum to the limiting operator's spectrum
in Hausdorff distance. This does not exclude a new eigenvalue exactly at
an old value inside that limiting spectrum. No exact old/new collision
exclusion theorem was identified in the inspected passages. I did not
audit the entire proof.

[Huang and Xu, Local Law and Eigenvector Delocalization for Random Lifts,
arXiv:2610.37463v1 (October 27, 2026)](https://arxiv.org/html/2610.37463).
I inspected the abstract, model, introduction and statements of the main
counting, delocalization and local-law results. They concern a fixed
connected simple base of minimum degree at least three. Counting is at
interval scales at least a power of log(N) divided by N, and the local
estimates permit finitely many exact collisions. The inspected theorems
do not state complete disjointness of old and new spectra. This is an
applicability assessment, not a full proof audit.

[Addario-Berry and Griffiths, The spectrum of random lifts,
arXiv:1012.4097v3](https://arxiv.org/abs/1012.4097).
I inspected the actual arXiv abstract and version metadata. Its stated
results bound the scale of new eigenvalues and relate exceptional large
ones to bounded dense subgraphs. The abstract does not supply the exact
collision assertion. No claim about the full paper follows from this
abstract-only check.

## Search scope and conclusion

Targeted searches included random lifts with old/new disjointness,
prescribed eigenvalues, adjacency invertibility, nonsingularity, simple
spectrum, characteristic-polynomial irreducibility, modular cokernels and
eigenvalue multiplicity. Search results were used only to locate primary
sources; no mathematical input rests on a secondary search summary.

No directly applicable prior theorem was found in the primary passages
actually inspected. This bounded statement must not be promoted to a
claim that the result is new or that no such theorem exists elsewhere.

## Methodological antecedents require explicit credit

[Vontobel, Counting in Graph Covers, arXiv:1012.0065v2](https://arxiv.org/html/1012.0065v2).
I additionally inspected Lemma 29 and Theorem 30 in the primary text.
They give the exact product of vertex multinomials divided by edge
multinomials and identify its Bethe-entropy exponent. Consequently
the star/edge factorial enumerator and its exponential interpretation
must not be described as newly developed here. The present argument
requires the extra exact lattice coefficient and boundary estimates.

[Mori and Tanaka, New Generalizations of the Bethe Approximation via
Asymptotic Expansion, arXiv:1210.2592v2](https://arxiv.org/pdf/1210.2592v2).
I inspected the introduction and Lemmas 15–16 with their hypotheses.
Lemma 16 gives constant-order prefactors for finite nondegenerate Bethe
minima when every minimizing root law and every legal local marginal
is strictly positive. The point phases here violate this condition.
Thus cover Gaussian prefactors are substantial prior art; the printed
lemma does not immediately supply this full irreducible moment or the
resulting exact collision exclusion.

The broader primary review in
[regular-lift-moment-priority.txt](../../../regular-lift-moment-priority.txt)
also credits Mészáros's arbitrary finite-group mixing, Nguyen–Wood's
moment-to-real framework, and Huang's local-CLT and large-deviation
invertibility analysis. That review is separate from the fresh algebra
and module audits in this directory. Historical novelty remains
unasserted for every theorem in this packet.
