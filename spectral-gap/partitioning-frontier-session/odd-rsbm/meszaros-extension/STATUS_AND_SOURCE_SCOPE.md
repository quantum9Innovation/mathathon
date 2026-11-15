# Odd-block mixing extension: status and source scope

The useful route found in this session is a direct undirected configuration
proof. The standalone result
[`balanced-all-target-configuration.tex`](balanced-all-target-configuration.tex)
proves uniform all-target point mixing for balanced inputs, for every fixed
d≥3 and odd prime p, along every admissible dn-even subsequence. It includes
odd n when d is even, particularly d=4. It is a five-page proof, not an
assertion that the original matching theorem already covers odd n.

The source is frozen at SHA256
`9a1a1d6254cd26829fb8a12e2f4a7cc7b22b19d0657cf73c077b86b13eabf557`.
The parent and literature agent independently reviewed the complete actual
source and reported mathematical PASS. Two final PDF builds were clean.
The proof gives the entire balanced-input contribution o(1) to the sum of
maximum-atom errors. Combining it with the other agents' nearconstant and
quantitative entropy tails is a separate integration step.

`check_balanced_exact.py` corroborates the count interface using exact
integer arithmetic, without sampling or floating-point row probabilities.
It enumerates all symmetric, even-diagonal configuration types and exact
row generating coefficients. In 24 d=4,p=3 examples, all n are odd. Twenty
additional d=3,p=3 examples check that the no-coprimality scope is plausible.
Every baseline type count sums exactly to (dn−1)!!. The JSON records also
show target dependence at finite size; no monotonicity or effective
asymptotic rate is inferred from these examples.

## What was inspected in the primary sources

- [Mészáros, arXiv:1806.03736v4](https://arxiv.org/html/1806.03736v4):
  model definitions, affine/tensor restrictions and Theorems 1.5–1.6;
  Section 2's typicality definitions; the counting/lattice/translation
  portion of Section 3; Section 7's matching count, typical-input argument,
  entropy reduction and the stated non-typical modifications. This was a
  targeted proof inspection, not a fresh read of every page of the paper.
  The source's undirected model is a sum of perfect matchings and requires
  even n. Its strong unscaled sum of maximum-atom errors cannot be
  replaced by an ordinary nonsingularity theorem.
- [Huang, arXiv:1807.06465v2](https://arxiv.org/pdf/1807.06465v2):
  Proposition 2.2's undirected labelled-stub count, the mean/covariance
  and character restrictions in equations (2.11)–(2.14), and the Section
  4.1 local-limit calculation. The original target is zero; the
  arbitrary-target triangular-array extension is proved in this note.
- [Greenhill–Janson–Kim–Wormald, *Permutation pseudographs and
  contiguity*](https://web.maths.unsw.edu.au/~csg/papers/gjkw-revised.pdf):
  definitions, Theorems 1.1–1.3 and Corollary 1.1, author PDF pages 1–5.
  Theorem 1.1 with θ₁=θ₂=1 explicitly covers degree four. Theorem 1.3
  covers any fixed sum of at least two permutation pseudographs, and its
  graph restriction is contiguous with uniform simple regular graphs.
  Thus degree-four contiguity is not an exceptional missing theorem.

The final configuration route needs no permutation-model contiguity to
transfer a high-probability event to the uniform simple model: condition
the configuration model on simplicity, whose probability stays bounded
away from zero for each fixed degree. Moment identities themselves must
not be transferred by qualitative contiguity without further work.

## Unfinished symmetrized-permutation route

For one uniform permutation π, put y_i=q_{π(i)} and z_i=q_{π⁻¹(i)}.
There is an exact elementary count:

    P(y=Pq,z=Pᵀq)=∏_{a,b} m_(q,y)(a,b)!/n!,

provided m_(q,y)(a,b)=m_(q,z)(b,a) for all a,b, and the probability is
zero otherwise. The proof matches source vertices of type (q_i,y_i)=(a,b)
to target vertices of type (z_j,q_j)=(a,b). For independent permutations,
these factors multiply. Their leading entropy exponent agrees with the
matching exponent because the paired two-variable entropies are equal
under transposition. This is a useful count, but the global strong-mixing
proof for that model was not completed here. No such theorem is claimed.

The direct configuration proof avoids that additional model extension.
Historical novelty of the combined odd-block result still requires a
separate primary-literature priority check.
