ODD-BLOCK RSBM PROOF PACKET -- 2026-11-15
=======================================

Result supplied
---------------
The assembled theorem covers every fixed d1>d2>0 with d1>=3 and every
admissible block size N (d1*N even). In particular it removes the odd-N
restriction for every even internal degree d1>=4, including d1=4.

For two independent uniform simple d1-regular internal graphs and ANY
fixed simple d2-regular cross biadjacency B,

   sup_B P(dim_R ker([C B; B^T D] - (d1-d2)I) >= 2) -> 0.

Uniformity is over cross graphs chosen independently of the internal
graphs; it does not authorize choosing B after observing those graphs.
An independent random uniform-simple cross graph is included. The known
planted sign vector is therefore the entire real kernel with high
probability; exact rational elimination gives polynomial-bit-complexity
recovery without an outlier gap.

No effective failure rate or historical novelty is certified. The
(d1,d2)=(2,1) case remains outside this proof. The old even-block proof
and all previously frozen frontier artifacts are unchanged.

Start here
----------
configuration-mixing-and-odd-blocks.pdf / .tex         6 pages
  Exact theorem, proof map, full strong-mixing assembly, two-block
  first moment, uniform-cross-graph argument, simplicity conditioning
  and recovery. Final source SHA256:
  2a2856c86d37c78a2a29bc2a5f67f5df0c5649963809fc32770fe76379cff048

configuration-proof-packet.pdf                       18 pages
  The six-page synthesis followed by all three complete proof notes.
  This concatenation makes the mathematical dependencies readable in
  one file; it is not an additional independent proof.

The central new proof obligation
-------------------------------
For the UNDIRECTED CONFIGURATION adjacency C_n, fixed d>=3 and fixed
odd prime p, let Q_q be the point mass at da*1 for q=a*1, and otherwise
uniform on {r:sum r=d sum q}. The packet proves

   sum_(q in Fp^n) sup_r |P(C_n q=r)-Q_q(r)| -> 0,

along ALL admissible sizes dn even. Loops contribute two on the
diagonal. This is a summed maximum-atom estimate over every target,
not an unshifted nonsingularity statement and not merely typical-input
mixing. No prime grows with n. Divisibility p|n or p|d is permitted;
the final two-block argument chooses p odd with p not dividing d2.

Three complete companion arguments
----------------------------------
1. parity-reduction/nearconstant-configuration-atoms.tex/pdf (2 pages)
   A direct sequential stub-exposure bound gives, for support size k,
      sup_r P(Cq=r) <= 2^(dk+1)(K_d k/n)^(dk/2).
   Summing nonconstant inputs within eta*n of a constant gives
   O_(d,p)(n^(1-d/2)). It covers arbitrary outputs and admissible parity.
   Final source SHA256:
   5f041c74739d9e8e8cc56944e6906995b3f0e978c7a58226929713a746aa480c

2. huang-primary/configuration-arbitrary-target-tails.tex/pdf (5 pages)
   Extends the exact tuple-color count to every prescribed output.
   AM-GM gives an all-target entropy rate with only uniform/point-mass
   zeros. A uniform Taylor calculation and compactness yield summed
   polynomially small tails outside a shrinking central profile window.
   Polynomial prefactors and the number of types are counted.
   Final source SHA256:
   46655a70f9c0d39de5e7d45cd4542de1dd0395fae6bc34d3a25020621b6ede6f

3. meszaros-extension/balanced-all-target-configuration.tex/pdf (5 pages)
   Proves a relative, uniform triangular-array local limit estimate by
   exponential tilting. Conditioned d-tuples have common mean/covariance
   for d>=3. Each row has lattice factor p; symmetric type matrices have
   p-1 independent weighted-row congruences. Explicit bounded even-diagonal
   translations show the coset index p^(p-1). The net factor p yields
   p^(-n+1), with all-target central tails controlled.
   Final source SHA256:
   9a1a1d6254cd26829fb8a12e2f4a7cc7b22b19d0657cf73c077b86b13eabf557

How this differs from the primary statements
-------------------------------------------
Mészáros, arXiv:1806.03736v4 (2020), Theorem 1.6, proves this style of
strong mixing for a sum of perfect matchings on EVEN n. Huang,
arXiv:1807.06465v2 (2018), Theorem 1.1(1.2), proves a ZERO-TARGET kernel
first moment for the configuration model, allowing odd n when d is
even. Neither stated theorem is silently treated as an arbitrary-shift
or odd-size all-target theorem. The exact enumeration, entropy adaptation,
uniform relative local limit and lattice argument are explicitly proved
in these companions.

Primary URLs and precise source-scope reading notes:
  https://arxiv.org/pdf/1806.03736v4
  https://arxiv.org/pdf/1807.06465v2
  huang-primary/PRIMARY_SCOPE_AND_AUDIT.md
  huang-primary/SOURCE_MANIFEST.json

Independent reviews
--------------------
The main synthesis has independent, actual-source reviews bound to its
final hash in the three child directories; see their *SYNTHESIS* audit
files. The balanced note was independently reconstructed by the primary
session and both other children. The entropy note was reconstructed by
the primary session and the central-note author. The nearconstant note
was reconstructed by the primary session and the entropy-note author;
its final hash differs from its earlier audited hash only by scope-text
formatting, with a delta review retained.

Audits check the supplied mathematics and scope. They do not certify
historical firstness or substitute for the parent thread's own review.

Exact corroboration
--------------------
huang-primary/check_configuration_counts.py and its JSON enumerate all
10,395 pairings for each of (n,d,p)=(3,4,3) and (4,3,3). Across 12
inputs, all 2,970 target/type coefficient cases agree exactly.

meszaros-extension/check_balanced_exact.py and two JSON outputs count
configuration types with exact integers. Forty-four examples include
odd n through 81 at d=4,p=3 and p|d examples through n=84 at d=3,p=3.
Targets include zero, constants, r=q and targets varying within a
single input-color class. Counts corroborate the leading factor p.
These computations are not asymptotic proofs or algorithm benchmarks.

Independent fallback proof
--------------------------
parity-reduction/odd-blocks-degree-six-surgery.tex/pdf (5 pages) gives
a separate matching-core vertex-insertion proof for odd N and even
d1>=6. It is not used in the main all-d1>=3 theorem. Its direction of
contiguity and simple-output/old-loopless conditioning are explicitly
checked; it does not cover d1=4 by itself.

Reproduction and integrity
--------------------------
build.sh rebuilds all four main proof notes and concatenates the
18-page packet. It also rebuilds the separate surgery proof.
SHA256SUMS.txt covers the final files in THIS subdirectory. The older
frontier packet's manifest is left frozen and is not rewritten.
