# Formal scope audit for the close-pair packet

Date: November 15, 2026, America/Los_Angeles.

Disposition: accepted as the finite components stated below. The fresh compile and axiom checks passed. No placeholder proof, custom axiom, or hidden assumption of the final spectral conclusion was found. The subcritical random-graph theorem and close-pair transition are not formalized end to end.

## 1. Exact revision and reviewer exposure

The reviewer read all four Lean source files, the validator and the final README. The reviewer did not author these formal sources. Prior exposure includes discussion of the finite averaging and far-row identities, authorship of the paper Chebyshev upper proof and review of the paper nonbacktracking upper proof. This is an independent implementation and scope audit with that exposure declared, not independent discovery of the underlying identities.

| Reviewed item | SHA256 |
| --- | --- |
| SOURCE_MANIFEST-v1.json | a656f70c2fb4d79f8d4ccd729f900681b41ccb18bc4759c5927c3a27a0ac8785 |
| source-v1/FiniteSampling.lean | fec583759e2d47b1d32615b4761ce98493319a0688b3607c4b338f0cb9a091b8 |
| source-v1/PairWitness.lean | 08d88773347ec807275e38e1ca629230f52365f88569fea2774f1ccb06f7d288 |
| source-v1/FarRowBound.lean | 6ae991fe25dde188944cd4ce38086bd7d7c2a8c6654cff341771515575f02e4a |
| source-v1/SchurWitness.lean | fba67cd48d1969928b75e54391c7ce6d6d041b7eeaa5cf91a3769cb20d26e5fc |
| validate.py | 2ed86e25dbaa94b5156420fb37af9f8da366976590e1fef1cec1c32d4b2a814c |
| README.md | ccdce224cbeba0d5cc0ca32aa5245acee0ff4420d3ae558f3bb3abdb13c884f7 |

The manifest also binds the toolchain, package configuration and dependency manifest. No formal source or author validation file was edited during this audit.

## 2. Actual finite sampling, without an assumed pair probability

FiniteSampling works with the actual finite set of all m-element subsets of Fin n. It proves the number of those subsets containing a given distinct pair by a finite combinatorial count. That count is binomial(n-2,m-2), rather than an assumed inclusion probability.

The source then exchanges finite sums over subsets and ordered distinct pairs, proves the binomial ratio and normalizes by the actual number binomial(n,m). The final theorem states, for 2<=m<=n and an arbitrary real array K,

\[
 \frac1{\binom nm}\sum_{|S|=m}\sum_{i,j\in S,\ i\ne j}K_{ij}^2
 =\frac{m(m-1)}{n(n-1)}\sum_{i\ne j}K_{ij}^2.
\]

Both sides count ordered pairs, so there is no missing factor of two. The denominator is proved nonzero from 2<=m<=n. The general arbitrary-weight identity is proved first, and squares are a specialization. The assumptions m>=2 and m<=n are explicit. The m=0 and m=1 formulas are not included in this theorem.

This is an actual deterministic sampling identity. It does not encode a random graph distribution or prove that predetermined coordinates in an exchangeable random graph have the same average. That latter step remains the written graph-law argument. The README describes this boundary accurately.

## 3. Far-row stationary correction

FarRowBound defines the actual constant matrix P_ij=1/n. Given actual real matrices with R=T-alpha P+W and zero T entries on an arbitrary finite row-coordinate set S, it proves

\[
 \sum_{j\in S}R_{cj}^2
 \le2\sum_jW_{cj}^2+2\alpha^2/n.
\]

The proof derives the entry identity, the elementary square inequality, the enlargement from the subset row sum to the full row sum, and the cardinality bound |S|<=n. It assumes n positive for the division. No sign assumption on alpha is needed.

The decomposition and zero-entry hypotheses are appropriate inputs to this algebraic lemma. They do not assume the row-energy conclusion. However, no graph polynomial, graph distance or approximation procedure is defined here. Finite propagation, the construction of T and W, and the operator bound on W remain application bridges.

## 4. The actual symmetric pair vector

PairWitness constructs y=e_a+e_b from actual coordinate vectors. For distinct a,b it proves y is nonzero and has squared norm two. The matrix used in the test is explicitly F=2zI-z squared G+H.

The exact pair quotient has diagonal term minus z squared times the average of G_aa and G_bb, and cross term minus z squared G_ab. The equality G_ba=G_ab is explicit. The four selected H entries are explicitly zero. These are the needed local matrix hypotheses, rather than an implicit assumption of global symmetry.

The lower bounds on those three G entries imply the stated scalar upper bound because z squared is nonnegative. A strict negative value of that scalar upper bound then proves a negative pair quadratic form. The code uses the symmetric plus vector, not an antisymmetric vector with the wrong sign for a positive cross interaction.

The scalar threshold is an explicit sufficient inequality to be verified by the application. It is not an assumed augmented eigenvalue conclusion. The tree Green lower bounds, choice of distance and scale, and eventual negativity of that threshold remain outside the formal file.

## 5. Concrete augmented Schur witness

SchurWitness constructs the actual block matrix with blocks A, B, B transpose and zero. For an invertible zI-A, the final theorem uses the actual inverse and defines

\[
 x=(zI-A)^{-1}By,\qquad v=(x,y).
\]

It proves the exact quadratic identity

\[
 z\|v\|^2-v^\top\mathcal Av
 =y^\top\left(zI-B^\top(zI-A)^{-1}B\right)y.
\]

A negative right side gives both v nonzero and a strict augmented Rayleigh inequality. Thus the vector being used is constructed, and its nonzero property is proved. An unspecified desired eigenvector is not assumed.

The quadratic identity itself does not need A to be symmetric. Accordingly, the formal conclusion is the strict quadratic inequality, not a largest-eigenvalue statement. Applying the variational principle to the actual symmetric graph adjacency remains unformalized. The source also does not identify its full Schur matrix with the pair-test matrix from PairWitness. The README explicitly records both bridges.

## 6. Inspected validator and fresh replay

The validator was inspected before running it. It checks all frozen source hashes, Lean 4.31.0, and every pinned dependency checkout revision. It compiles the four files in the manifest order, using two threads, a 4096 MB memory setting and a 120-second timeout per source. Temporary local compiler output is first on the import path. It requires warning-free success and an axiom report for every declared theorem.

The accepted axiom list contains only propext, Classical.choice and Quot.sound. All 20 new declarations passed this check. The source inspection and validator found no sorry, admit, custom axiom or unsafe declaration.

A fresh replay used a copy of the frozen packet in /tmp/spectral-close-pair-formal-yx90cr_x. It finished on November 15, 2026 at 09:01:13 UTC, corresponding to 01:01:13 Pacific. The receipt hash is

`79c8244228699a08e52b4739fa5f466eeb9a878b14c05084a0bc143d935f389c`.

That receipt records six sampling theorems, six pair-witness theorems, two far-row theorems and six augmented-witness theorems. The source bindings match the reviewed manifest. The replay left the author validation output untouched.

The installed compiler and dependency caches are trusted inputs. The caches were not rebuilt from source, and revision checks do not cryptographically verify every compiled library object. This was a fresh compile of the supplied component sources against the recorded cached dependencies.

## 7. Remaining graph and analytic bridges

The formal packet does not prove graph-law exchangeability, the nonbacktracking recurrence or two-walk collision bound, graph separation probabilities, the polynomial approximation, finite propagation, the tree Green estimates, host inverse existence, Taylor error bounds, the identification B=AE with the exact pair Schur matrix, or the final symmetric-matrix variational conclusion. The limiting probabilities and spectral transition remain paper-proof results.

No correction is required at the stated formal scope. These 20 declarations are new finite components, separate from the prior packet's 27 declarations. Neither number is a count of new research theorems or an end-to-end formalization certificate.
