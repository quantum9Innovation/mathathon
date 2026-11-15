# Source audit for the growing-base random-lift target

Audit date: November 15, 2026. This is a bounded search, not a historical priority certificate.

## What is already stated in primary sources

1. Bordenave and Collins, *Eigenvalues of random lifts and polynomials of random permutation matrices*, Annals of Mathematics 190 (2019), pages 811-875, proves the universal-cover spectral approximation for a fixed base graph. [Journal record](https://annals.math.princeton.edu/2019/190-3/p03).

2. Chen, Garza-Vargas, Tropp and van Handel, *A new approach to strong convergence*, Annals of Mathematics 203 (2026), pages 555-602, Theorem 3.9, proves

   \[
   \Pr\{\|P(S_N)\|\geq\|P(u)\|+\epsilon\}
   \lesssim \frac DN\left(\frac{Kq_0\log r}{\epsilon}\right)^8
   \log(eK/\epsilon).
   \]

   Its rational-trace and first-order-support statements are the inputs to the separate generator-free derivation. [Full arXiv v3](https://arxiv.org/html/2405.16026v3), [journal record](https://annals.math.princeton.edu/2026/203-2/p04).

3. Chen, Garza-Vargas and van Handel, *A new approach to strong convergence II. The classical ensembles*, arXiv:2412.00593v3, June 6, 2026, Theorem 9.4, improves the fixed-polynomial permutation rate to O_P((log N/N)^(1/6)). Its proof replaces the exponent 4m in the rational interpolation estimate by 3m. An epsilon^(-6) finite tail with the same D/N factor and generator logarithm follows by following that stated proof modification, but it is not separately displayed as a theorem. [Exact current version](https://arxiv.org/html/2412.00593v3#S9.SS2).

4. Bordenave and Collins, *Norm of matrix-valued polynomials in random unitaries and permutations*, arXiv:2304.05714v2, January 10, 2024, Theorem 1.4 and Corollary 1.5, permits coefficient dimension as large as N^(sqrt(log N)), with at most sqrt(log N) independent permutation generators in that corollary. Thus a linear barrier on arbitrary coefficient dimension would be false. A base with m independent edge permutations has generator count of order m and is outside that regime. [Primary PDF](https://arxiv.org/pdf/2304.05714v2).

5. Oliveira, *The spectrum of random k-lifts of large graphs (with possibly large k)*, arXiv:0911.4741, treats arbitrary growing bases but has an upper scale O(sqrt(Delta log(km))). This does not give the universal-cover edge for fixed degree. [Primary record](https://arxiv.org/abs/0911.4741).

6. Addario-Berry and Griffiths, *The spectrum of random lifts*, arXiv:1012.4097, and Lubetzky, Sudakov and Vu, *Spectra of lifted Ramanujan graphs*, arXiv:0911.4148, are adjacent older work. Their growing-base and degree dependencies should be distinguished from a sharp 2sqrt(d-1)+o(1) bound. [Addario-Berry and Griffiths](https://arxiv.org/abs/1012.4097), [Lubetzky, Sudakov and Vu](https://arxiv.org/abs/0911.4148).

## The candidate additional statement

The new proof file derives a bound C(m/N)(Delta/epsilon)^9 for every deterministic finite connected loopless base of maximum degree Delta. This gives the sharp universal growing-base scale m=o(N), if paired with the separately proved connected cubic obstruction at m of order N.

The algebraic change is small: use the color-count bound floor(q/(j+1)) in the common denominator and sum the resulting logarithmic degree loss through one extra smooth derivative. This is strongly dependent on the published polynomial method. It is more accurate to describe the work as a parameter refinement and sharp growing-base consequence than as an independent new method.

The displayed Theorem 3.9 alone gives only m(log m)^8=o(N) for bounded-degree bases at a fixed positive error. Theorem 9.4's proof improves that to m(log m)^6=o(N). Removing those generator logarithms is what changes the full base-growth range. This comparison is about the displayed bounds, not a claim that the sharper corollary was unknown to their authors.

## Search coverage

The targeted web queries included:

- random lifts growing base spectral
- random lifts growing base graphs
- random lifts size of the base graph
- random lifts base size eigenvalue
- random lifts o(N) base
- random lifts o(n) base eigenvalues
- random lifts m=o eigenvalue
- random lifts m = o spectral
- random lifts sublinear base graphs eigenvalues
- random permutations number of generators uniform norm convergence
- strong convergence number of permutations growing
- random lifts necklace spectral
- random lifts parallel edges tangles outliers

No exact statement of the generator-independent tail or the uniform sharp m=o(N) theorem was identified in the inspected sources. No exact duplicate of the proposed connected necklace obstruction was found. The classical tangle mechanism and the optimal order 1/N fixed-base tail are established prior work, including the staircase theorem in the Chen et al. paper. An independent reconstruction of an elementary consequence does not establish priority.

The search did find several unrelated 2026 pages and local-law papers. They were not used as proof inputs. The broad keyword searches are not exhaustive citation tracing. A publication-level priority audit should inspect citations to the 2026 polynomial-method papers and ask whether the generator-independent reformulation has been stated in talks, preprints, or private notes. No external correspondence was performed.

## Preserved primary files

The following were downloaded directly from the listed author or arXiv URLs:

| File | URL | SHA256 |
| --- | --- | --- |
| CGVTvH-2026.pdf | https://tropp.caltech.edu/papers/CGV%2B26-New-Approach.pdf | 490f68343ed4dad57777855500d38c748f2a98ab1141105af88e00d896af02a3 |
| CGVTvH-I-v3-source.tar.gz | https://arxiv.org/src/2405.16026v3 | e0b51d433a7d26f071d22373d07651a894a7c61cb5bf293e23b500175b69f869 |
| CGVTvH-I-v3-source/strongcv.tex | extracted from preceding archive | a8aae7fc21d6abe98dc177849a9fcff3768bce74e25a84debb5a6e78833dc440 |
| CGVvH-II-v3.pdf | https://arxiv.org/pdf/2412.00593v3 | e8a2bf967f3c6eed02079128328c980ed4a646fdf95b1de7854124a454d2f3c3 |

Complete HTML for the two Chen et al. papers and the complete source archive for Bordenave and Collins 2304.05714v2 are also retained. The initial author-hosted II PDF has 52 pages and predates the latest 53-page arXiv v3, so the latter is the version used for the current theorem audit. A missing local pdftotext executable was bypassed by retaining full TeX and HTML.
