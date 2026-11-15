# RSBM source audit: planted-eigenvalue simplicity

Checked 2026-11-15. This is a source audit and a logical assessment of applicability, not a proof that in-bulk simplicity holds or fails. Set total degree d=d1+d2 and planted eigenvalue λ=d1−d2. The task's N is the size of each block.

## 1. Zhu–Zhu v3: exact model, restricted theorem, overbroad lemma

Primary source: [Zhu–Zhu, arXiv:2312.03300v3, September 25, 2026](https://arxiv.org/html/2312.03300v3).

- Definition 3.9 is exactly the task's model: two equal blocks; independent uniform simple d1-regular internal graphs; uniform d2-regular bipartite cross graph. Their n=2N.
- Section 1.3 explicitly reports the full efficient exact-recovery conjecture for d1>d2>0 as open.
- Theorem 3.10(3) and Corollary 3.11 assume d1 even and λ²>4(d−1). Remark 3.12 calls removal of the parity restriction future work.
- Lemma 9.1, read literally, asserts simplicity of d and λ without those qualifications. Its proof cites only Brito et al., Section 4, the random-lift spectral bound, and contiguity. That argument does not establish in-bulk simplicity. Treat this lemma as missing scope, rather than as a solution of the conjecture.
- The deterministic quadratic relation is μ²−λμ+d−1=0. Passing to reduced non-backtracking matrices preserves the collision issue at an interior planted adjacency eigenvalue.

The conflict is internal: blanket simplicity plus exact rational nullspace computation would already imply the recovery conjecture that their introduction calls open.

## 2. Recovery and Rigidity: what its proof actually establishes

Primary source: [Brito–Dumitriu–Ganguly–Hoffman–Tran, arXiv:1507.00930v4](https://arxiv.org/html/1507.00930v4).

- Definition 1 matches the same uniform component model, with 2n vertices.
- Theorem 2 assumes d1 even and λ²>4(d−1), and proves efficient strong recovery.
- Section 4 explicitly assumes even d1 throughout. Its two-vertex base has d1/2 loops at each vertex and d2 parallel cross edges. The quotient eigenvalues are d and λ.
- The proof identifies these old eigenpairs and bounds the new eigenvalues in absolute value by 2√(d−1)+ε. It then invokes λ>2√(d−1) to obtain separation and compute the second eigenvector.
- Thus the cited proof has no mechanism to rule out a new eigenvalue exactly equal to an old eigenvalue in the bulk.
- Theorem 1 proves uniqueness only for sufficiently large degrees d1>d2>d0. Theorem 3's majority amplification assumes d1>d2+4. Neither covers (2,1).

## 3. Barucca: conjecture, not an in-bulk nonsingularity theorem

Primary source: [Barucca, arXiv:1610.02668v5 / Phys. Rev. E 95, 062310 (2017)](https://arxiv.org/html/1610.02668v5).

The homogeneous two-community equitable ensemble fixes each vertex's internal and cross degrees. Section IV conjectures full efficient recovery as soon as c_in>c_out>0. Its algorithm examines inverse participation ratios across adjacency eigenvectors; the community vector has minimum possible IPR 1/n. The evidence is analytical and numerical; it does not prove the planted eigenvalue is simple throughout the bulk, nor resolve possible degeneracy-dependent choices of eigenbasis. It cites the restricted high-degree uniqueness result above. Therefore one should attribute this conjecture to the source and avoid an unsupported historical novelty claim about the nullspace observation.

## 4. Critical degree-two contiguity exception

Primary source: [Greenhill–Janson–Kim–Wormald, Permutation pseudographs and contiguity (2002), author PDF](https://web.maths.unsw.edu.au/~csg/papers/gjkw-revised.pdf).

Theorem 1.3 requires total degree ≥3. Page 5 says distinct F_n(θ) degree-two models are not contiguous: F_n(1) is the permutation model; F_n(1/2) is the configuration model. After conditioning on simplicity, the former weights each 2-factor by 2^{number of cycles}, whereas the latter is uniform. Thus the internal degree-two block cannot be replaced by a single permutation lift. The separated theorem avoids this case. A similar cycle-weight check is needed for a degree-two bipartite union of matchings; this source's theorem is undirected.

## 5. Latest random-lift local law does not fill the gap

Primary source: [Huang–Xu, arXiv:2610.37463v1, October 27, 2026](https://arxiv.org/html/2610.37463).

The paper concerns N-lifts of a fixed connected **simple** base with minimum degree at least 3. Theorems 1.2–1.3 give eigenvalue counting on intervals of length at least (log N)^C/N and complete delocalization away from singular energies of the universal-cover measure. Theorem 4.2 is the corresponding local law. It does not state shifted nonsingularity, simple spectrum, or disjointness of old and new eigenvalues. Moreover, the two-vertex RSBM base has loops and parallel edges, outside the stated base assumptions.

Even with an extension to that base, these estimates would allow finitely many exact collisions. At resolution (log N)^C/N, changing one eigenvalue multiplicity by one is smaller than the allowed counting scale. Delocalization also permits a second, extended eigenvector at λ.

## 6. Latest fixed-degree RRG universality is for the uniform ensemble

Primary source: [He–Huang–Wang, arXiv:2610.08127, October 2026](https://arxiv.org/html/2610.08127).

The paper studies the adjacency matrix of a uniform simple d-regular graph, for each fixed d≥3. Its main theorem gives fixed-energy bulk point-process convergence to Sine_1; Theorem 1.1 gives gap and fixed-energy correlation universality. It does not state these results for general random lifts or RSBM.

For the uniform regular ensemble, fixed-energy point-process convergence implies that the probability of an eigenvalue at any specified interior bulk energy tends to zero: dominate the exact-equality event by a shrinking microscopic neighborhood and use that Sine_1 has no atom at a deterministic point. RSBM has an eigenvalue exactly λ deterministically. Hence this result itself rules out a contiguity argument from uniform RRG to RSBM in the in-bulk setting. One would need a universality or anti-concentration theorem for the *new* spectrum of the planted ensemble.

## 7. Classical nonsingularity is a different assertion

Primary sources: [Huang, arXiv:1807.06465v2](https://arxiv.org/abs/1807.06465), and [Nguyen–Wood, arXiv:1806.10068v2](https://arxiv.org/html/1806.10068).

Huang proves polynomially small adjacency singularity probability for fixed-degree random directed or undirected regular graphs. Nguyen–Wood analyze adjacency cokernels for sums of independent permutations or perfect matchings and infer nonsingularity. These are assertions at zero for unplanted matrix ensembles. Their stated theorems do not directly cover (A−λI) restricted orthogonally to the forced planted eigenvector.

## Precise remaining barrier

The desired assertion is

    P[ ker(A−λI) ∩ span{1,σ}^⊥ ≠ {0} ] → 0.

Since d≠λ, this is equivalent to simplicity of the forced planted eigenvalue. In the loop-lift model it is exclusion of λ from the new spectrum. Bounds on the support, empirical law, mesoscopic counts, or delocalization do not imply it. No directly applicable shifted-nonsingularity theorem was found in the primary sources checked. This is a bounded search conclusion, not a claim that no such theorem exists anywhere.

If the assertion were established for the exact uniform-component model, Gaussian elimination on the integer matrix A−λI gives the planted line in polynomial bit complexity; a macroscopic spectral gap is unnecessary. Thus numerical stability is not an intrinsic Turing-model obstacle to that implication.

## 8. Finite-field route found after the initial audit

Primary source: [Mészáros, arXiv:1806.03736v4, January 28, 2020](https://arxiv.org/html/1806.03736).

Theorem 1.6 is stronger than adjacency nonsingularity: for C_N equal to the sum of r≥3 independent uniform perfect-matching matrices on **even** N, and any fixed finite abelian V,

    Σ_{x∈V^N} max_z |P(C_N x=z)−P(U_x=z)| → 0.

Here U_x is uniform on the explicitly specified affine support R^S(x,r). For V=Fp, p odd, and x nonconstant, the support is simply {z:Σz=rΣx}; the extra symmetric tensor condition is vacuous in this one-dimensional odd-characteristic case. Section 1 expressly limits this matching model to even N. The theorem does not state a signed/multitype result, but the following two-block deduction uses it directly.

### Consequence for r=d1≥3 and even N (deduction)

Fix any N×N cross matrix D with row and column sums d2. D can be deterministic; it need not be sampled from a permutation model. Let C1,C2 be independent copies of C_N, independent of D, λ=d1−d2, and

    M = [[C1−λI, −D], [−D^T, C2−λI]].

This is diag(σ)(A−λI)diag(σ). Fix odd p not dividing d2. Put t=p^{−(N−1)} and let e(x) be the maximum probability error in Theorem 1.6; ε_N=Σ_x e(x)=o(1).

For nonconstant x,y, the equations M(x,y)=0 are

    C1 x=λx+Dy,      C2 y=λy+D^T x.

Their sum constraints force Σx=Σy. Each conditional probability is at most t+e(x), respectively t+e(y), and independence permits their product. Summing over pairs with equal sums gives at most

    p + 2 ε_N + ε_N².

Indeed, there are p^{2N−1} pairs with equal sums; each x has p^{N−1} possible y with the required sum. This bound can overcount constants harmlessly.

If x=a1 and y is nonconstant, the first equation requires Dy=d2 a1, hence Σy=Na. There are at most p^{N−1} such y. The second probability is at most t+e(y), so this sector contributes at most p+pε_N after summing over a. The other one-constant sector has the same bound. Both-constant solutions have x=y because p does not divide d2, contributing exactly p. Therefore

    E |ker_Fp M| ≤ 4p+(2+2p)ε_N+ε_N² = 4p+o(1).

Real nullity at least two implies nullity at least two over every Fp, by vanishing integer minors. Thus

    limsup_{N→∞, N even} P(nullity_R M≥2) ≤ 4/p.

Letting p tend to infinity through odd primes not dividing d2 proves simplicity with high probability in this matching-block model. The bound is uniform over D, so any independent d2-regular cross ensemble is allowed. The argument does not require a rate uniform in p: N tends to infinity first.

### Transfer to the requested uniform simple internal blocks

Conditioning each fixed-degree matching union on simplicity preserves the conclusion because simplicity has probability bounded away from zero. [Greenhill–Janson–Kim–Wormald, Corollary 1.1](https://web.maths.unsw.edu.au/~csg/papers/gjkw-revised.pdf), applied to d1 degree-one summands, transfers it to uniform simple internal blocks. This includes d1=3: the pseudograph exception targets a loopless configuration model, but its simple conditioning is still uniform cubic.

Hence simplicity follows for the exact requested model when d1≥3 and N is even. No odd-N conclusion follows here. For odd d1, admissibility already forces even N. For even d1, odd N remains separate. The pair (2,1) remains outside Theorem 1.6.

This is a mathematical deduction from a verified source, not a claim that the deduction is historically new. The earlier bounded-search conclusion should be read with this update: an applicable *mixing theorem* does supply substantial recovery regimes even though its headline is sandpile distributions.
