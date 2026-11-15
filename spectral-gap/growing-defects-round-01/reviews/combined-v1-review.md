# Separate review of the growing-defect theorem and its probability input

November 15, 2026, America/Los_Angeles.

Verdict: accept the original cubic theorem and the stated weighted fixed-degree extension at the exact revisions below. Every section of the probability proof and assembled graph proof was read. The whole dependency chain was reconstructed, including the previously reviewed deterministic transfer. No unsupported mathematical inference or unresolved integration finding was identified.

This is an internal paper-proof review. It is not end-to-end formal verification, a historical-priority certificate, or external specialist acceptance.

## Exact revisions and exposure

| Input | SHA256 |
| --- | --- |
| [Probability proof v1](../probability/proof-v1.md) | 56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b |
| [Deterministic transfer v1](../root/transfer-v1.md) | deb05e53631ad4d273f48b2d6253014352c1263010d3990ebcc4e0b616351b99 |
| [Graph theorem v1](../root/graph-theorem-v1.md) | b4a00f7b6490590a51e112c99be336e895723f29df4819c68d00dec526a4d2e3 |
| [Separate transfer review](transfer-v1-review.md) | a8f87ea74c8e5efa11f63f33a9d60943c1b1cc55621ff240fd0625807a7456cb |
| [Priority comparison](../priority/PRIORITY-v1.md) | d8fd3d54b5befe8fdf630ee911cb1e3f9a2fe710f499c160e887253474b13e4c |

Prior exposure included the problem packet, SG-17, the integrator's mathematical description of the weighted extension, the priority sources and the deterministic component reviewed earlier. The new probability and graph proofs were first read after the above hashes were supplied. This is a separately reconstructed review with shared target exposure, not access isolation.

No proof file was edited. No simulation was used as a premise. No archived command was executed.

## P1. Host model and external inputs

The exact ensemble is the uniform simple labelled d-regular graph for fixed d>=3 and admissible n. The retained Bordenave journal passage, lines 125 through 165, defines this ensemble and states the two-sided nontrivial spectral bound. Choosing 2sqrt(d-1)<d rho<d gives the required good event. An additional component would give another eigenvalue d perpendicular to the constant vector, so the event also enforces connectedness.

The retained Angel, van der Hofstad and Holmgren passage, lines 180 through 235, gives the regular simplicity probability as exp(-(d-1)/2-(d-1)^2/4)+O(1/n). Its positive limiting value justifies the lower bound on alpha_(n,d). Counting (d!)^n labelled pairings per simple graph confirms that conditioning gives exactly the desired law. The source statements were checked directly. Their complete published proofs were not re-audited.

Zero extension of the restricted inverse off the good event is legitimate for convergence in probability. The argument uses no inverse on a disconnected exceptional graph and no quantitative rate for the good event's failure.

## P2. Single-walk excess and simplicity conditioning

For every configuration multigraph, its universal cover is the d-regular tree when loops are represented by their two distinct incidences. A tree-root return projects to a graph return. Lifting each half-edge walk uniquely identifies an inclusion of return events, so the diagonal excess D_k is nonnegative before averaging.

Before a collision in deferred pairing exposure, the discovered graph is a tree and the lifted discovered walk is injective. Any graph return absent from the tree-return event therefore requires a collision. In k steps there are at most k fresh pairings and k+1 discovered vertices. The number of forbidden partners is at most d(k+1), while the available count at each fresh query is at least nd-2k+1. The resulting bound is at most 2k(k+1)/n for k<=nd/4. Previously exposed edges, loops and parallel edges are handled consistently.

Since D_k>=0, conditioning on simplicity costs at most the reciprocal simplicity probability. No signed expectation is incorrectly conditioned. The factor 2 and the k=0 boundary are correct.

## P3. Off-diagonal identity and matrix norm

The simple-graph law is invariant under permutations fixing one marked label c. Thus E p_k(c,b) is identical for every b different from c. Summing the row gives exactly

\[
\mathbb E p_k(c,b)=\frac{1-\mathbb E p_k(c,c)}{n-1}.
\]

This identity is unconditional under the simple-graph law. It is not applied after conditioning on the spectral event. Bounding it by 1/(n-1) is valid, and dropping the k=0 off-diagonal contribution explains B_(j,L)-1.

The matrix X_(j,L) has nonnegative diagonal entries by the excess-return argument and nonnegative off-diagonal entries by transition positivity. It need not be positive semidefinite. Its Euclidean operator norm is bounded by its Frobenius norm, which is bounded by the sum of its nonnegative entries. Summing the diagonal and ordered off-diagonal expectations gives precisely M_(j,L). No entry independence is required.

The binomial sums in equations (6) and (7) are correct. In particular, k(k+1)=k(k-1)+2k produces the coefficient 2(j+1) in the second term. At j=0 the sum reduces to L(L+1)(L+2)/3, and at L=0 both excess contributions vanish.

## P4. Derivative series, stationary subtraction and operator tails

Differentiating z^(-k-1) j times yields sign (-1)^j and factor j! binom(k+j,j). Replacing A^k by d^k P^k at z=d leaves the factor j!/d^(j+1), exactly as stated.

The projected series subtracts J_m/n at every order k, including k=0. Therefore the finite stationary term has norm m B_(j,L)/n. Omitting its zeroth term would have changed the identity, but the source retains it.

On the good event, P restricted to the constant-vector complement has norm at most rho. Compression by E and Q cannot increase norm. Thus the host tail is bounded by the scalar sum of w_j(k) rho^k without any factor m. The tree tail uses rho_0. The orientation-to-an-end argument supplies the claimed tree adjacency upper norm, which is all the proof needs.

The finite-n probability bound follows from Markov's inequality on the unconditional nonnegative entry sum, plus the exceptional-event probability. It does not require a conditional version of any previous identity. This establishes Theorem 1 for every fixed derivative order, including the stated finite constants.

## P5. Growth range and derivatives

With L proportional to log n, the truncation tails are O((log n)^j n^(-4)), and the expectation bound has orders m(log n)^(j+3)/n and m(m-1)(log n)^(j+1)/n. The stationary term is smaller than the first displayed order. These imply the claimed O_P estimate even though the exceptional-event probability has no rate, because it tends to zero independently of the comparison scale.

For j=0, dividing by s=sqrt(m/n) yields the three terms in equation (29). The central term tends to zero exactly under m^3(log n)^2/n tending to zero. That condition implies m<=n^(1/3) eventually, so the other logarithmic term tends to zero as well. The remaining tail divided by s is at most n^(-7/2). For each fixed j>=1, the same upper bound on m gives derivative convergence. The proof does not claim uniformity in a growing derivative order.

The separate weaker derivative-convergence range also follows: m=o(sqrt(n)/(log n)^((j+1)/2)) makes the quadratic-mark term vanish, while the diagonal term is bounded by a vanishing polynomial factor times a fixed logarithmic power. The claim is not used to replace the stronger collective-scale estimate.

The no-marked-edge probability follows from the exact edge marginal d/(n-1) and a union bound over unordered pairs. It vanishes in the target range. The proof keeps rare adjacent realizations in the sample space and later intersects the good events.

## G1. Exact block identity and general-degree calibration

On the complement of the constant vector, A R_Q=z R_Q-Q. Multiplying once more gives A R_Q A=z^2 R_Q-zQ-AQ. Compression by E yields the displayed positive (z+d)J_m/n term. Subtracting the attachment quadratic form in F_H changes its sign to negative. The source's equation (16) is therefore exact, including the stationary correction.

The tree constants follow from r(d)=1/(d-1), r'(d)=-1/((d-1)(d-2)) and g=r/(1-r^2). This gives the stated g and g'. With attachment-square factor a=d-2, the limiting constant term cancels:

\[
(d-1)d-a d^2 g=0.
\]

Direct substitution in the derivative gives D_d=2(d-1)^2/(d-2)^2>0. The stationary value error is 2ad m/n and the stationary derivative error is a m/n, both as stated.

The attachment norm is bounded by d sqrt(d-2), because ||A||=d for every d-regular graph and E is an isometry. The coupling to the isolated host vector is d sqrt(d-2) times the constant marked vector divided by sqrt(n). Dividing by sqrt(D_d) gives exactly kappa_d sqrt(m/n), with

\[
\kappa_d=\frac{d(d-2)^{3/2}}{\sqrt2(d-1)}.
\]

The lower-right effective block has positive sign H/D_d, since the reference value is Z_H=-sH.

## G2. Uniform interaction family and eigenvalue ordering

Both value and derivative error bounds are independent of H. The effective-matrix norm is bounded by kappa_d+H_0/D_d for every H in the norm ball. Choosing the same L above this bound plus one therefore works for every such H.

The dimension-free deterministic transfer error divided by s is bounded by equation (23). Its three terms tend to zero. The same host-gap, no-marked-edge and scalar-error event consequently applies to every H simultaneously. There is no union bound over matrices or eigenvalues. This supports choosing H after observing the graph, within the fixed norm bound, while preserving the requirement that the labels were fixed before sampling.

The deterministic theorem counts precisely the largest m+1 eigenvalues, including repeated eigenvalues. Interlacing places mu_(m+2) at or below lambda_2(A), which is separated below d on the good event. The continuity and compactness argument correctly makes the supremum over H measurable. No spacing assumption is hidden in the maximum ordered error.

## G3. Original model and worked cases

At d=3 and H=0, the edge weight is one, D_3=8 and kappa_3=3/sqrt(8). The effective matrix has the two eigenvalues plus and minus kappa_3 and m-1 zeros. Ordered transfer gives exactly the original theorem, including the full maximum over intermediate modes.

For m=1 the constants coincide with SG-17. For m=2, multiplying kappa_3 by sqrt(2/n) gives 3/(2sqrt(n)), so the reported top and third eigenvalue formulas and intermediate-mode scale are correct. The common-coupling vector is the sum of the two marked directions, and its orthogonal difference has zero effective shift.

For H=hI, the two collective values solve theta^2-(h/D_d)theta-kappa_d^2=0 and the orthogonal sector has value h/D_d. The more general assertion when H e_m=h e_m follows from symmetry and the resulting invariant orthogonal complement.

The adjacent-pair boundary check is also correct: the cubic-tree off-diagonal Green value is 1/3, and the regular Schur off-diagonal value at 3 is -9/3+1=-2. This does not contradict the original theorem, whose predetermined labels are adjacent only on a vanishing-probability event.

## Scope, priority and disposition

The final statement matches the audit's proposed distinction. It proves a growing marked-resolvent estimate and a specific critical finite-host law, including a calibrated weighted interaction family. It does not claim a general invention of growing-rank transfer, an optimal growth threshold, a bulk-edge law, a mixing result or a solver guarantee. The weighted family for d other than three is clearly identified as weighted, and arbitrary H may include diagonal potentials.

The priority note's comparisons with fixed-rank invariant models, Huang's growing-rank Wigner and invariant models, subspace-law transfer, regular-graph local laws and tree scattering remain applicable. The present review does not upgrade its bounded novelty assessment into historical firstness.

All inspected mathematical and integration obligations are closed for the three exact revisions above. There is no first unsupported inference to report. The integrator may record paper-proof acceptance at this scope, while retaining separate labels for external source dependencies, priority and absence of end-to-end formalization.
