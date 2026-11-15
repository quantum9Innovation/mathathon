# Exact-revision review of the single-phase obstruction

Date: November 14, 2026, America/Los_Angeles.

Reviewed proof: `../phase-obstruction/proof-v1.md`.

Reviewed SHA256: `c99429b53cd993ab1526dbdd41d2224dc55f5f9c165b011f3e1c6805344675f0`.

Verdict: the lower-bound theorem, its simultaneous phase quantifier, and its stated obstruction to an improved tail exponent are accepted within the exact model below. No unsupported mathematical inference was found. This review does not certify historical priority, the external upper theorem cited in Section 7, or end-to-end formal verification.

## Scope and prior exposure

The reviewer inherited the current discussion and had already audited the existing spectral inventory. Before opening the frozen candidate, the reviewer received its proposed model, cubic equation, core moments and projection mechanism. The reviewer then independently reconstructed those steps, read all of the frozen proof, and checked its hash. This is separate reconstruction with declared exposure, not a blind or access-isolated review.

The model is the ordinary uniform permutation n-lift of K4 with six independent base-edge bijections, four fibers of size n, and no connectivity conditioning. Only the edge between base colors 3 and 4 has a nontrivial scalar unit phase. The operator is Hermitian raw adjacency. The new sector is the orthogonal complement of vectors constant on each fiber.

The accepted conclusion is stronger than a statement for each fixed phase. For every fixed delta satisfying

\[
0<\delta<\lambda_*-2\sqrt2,
\qquad
\lambda_*=r+2/r,
\qquad
r^3-r-2=0,\quad r>0,
\]

there is a phase-independent graph event with probability at least

\[
\frac1n-\frac{C_\delta}{n^2}
\]

for all sufficiently large n, on which

\[
\lambda_{\max}(A_{\zeta,n}|_{\operatorname{ran}Q})
>2\sqrt2+\delta
\]

holds for every unit phase zeta. Consequently the same lower bound holds for a phase chosen after observing the graph. In particular, the liminf of n times the simultaneous-event probability is at least one.

## 1. Infinite localized eigenfunction

Let S be K4 with its edge 34 deleted. Its two degree-two vertices each receive one infinite rooted binary branch. Every vertex of the resulting infinite graph H has degree three.

For p(r)=r^3-r-2, the derivative is negative between zero and 1/sqrt(3), while p is negative throughout that interval. Thereafter p increases strictly to infinity. This verifies the unique positive root. Since p(sqrt(2))=sqrt(2)-2<0 and p(2)=4>0, this root lies strictly between sqrt(2) and 2. Therefore lambda_* exceeds 2sqrt(2).

Set b=(lambda_*-1)/2. The candidate vector equals 1 on core colors 1 and 2, b on core colors 3 and 4, and b r^(-k) at depth k in either branch. The branch recurrence is exactly lambda_*=r+2/r. The two core equations are

\[
\lambda_*=1+2b,
\qquad
(\lambda_*-1)(\lambda_*-r^{-1})=4.
\]

Direct expansion gives

\[
(\lambda_*-1)(\lambda_*-r^{-1})-4
=\frac{(r-1)(r^3-r-2)}{r^2}=0.
\]

There are 2^k vertices at added depth k, so the squared norm has geometric tail with ratio q=2/r^2<1. Thus the vector is square-summable. The adjacency operator on H is bounded with norm at most three, so the pointwise eigenvalue equations give a genuine Hilbert-space eigenfunction.

For truncation through depth R, the norm S_R and support size M_R in the proof are correct. In the difference between lambda_* S_R and the finite-support energy, every edge from the support to its complement contributes once, from its inside endpoint. There are 2^(R+1) such edges, each with endpoint product b^2 r^(-2R-1). Their total is

\[
\frac{2b^2}{r}q^R.
\]

This verifies the exact quotient in equation (2), including R=0. Its numerator is positive since the vector and internal edge weights are positive. That positivity also suffices for the constant used later in the projection bound.

## 2. Exact count of cores

A colored core has exactly one vertex of each base color and five required edge matches. For every prescribed tuple, the five matches lie in distinct independent base permutations and have joint probability n^(-5). There are n^4 tuples. Hence EX=1/n exactly.

Two realized colored cores sharing any vertex must be identical. Along each edge of S, the unique matching neighbor propagates equality to the adjacent color. Connectivity of S then propagates it to all four colors. Every partly overlapping distinct pair therefore has probability zero.

The ordered pairs of disjoint tuples number [n(n-1)]^4. For each of the five base-edge permutations, prescribing the two distinct matches costs 1/[n(n-1)]. Independence across the five permutations yields

\[
\mathbb E[X(X-1)]=\frac1{n(n-1)}.
\]

No graph automorphism factor is missing because the copies are distinguished by their four base colors.

## 3. Conditional clean exploration

Conditioning on a specified core fixes one entry in each of five permutations. Every remaining permutation, conditioned on these entries, is a uniform bijection between its unused sets. The sixth permutation remains unconditioned.

Explore previously unknown edges from the two missing ports and then from the discovered tree vertices, skipping the already known parent edge. A fresh image or preimage is uniform among unused labels in its target fiber. Previously exposed reverse orientations are not fresh queries. On the success path, the exploration through depth R+1 encounters B_R=2^(R+2)+2 vertices.

The proof's bound of 3B_R on all fixed or queried entries is conservative. In any one permutation there are therefore at most 3B_R used entries. For n>=6B_R, at least n/2 possible targets remain. At most B_R of them have already been discovered. This proves a collision probability of at most 2B_R/n at each fresh query. A union bound gives equation (5).

The extra layer is essential and present. All ports of support vertices through depth R are exposed. Consequently an extra edge between support boundary vertices would be detected as a collision. The induced support graph therefore has precisely the desired core and branch edges.

Let Y count clean cores. Its first moment is at least 1/n-6B_R^2/n^2. Since Y<=X, the inequality

\[
\boldsymbol1_{\{Y\ge1\}}
\ge Y-\frac{Y(Y-1)}2
\]

and the exact second factorial moment prove equation (6). The last simplification uses 1/[2n(n-1)]<=1/n^2 for n>=2. No independence between different clean-core events is needed.

## 4. Uniform phase removal and new-sector projection

Every cycle in the clean support lies in S. All edges of S are unphased. On each attached finite tree, phases can therefore be removed recursively by a diagonal unitary that equals one at its core root. This construction works for every value of zeta and preserves coordinate magnitudes.

The resulting unit vector u_zeta has support size M_R and energy R_R for every phase. Edges leaving its support contribute zero to its quadratic form. Clean exploration has already excluded any extra internal edges.

Each magnetic edge block is a scalar multiple of a permutation matrix. Thus the four-dimensional fiber-constant space is invariant. Hermiticity gives invariance of its orthogonal complement and commutation with P and Q. The absolute row and column sums give operator norm at most three.

Fiberwise Cauchy-Schwarz proves

\[
s=\|Pu_\zeta\|^2\le M_R/n.
\]

Orthogonal invariant sectors eliminate the cross terms. Therefore the new-sector Rayleigh quotient is at least

\[
\frac{R_R-3s}{1-s}
=R_R-\frac{(3-R_R)s}{1-s}.
\]

As R_R>0 and n>=2M_R, the loss is at most 6M_R/n, verifying equation (8). All estimates are uniform in zeta. A common test vector for all phases is unnecessary. The same underlying graph event supplies an appropriate test vector for each phase.

## 5. Quantifiers and completion

For fixed delta in the stated interval, Delta=lambda_*-2sqrt(2)-delta is positive. Since q<1, the chosen fixed R exists. Equation (2) then loses strictly less than Delta/4. The specified lower bound on n makes the projection loss at most Delta/4. The resulting quotient exceeds lambda_*-Delta/2 and hence strictly exceeds 2sqrt(2)+delta.

The event Y>=1 depends only on the unweighted lift. Its probability bound is independent of the phase, and every graph on that event satisfies the spectral inequality for every phase. This validates both the simultaneous conclusion and post-selection of the single phase. The discrete finite probability space also removes any measurability concern about the universal phase quantifier.

Dividing raw adjacency by three gives exactly the normalized threshold and delta_*/3 excess range stated in the proof. The operator norm lower bound follows from the largest-eigenvalue lower bound.

## 6. Interpretation and limitations

The proof rules out an o(1/n) upper tail at the specified fixed positive excesses, even after adaptive choice of the one base-edge phase. This follows directly from the lower bound and does not depend on an external upper theorem.

The proof does not establish that all obstructions have been classified, that the leading tail coefficient is one, or that a simultaneous upper bound holds. It makes no claim for connectivity-conditioned lifts, changing multiple independent cycle phases, thresholds outside the stated interval, or graph solvers. Those would be different statements.

The external O(1/n) theorem mentioned in Section 7 was not re-audited here. This acceptance concerns the self-contained lower bound. No novelty conclusion follows from this review. No proof-assistant verification or numerical experiment was performed.

Open findings in the reviewed lower-bound argument: none.

Only this review file was written. The frozen proof and all earlier accepted records were left unchanged.
