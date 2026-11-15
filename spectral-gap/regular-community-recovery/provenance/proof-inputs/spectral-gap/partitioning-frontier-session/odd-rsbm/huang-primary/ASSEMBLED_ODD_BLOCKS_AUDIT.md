# Actual-source audit of the completed parity extension

Verdict: **PASS at the source hashes below**, with the companion theorem locator corrected. No remaining mathematical defect was identified in this review. This is a proof review, not a formal verification, implementation benchmark, or historical novelty certification. This reviewing agent authored the entropy companion; its assessment of that companion is therefore a self-check. The nearconstant, central, and assembled arguments were separately reconstructed from their actual supplied sources.

Date: 2026-11-15.

## Sources binding this review

| Source | SHA256 |
|---|---|
| `../configuration-mixing-and-odd-blocks.tex` | `2a2856c86d37c78a2a29bc2a5f67f5df0c5649963809fc32770fe76379cff048` |
| `configuration-arbitrary-target-tails.tex` | `46655a70f9c0d39de5e7d45cd4542de1dd0395fae6bc34d3a25020621b6ede6f` |
| `../parity-reduction/nearconstant-configuration-atoms.tex` | `5f041c74739d9e8e8cc56944e6906995b3f0e978c7a58226929713a746aa480c` |
| `../meszaros-extension/balanced-all-target-configuration.tex` | `9a1a1d6254cd26829fb8a12e2f4a7cc7b22b19d0657cf73c077b86b13eabf557` |

The entire assembly and each companion were read. The earlier assembly SHA `a7d034f9153d5c5201f732b3a6315f0cadca3b00e86f62d210e11fd21ddf18b9` had a bibliographic locator error: its reference to “Theorem 4” of the entropy companion was incorrect because that source uses separate counters for theorem, lemma, and proposition. The intended result is its **Theorem 1, All-target noncentral tails**, label `thm:tails`, printed pp. 4–5. The final assembly uses the descriptive locator. Reversing exactly that sentence replacement reconstructs the old source hash, confirming that this was the only assembly change between those two versions.

The nearconstant source changed from previously inspected SHA `27e848...` only in its final scope paragraph. The full current source was reread, and its proof still passes the checks recorded below.

## Strong mixing and the partition of inputs

The configuration model requires only dn even. The diagonal counts each loop twice, so the exact identity \(C\mathbf1=d\mathbf1\) and its transpose both hold. All fields in the assembly are fixed odd prime fields. Neither the central nor entropy argument needs p coprime to d.

The reference law is a point mass for constant inputs and uniform mass p^{-n+1} on the sum hyperplane for nonconstant inputs. That hyperplane has p^{n-1} points even when p divides n or d: it is a single nonzero linear functional on the full n-coordinate space, not multiplication by n on the constant subspace.

The nearconstant threshold may be decreased without invalidating the companion bound. Choosing it to satisfy the displayed entropy inequality ensures exponentially fewer than p^n nearconstant inputs. The nearconstant actual atom sum is o(1), and multiplying the input count by p^{-n+1} also gives o(1).

Outside that class, every noncentral input satisfies the hypotheses of the entropy companion. Its combined input-and-edge-type tail theorem implies the assembly's weaker input-only tail because the event involving the input norm is contained in the combined tail event for every type. The target supremum is already inside the summed bound. No loss of p^n occurs here.

The reference-law intermediate contribution is p times a uniform multinomial tail. Coordinate Hoeffding bounds and a union bound over the fixed p labels send it to zero for every fixed positive B. The central input norm bound implies the balanced count hypothesis with any fixed K>sqrt(B), eventually accounting for log(n+1)/log(n).

The central companion error is uniformly o(p^{-n+1}); at most p^n inputs multiply it to p·o(1)=o(1), because p is fixed. Incompatible target sums have exactly zero actual and reference mass. Constant inputs have exactly zero error and are excluded before this partition. For large n, the nearconstant and central classes are disjoint. The three estimates cover every remaining input.

## Companion analytic and combinatorial checks

For the nearconstant estimate, the constrained-exposure conditional bound is uniform over the entire adaptive past. The random stopping condition can only restrict any specified binary word event. On the prescribed-output event, each unprescribed outside vertex is hit at least twice; hence 2c-dk=J+R-F>=0. The factorial input count and the displayed geometric ratio give O(n^{1-d/2}). The loop lower example is correctly restricted to the unconditioned model.

For the entropy estimate, the arbitrary-output count uses one row polynomial for each actual output coordinate. Evaluating nonnegative coefficients at pi^{(d-1)/d} gives a target-uniform bound without enumerating target profiles. The F_t equality analysis uses the cyclic additive group of a prime field. The Taylor Hessian is -(d-1)p/d on the sum-zero hyperplane, giving the stated quadratic Taylor coefficient. Zero row masses pose no continuity problem because p^{-(d-1)}<=max_t F_t<=1. The global rate vanishes only at the uniform matrix or point-mass matrices. The uniform local quadratic bound and compactness away from constants justify the shrinking-window tail after all polynomial type factors are counted.

For the central estimate, direct stub counts give W(M), B(M), and the exact baseline type distribution. Pairwise independence of conditioned tuple positions holds for d>=3. The row difference lattice has index p; its maximal characters are exactly the affine phases obtained by varying any two positions of a tuple of prescribed sum. Uniform real tilts control relative moderate-deviation errors of order O(log^3(n)/sqrt(n)), not merely additive errors. The fixed finite family gives uniform spectral decay away from those characters. The noncentral type contribution is o(p^{-n}).

The bounded integral matrices 2(e_j-e_0)(e_j-e_0)^T preserve row sums and even diagonal, and their weighted-row outputs span the total-zero hyperplane when p is odd. The smooth factorial ratio and concentration in enlarged/shrunken windows equidistribute all p^{p-1} feasible output cosets. Thus the leading mass is p^{-n+p}·p^{-(p-1)}=p^{-n+1}. This explicitly covers odd n with even d.

## Two-block moment, rank, and conditioning

The affine reference bound is uniform in b. For nonconstant x, its scalar condition is d2·s(x)=s(b), giving at most p^{N-1} terms of mass p^{-N+1}. For constant x=a1, it is the vector equation b=d2·a1; there is at most one a since p does not divide d2. Thus the bound 2 is valid even when p divides N or d1.

The first probability replacement in the two-block kernel moment costs at most (2+e_N)e_N; the second costs at most 2e_N. Each uses an affine sum with its other variable fixed, exactly as required. The bound is uniform over all cross matrices B.

Both nonconstant reference factors impose the same condition s(x)+s(y)=0. There are at most p^{2N-1} pairs, giving p. Constant-constant pairs are governed by the full vector equation a+b=0 and contribute exactly p, regardless of p dividing N. The mixed cases have at most p^{2-rank(B)} each; counting possible constant solutions again is only harmless overcounting.

The greedy disjoint-support row construction gives rank_Fp(B)>=N/[1+d2(d2-1)] over every field, because every selected row is a nonzero zero-one row with support disjoint from the others. This supplies a uniform rank bound even though B ranges over an N-dependent family.

Real nullity at least two forces every (2N-1)-minor of the integer shifted matrix to vanish, hence also mod-p nullity at least two. Markov at p^2 gives the limsup bound 2/p. The order of limits is correct: p is fixed while N grows, and only afterwards ranges through arbitrarily large fixed odd primes excluding the finitely many divisors of d2. This yields zero failure limit without any uniform-in-growing-prime claim.

The configuration simplicity probability is bounded below for fixed d1 along all admissible sizes. Conditioning the two independent configurations on simplicity costs a bounded product factor and produces precisely two independent uniform labelled simple internal graphs. Since the unconditioned failure estimate is already uniform in B, conditioning preserves that uniformity. An independent random simple cross graph may therefore be adjoined. No even-size matching-model contiguity is needed for this final transfer.

On real nullity one, rational and real ranks agree for the integer matrix. Its rational kernel is spanned by the planted sign vector, whose first coordinate is nonzero. Hadamard bounds give O(N)-bit minors for fixed degrees, so fraction-free elimination has polynomial bit complexity. This conclusion is exact algebraic recovery, not a nearly-linear algorithm or a numerical eigengap statement.

## Final scope

The assembly's d1>=3, d1>d2>0, all-admissible-N statement follows from the three supplied ingredients under the checks above. It closes the odd-N, even-d1>=4 gap of the previous note. It does not cover (d1,d2)=(2,1), establish a quantitative failure rate, or certify historical priority. Huang's unshifted nonsingularity theorem is not used as if it were an arbitrary-shift theorem.
