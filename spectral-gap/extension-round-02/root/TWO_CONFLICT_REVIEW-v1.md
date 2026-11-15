# Reconstruction of the exact two-conflict envelope

Date: November 14, 2026 Pacific. Verdict: accept the mathematical statement in MIX2-1 and the general upper bound MIX2-2. The reviewed proof has SHA256 `07c2aa5a4907a309546180835fe47e5a5301f352ed55bbd9e15aaf7dfa41a952`. The manuscript candidate was also read in full. This review was completed by the integrator, who had read the earlier kernel proofs and knew the proposed formula. It is separate from the original two-conflict derivation, but is not a blind review or formal verification.

## Reconstruction

The positive quantity B_(h,r)=K_(h,r)+2K_(h+1,r) equals 2K_(h,r+1)-K_(h,r) by the exact kernel difference. The first expression proves its monotonicity in r. This matters because bounding the difference of two increasing kernels directly would not prove monotonicity.

Retain the two inconsistent centered cells e,f and all h isolated centered singletons. Expand only the remaining r=a-h-2 cells. For a compatible selected support S, with s selected raw indicators, the scale is exactly n^(-h-2-s). The four cases in the proof exhaust the possibilities.

If both retained indicators are forced to zero, their centered factors give n^(-2), and the merged kernel is K_(h,s). If exactly one is forced, its negative factor leaves one additional compatible centered singleton, giving K_(h+1,s). Both are bounded by B_(h,r).

If neither is forced and the retained cells conflict, their indicator product vanishes. Expanding this pair alone gives K_(j,s0)-2K_(j,s0+1) in their common color, times the kernels of other colors. Rewriting its negative as K_(j,s0)+2K_(j+1,s0) permits separate positive color merging. The result is exactly bounded by B_(h,s), hence by B_(h,r). The sign is negative in the attaining family.

If neither is forced and the retained cells are compatible, at least one conflicting neighbor of e lies in the expanded support but is omitted from S. A good singleton cannot be that neighbor, and f cannot be that neighbor in this case. Thus s<=r-1, even if both retained cells share the same omitted neighbor. The kernel difference yields K_(h+2,s)<=K_(h+1,s+1)<=K_(h+1,r)<=B_(h,r). No assumption of two distinct omitted neighbors is used.

All kernel totals are at most a-1, including this last case. Therefore a=n is admissible and r=0 correctly excludes the final case. The affine coefficient sum contributes at most two for each of the b-2 remaining bad centered singletons, and at most one for every other cell factor. This proves the full bound with arbitrary powers and independent colors.

The attaining pattern uses centered cells (1,1),(1,2), with all other cells (i,i+1) for 2<=i<=a-1. The added cells avoid the pair's row and both columns and are pairwise compatible. Taking r raw and h centered gives exactly -n^(-a)B_(h,r). This includes every admissible n,a,h and proves the exact maximum at b=2.

The compact TeX candidate retains all four cases, the full-support domain check, the affine coefficient sum and the attaining construction. Its notation agrees with the maintained mixed section. No required proof correction was found.

## Independent finite corroboration

The [check program](check_two_conflict_independent.py) directly enumerates the original permutation products by color. It computes the comparison kernel from the alternating indicator sum, without importing the positive recurrence or the author's program. Its [saved report](two-conflict-independent-checks.json) records 20,246 original products, including 14,249 cases with exactly two bad singletons, 5,997 with more, and 18,379 at full support. All bounds pass. Fifty-six attaining patterns through n=7 give exact equality. The written argument establishes the unrestricted claim.

## A limit to the natural extension

The same-row clique does not always maximize products with more bad centered singletons. At n=a=b=8 and h=0, use four disjoint rows, each requesting its own two columns, and center all eight cells. If Y_i is the sum of the two indicators in row i, then the scaled product is the product of 1-nY_i. Selecting j rows gives 2^j compatible choices, so

$$
n^8\mathbb E P=\sum_{j=0}^4\binom4j(-2)^j\frac{n^j}{(n)_j}
=\frac{1121}{105}>7.
$$

The eight-cell same-row clique instead has scaled absolute expectation seven. Thus a universal clique-extremizer claim is false. This exact counterexample is useful frontier information, not a defect in the proved b=2 theorem. No exact maximum for b>2 is asserted.
