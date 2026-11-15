# Exact two-conflict envelope, independent review

Date: November 14, 2026, America/Los_Angeles.

Decision: Accept MIX2-1 and MIX2-2 in the exact frozen revision identified below. Accept the compact integration candidate as a faithful proof of the same statements. No unsupported inference or required repair was found.

This acceptance covers the exact maximum for \(b=2\), the stated general bound for \(b\ge2\), all permitted multiplicities and independent colors, and the endpoint \(a=n\). It does not assert sharpness for \(b>2\), classify all equality patterns, or certify historical priority.

## Revision, exposure and method

| Input | SHA256 |
| --- | --- |
| Author proof v1 | 07c2aa5a4907a309546180835fe47e5a5301f352ed55bbd9e15aaf7dfa41a952 |
| Author manifest v1 | 41175ccf28cd46e77c37a0e4067cac384b95c0d7ef991a668da73a7eba4b5010 |
| Compact integration candidate v1 | cb4313258b9ac9e0e0dd8b458dc5a0a585678aba9349a3d9d27c792a7ad1e93f |
| Base exact mixed proof | 878a139aee3caf6040debcc0f9b476e5fa0dd283c70c2a75a48ceaaea38d6b4d |
| One-conflict proof | 4ed2c2cbe44c453eb401ebbf20eae09b35a9365d018f86abee262fc38dca83f4 |

All seven author-manifest output and input entries were verified. The integration candidate is separately hashed because the author manifest does not list it.

Prior exposure includes the base mixed proof, its integration draft, the one-conflict proof, and assembled revisions through v8. The present argument was reconstructed from the frozen MIX2 proof before inspecting any v9 source. The author's checker, its numerical output and the integrator's separate MIX2 review were not read or imported as mathematical evidence. Only their file hashes were verified where listed by the manifest. The independent checker adapts the original-product evaluation method from the earlier one-conflict review.

No author, frozen-manuscript, maintained-manuscript or canonical record was edited.

## Mathematical reconstruction

Write
\[
K_{j,s}=\frac{n^s\mathcal P_j(n,s)}{(n)_{j+s}},
\qquad
B_{h,r}=K_{h,r}+2K_{h+1,r}.
\]
The positive partition formula gives nonnegativity, monotonicity in the integer parameter \(s\), and merging across colors when total indices do not exceed \(n\). Merging uses both the partition embedding and
\[
(n)_u(n)_v\ge(n)_{u+v}.
\]
Thus merging cannot reverse direction when a polynomial coefficient vanishes, including \(K_{1,0}=0\).

For \(j+s+1\le n\), isolating a compatible centered indicator gives the exact identity
\[
K_{j+1,s}=K_{j,s+1}-K_{j,s}.
\]
Consequently
\[
B_{h,r}=2K_{h,r+1}-K_{h,r}\ge0.
\]
Its first expression, not subtraction of two monotone functions, proves monotonicity in \(r\).

Retain two distinct inconsistent centered singletons \(e,f\), together with all \(h\) globally consistent centered singletons. Expand only the remaining \(r=a-h-2\) cells. For a selected raw support \(S\), put \(s=|S|\). An incompatible \(S\) gives an identically zero product. When \(S\) is compatible, the following cases prove
\[
|G_S|\le n^{-h-2-s}B_{h,r}.
\]

1. If both retained indicators are forced to zero, their centered factors contribute \(n^{-2}\). Conditioning and color merging leave \(K_{h,s}\), which is at most \(B_{h,r}\).
2. If exactly one is forced, its factor contributes \(-n^{-1}\). The other retained factor remains a compatible centered singleton. The merged kernel is \(K_{h+1,s}\), again at most \(B_{h,r}\). A conflict between \(e\) and \(f\) does not interfere after the forced indicator is replaced by zero.
3. If neither is forced and they conflict with each other, they have one color and \(M_eM_f=0\). If that color contains \(j\) consistent centered factors and \(s_0\) selected raw factors, the exact bracket is \(K_{j,s_0}-2K_{j,s_0+1}\). The kernel difference rewrites it as \(-K_{j,s_0}-2K_{j+1,s_0}\). The sign is therefore known before taking absolute values. Merging the two positive absolute-value terms separately gives \(K_{h,s}+2K_{h+1,s}\), and monotonicity gives \(B_{h,r}\).
4. If neither is forced and they are compatible, a neighbor conflicting with \(e\) lies outside \(T\cup\{e,f\}\). It belongs to \(V\setminus S\). This proves \(s\le r-1\) using just one omitted cell. The argument does not assume two distinct neighbors, and it also covers different colors. After conditioning, the merged kernel is \(K_{h+2,s}\). The difference identity gives
\[
K_{h+2,s}\le K_{h+1,s+1}\le K_{h+1,r}\le B_{h,r}.
\]

The globally consistent cells avoid every requested cell, including omitted ones. They therefore stay in unused rows and columns in every conditioning step. Each identity applies to a compatible partial matching within its color.

Every kernel total in these four cases is at most \(h+r+1=a-1\). In the fourth case this follows from the omitted-neighbor argument. Thus the proof has an actual spare index at \(a=n\). It does not invoke an undefined depleted seed or a conditioning probability with too many matches.

For arbitrary powers, the exact affine form is \(c_v+d_vM_v\), with \(d_v\ge0\). For a centered singleton its weight \(d_v+n|c_v|\) equals \(2\). For every other permitted factor this weight is at most \(1\). For even centered powers at least two, it is at most \(1-1/n\). For odd powers at least three, the bound
\[
(1-1/n)^3+(n+1)n^{-3}=1-3/n+4/n^2\le1-1/n
\]
holds for every \(n\ge2\). Raw powers and mixed raw-centered powers have \(c_v=0\).

Summing the selected-support bound therefore gives exactly
\[
|\mathbb EX|
\le n^{-a}B_{h,r}
   \prod_{v\in V}(d_v+n|c_v|)
\le 2^{b-2}n^{-a}B_{h,r}.
\]
There are precisely \(b-2\) centered singletons in \(V\), because all consistent centered singletons were retained. This count is relative to the original support, so no change of consistency after expansion is being silently used.

## Attainment and endpoints

For every admissible \(n,a,h\), take centered cells \((1,1),(1,2)\) and the cells \((i,i+1)\), \(2\le i\le a-1\). Make the first \(r=a-h-2\) added cells raw and the remaining \(h\) centered. All indices lie in \([n]\), including when \(a=n\). Exactly the first pair is inconsistent. Conditioning on the raw cells leaves the exact signed value
\[
\mathbb EX=n^{-a}(K_{h,r}-2K_{h,r+1})
=-n^{-a}B_{h,r}.
\]
Thus the upper bound for \(b=2\) is attained, rather than only approached.

The endpoint \(r=0\), equivalently \(h=a-2\), is covered. The compatible-unforced case cannot occur there because it would require an omitted neighbor. At \(a=2,h=0\), the maximum is \(n^{-2}\). At \(h=0\), the general expression reduces to
\[
\frac{n+a-2}{n^2(n)_{a-1}}.
\]
At \(a=3,h=1\), it equals \(2/[n^3(n-1)]\). Since \(K_{1,0}=0\), the improvement over the earlier general bound need not be strict. The text correctly states that limitation.

## Independent finite checks

The portable script evaluates the original products over every permutation in each color and multiplies the resulting expectations across independent colors. Rational arithmetic is exact. It does not derive the tested expectation by replaying the author's selected-support proof.

All 20,204 original products checked satisfy the stated bound. These include 18,833 cases with \(a=n\), 1,653 with multiple colors and 1,976 with repeated or mixed powers. The exhaustive families use two colors for \(n=2,3\), with five exponent choices, and one color for \(n=4\), with raw or centered factors. A fixed-seed sample adds three-color products at \(n=5,6\).

The selected-support check covers 63,916 supports. All four compatible cases occur, as do incompatible selected supports. Targeted examples include one omitted cell conflicting with both retained cells and retained cells of different colors.

All 84 triples \(2\le n\le8\), \(2\le a\le n\), \(0\le h\le a-2\) attain the claimed negative value by direct original-product enumeration.

These computations corroborate finite cases only. The proof above supplies the general result.

## Integration and reader-facing scope

The compact TeX candidate preserves the four-case argument, the crucial sign rewrite in the conflicting-pair case, the single omitted-neighbor argument, the \(a-1\) domain bound, arbitrary affine weights and exact attainment. Its six references to earlier definitions and lemmas resolve in frozen v8. Its distinction between an exact \(b=2\) maximum and a general \(b\ge2\) bound is explicit.

The notation \(r=a-h-2\) is local to this subsection and is restated in both general-bound and attainment passages. The examples make clear that the improvement can vanish. No inference from an inconsistent-singleton count to a count of conflicting pairs is made.

No additional issue is proposed for the canonical registry. The requested next action is an assembled v9 delta check against this exact candidate, together with the already recorded v8 editorial fixes and the new source attribution.

