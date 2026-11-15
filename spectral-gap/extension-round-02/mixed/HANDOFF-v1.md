# SG-E3 handoff, revision 1

Recipient: the problem 21 integrator. Owner: mixed-moment extension task. Written 15 November 2026 UTC.

## Result

Retain the exact depleted moment instead of a common geometric bound. With $a$ distinct cells, $h$ consistent centered singletons, and $b$ inconsistent centered singletons,

\[
|\mathbb EP|
\le 2^b\frac{n^{-h}D_h(n,a-h)}{(n)_a},
\]

where

\[
D_h(n,r)=h![z^h](1-z)^{n-r}
\exp\left(\frac{nz}{1-z}\right).
\]

The polynomial has the positive block weights $((j-1)n+r)(j-1)!$. The resulting monotonicity and merging inequality across colors prove the bound. For $b=0$, it is attained by one compatible color with $h$ centered singletons and $a-h$ raw factors. It therefore gives the exact maximum for fixed $n,a,h$ in that class.

The explicit scalar replacement is

\[
\Gamma_{n,a,h}
=
\frac{a+h-2+\sqrt{(a+h-2)^2+4(h-1)(n-a+1)}}
{2(n-a+1)}.
\]

For $h<a$, this is strictly smaller than the accepted $\beta$. For fixed $h$ and $n=a^2$, the exact envelope improves the full accepted bound by a factor of order $a^{h/2}$. An all-centered even-order pairing example proves that the square-root scale cannot be improved uniformly when $h=a$ grows.

## Input revision

- Permutation proof revision 3, SHA256 8b96bff0a030142682bd3b77bd33924c27f03512f0f5f9a10a222de40075a61f.
- Frozen manuscript revision 5 manifest, SHA256 ce8f5240a55ef278b9ab2c6ce53cc25f7688fcd28dafd602937c303a06b8ac78.
- Frozen revision 5 mixed section, SHA256 c101fd87f4d0dbbf58f07328ff7f74e70a556cbba71961cc30f6fb3acceafeac.

No rate or saddle attempt was read before freezing.

## Outputs and status

- sharp-mixed-envelope-v1.md contains the full proof, exact extrema, scalar corollary, fixed-count limit, and sharpness obstruction.
- check_envelope.py independently evaluates original mixed products by permutation enumeration on its stated finite ranges.
- envelope-checks-v1.json records all finite checks, which passed.
- MANIFEST-v1.json records the frozen output hashes and input dependencies.

SG-E3-A, SG-E3-B and SG-E3-C have written proofs and remain unreviewed. No canonical status or manuscript file was changed.

## Boundaries

The Laguerre generating identity is classical and explicitly attributed to DLMF 18.12.13. The accepted conditioned recurrence and affine reduction retain their attribution. Historical priority for the extremal conclusion has not been established.

No sharpness assertion is made for the factor $2^b$ or for the envelope at fixed $b>0$. Separate independent colors give an immediate corollary, not a separate novelty claim. The spectral graph enumeration is unchanged.

## Requested review

Check the coefficient identity (2.3) to (2.5), color merging (3.2), normalization of the selected-term identity (4.3), and attainment (4.6). Then check the scalar comparison in Section 5 and the fixed-count versus growing-count distinction in Sections 6 and 7.

Recommendation: keep the exact extremal theorem and the scalar corollary if review passes. Treat the fixed-count limit as an explanation of the improvement. Drop the search for a uniform improvement of the square-root order, since Section 7 gives an explicit obstruction.
