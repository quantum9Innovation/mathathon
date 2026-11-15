# Two-conflict envelope handoff

Task: MIX2-1. Sender: mixed two-conflict extension. Recipient and integrator: the main problem 21 session. Revision 1, November 15, 2026 UTC.

## Result

For exactly two inconsistent centered singletons, support size $2\le a\le n$ and $0\le h\le a-2$ consistent centered singletons, put $r=a-h-2$. The exact maximum over all permitted multiplicities and independent colors is

\[
n^{-a}\bigl(2K_{h,r+1}-K_{h,r}\bigr)
=\frac{2n^{-h-1}\mathcal P_h(n,a-h-1)}{(n)_{a-1}}
-\frac{n^{-h-2}\mathcal P_h(n,a-h-2)}{(n)_{a-2}}.
\]

Two centered cells sharing a row attain the bound when every other cell is compatible with the pair and with every other cell. Use raw factors for the other $r$ cells and centered factors for the other $h$ cells. This construction works at $a=n$.

The proof also gives a factor $2^{b-2}$ times the same expression for all $b\ge2$, with no sharpness assertion for $b>2$. The old general bound exceeds this one by $2^{b-2}n^{-a}K_{h,r}$. That term may vanish, including at $h=1,r=0$.

## Evidence and dependencies

The frozen proof is `proof-v1.md`, SHA256 `07c2aa5a4907a309546180835fe47e5a5301f352ed55bbd9e15aaf7dfa41a952`. It contains exact hypotheses, numbered steps, explicit kernel domains, arbitrary multiplicities and colors, an attaining family, and three finite examples.

It uses the positive kernel and color merging from `../mixed/sharp-mixed-envelope-v1.md`, SHA256 `878a139aee3caf6040debcc0f9b476e5fa0dd283c70c2a75a48ceaaea38d6b4d`, and the kernel difference from `../mixed-one-conflict/proof-v1.md`, SHA256 `4ed2c2cbe44c453eb401ebbf20eae09b35a9365d018f86abee262fc38dca83f4`. Those facts and their domain checks are reproduced in the proof. Prior exposure and the current task scope are recorded in `RUN_CONTRACT.md`.

The exact rational checks passed:

- 6,168 exhaustive mixed products for $n=2,3$, one or two colors and eight listed factor types, restricted to $b=2$.
- 38,838 exhaustive selected-support configurations, including 4,356 unforced compatible retained pairs and every other branch of the proof.
- 2,520 sampled exact products with $b=2$ and 2,520 separate assignments with $b\ge2$, through $n=10$, with one to three colors and powers as high as 101.
- 108 comparisons between direct permutation enumeration and exact compatible-subset expansion.
- All 1,771 admissible attaining triples through $n=22$.

The source and complete ranges are in `check_two_conflict.py` and `checks-v1.json`. These checks are finite corroboration, not proof premises.

## Review request and stopping point

The proposed status is written proof complete, awaiting independent review. No canonical status was changed. Review the exact frozen hash, with particular attention to Section 3.4. When the retained cells are compatible and neither is forced, one omitted neighbor already gives $s\le r-1$. The inequality $K_{h+2,s}\le K_{h+1,s+1}$ then closes the bound. It is not necessary to assume that the two retained cells have distinct conflicting neighbors.

No open logical obstruction was found. No claim is made about all equality patterns, the exact envelope for $b>2$, spectral consequences, or historical firstness. The extension stopped once the general theorem, boundary checks, attaining family and finite checks were frozen. Maintained manuscript files, canonical ledgers and earlier frozen records remain unchanged.
