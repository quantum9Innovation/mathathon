# One inconsistent singleton handoff

The requested candidate is proved, including arbitrary powers and independent colors. The exact-maximum assertion holds for every $n\ge2$, $2\le a\le n$ and $0\le h\le a-2$ with $b=1$:

\[
|\mathbb EX|\le
\frac{n^{-h-1}P_h(n,a-h-1)}{(n)_{a-1}}.
\]

The same proof gives the bound with factor $2^{b-1}$ for every $b\ge1$. No general sharpness assertion is made for $b>1$.

## Decisive mechanism

The exact kernel identity is

\[
K_{j+1,s}=K_{j,s+1}-K_{j,s}\le K_{j,s+1}.
\]

Distinguish one inconsistent centered singleton. After expanding the other factors, a selected compatible support either contains a conflicting neighbor, forcing the distinguished indicator to zero, or avoids all such neighbors, omitting at least one requested cell. The missing cell pays for one additional exposure through the kernel inequality. Every selected support is bounded by the same reduced-depletion envelope. The remaining affine weights are at most one except for the other $b-1$ inconsistent centered singletons, whose weights are two.

## Attainment and domain

In one color, take the distinguished centered cell $(1,a)$, raw diagonal cells $(i,i)$ for $1\le i\le r=a-h-1$, and centered diagonal cells for $r+1\le i\le a-1$. It has exactly one inconsistent centered singleton and attains the displayed bound in absolute value. The condition $h\le a-2$ is necessary and is stated explicitly. The construction stays in $[n]^2$ at $a=n$.

## Exact finite checks

Two methods were used.

- Affine expansion and exact compatible-assignment probabilities checked 67,830 exhaustive cases with $b=1$, 16,800 sampled cases, 286 attainment instances and 11,479 kernel difference identities.
- Direct enumeration of uniform permutations checked the same 67,830 exhaustive cases with $b=1$, 6,294 exhaustive cases with $b\ge2$, and 3,600 sampled cases. This second expectation calculation does not use the selected-support proof.

All recorded checks passed using rational arithmetic. Powers include pure centered powers through five and mixed centered and raw powers. Dimensions, random seeds and all precise ranges are in the scripts and JSON records. The attainment check was bounded at $n=12$. A preliminary generator used an invalid placement that could create a second inconsistent centered singleton. That placement was corrected before the recorded checks. An exploratory larger attainment run was stopped because the smaller run already checks every admissible parameter triple through twelve. No inequality failure was found.

## Dependencies and review request

The direct mathematical dependency is the frozen mixed proof, SHA256 `878a139aee3caf6040debcc0f9b476e5fa0dd283c70c2a75a48ceaaea38d6b4d`. The integrator supplied the candidate and the proposed general corollary. This packet does not claim independent discovery of the research direction or historical priority.

Review the exact normalization in the kernel difference identity, the assertion that every conflicting neighbor lies outside the consistent-singleton set, the missing-neighbor count, and the arbitrary-power affine weights. The candidate's attainability is proved separately from the upper bound.

No maintained manuscript, canonical ledger, or earlier frozen packet was edited. The proof and support records are fixed by `MANIFEST-v1.json`.
