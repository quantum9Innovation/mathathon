# SG-E1 handoff

Sender: rate investigator. Recipient: problem 21 integrator.

The starting accepted proof was `../../manuscript-round-01/extensions/hyperbolic-window-v1.md`, SHA256 `73de96b41b7fba59454795f14bf1fe6160f8eee1391553bf980f3f29f4eba68a`. The accepted manuscript was revision 5, whose manifest SHA256 is `ce8f5240a55ef278b9ab2c6ce53cc25f7688fcd28dafd602937c303a06b8ac78`.

Prior exposure: this investigator wrote the base extension proof and read its accepted manuscript presentation. No new saddle or integrator attempt was read before freezing the rate proof.

## New result

RATE-1 gives a fully explicit uniform relative bound

$$
\left|\frac{R_k}{e^{k^2/(4N)}H_k}-1\right|
\le A_1(C)N^{-1/4}+A_2(C)N^{-1/2}+A_3(C)N^{-1}
$$

for every real $C\ge1$, integer $N\ge16C^2$, and integer $2\le k\le C\sqrt N$. The three constants are defined by elementary expressions in equations (2) and (3) of the frozen proof. Equation (5) supplies a finite bound using the actual order $k$.

The constants are conservative. The contribution is an explicit rate on the full bounded square-root range, including fixed orders and exact odd normalization. The accepted base proof established convergence there without a rate. No optimality or historical priority claim is made.

## Proof mechanism

Condition the triple count on its required parity, retain four-blocks as an independent Poisson count, and compare the exact pair availability product to an exponential. The odd variable is shifted from $J$ to $J-1$, so all moment errors vanish correctly as the triple parameter tends to zero. Explicit first and second moment bounds control the exponential comparison. The aggregate weight of all blocks of size at least five supplies the other term of order $N^{-1/4}$.

## Frozen outputs and checks

- `square-root-rate-v1.md`, SHA256 `ed472ce70521c37d59c4e3efc88bf7e883d1a75526023ef2c3a15c57bcd9c581`.
- `check_rate.py`, a bounded corroboration script.
- `rate-checks-v1.json`, successful results tied to the proof hash.
- `MANIFEST-v1.json`, output and source hashes.

All five symbolic moment identities passed. One hundred conditioned-moment inequality cases, 13920 pointwise availability cases, 7118 finite corrected-bound cases, and 11736 uniform-rate cases passed. The numerical calculations used 80 decimal digits. Twelve square-root examples through $N=10^8$ are recorded. These checks corroborate identities and examples, not the universal theorem.

No mathematical defect was found while deriving or checking this revision. The reviewer should particularly check the shifted odd moments, equation (16)'s coefficient collection, and the small-parameter tail normalization in Section 5.

## Proposed status and next action

Propose RATE-1 as proved in writing, awaiting independent review. It directly depends on the accepted positive partition representation and its normalization. It does not depend on another live extension result. If accepted, replace the manuscript's statement that no rate is supplied on bounded square-root ranges with the quantitative theorem, while retaining conservative-constant and scope language.

Requested next action: assign an independent reconstruction of the frozen proof hash before promoting the result or changing the manuscript. The owned proof and output files are frozen. New corrections should use a new revision.

Stopping reason: the requested explicit uniform rate, finite bound, derivation and corroboration are complete within the first checkpoint window. Further optimization is deferred to review rather than changing the frozen result.
