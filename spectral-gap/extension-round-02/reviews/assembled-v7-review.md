# Assembled manuscript v7 delta review

Date: November 14, 2026, America/Los_Angeles.

Task: Audit the exact v6-to-v7 delta for mathematical invariance, source scope, priority language, the two wording repairs and the supplied PDFs.

Decision: Accept this revision within that scope. No unsupported mathematical inference or blocking source claim was found in the delta. The accepted v6 proof review carries forward because every formal statement and proof block is unchanged. This is not a universal novelty certificate or an audit of the separate one-conflict extension.

## Revision and exposure

The reviewed v7 manifest has SHA256 `ed77594646cbc9c1372aebaa707f209d9395a1c20b40bf6bb8fb6943695b9b80`. All 24 entries were recomputed and match. The base is frozen v6, manifest `40999c65a266ec572b41e23824c9b2550c8e1e211b43180711c087f01d604165`.

Prior exposure includes the original sublinear proof, the mixed integration draft, the full-range extension review and the assembled v6 audit. The three supplied priority notes were read as claims and source locators. Their conclusions were not substituted for checking the new displayed identities and applicable source domains.

| Reviewed item | SHA256 |
| --- | --- |
| Main source | `4a442621ecb76410aa1c93ab818ff878205ada94cd0f79062b23fc06290a5de0` |
| Discussion source | `dad89f829ea4e24cd7d5ef549b02ad78db43336d6b282c64e34ee5e2b2e13298` |
| Introduction source | `0098634e372434314ffaa19dff0c477f48dbf15b9c7b55011a7913543a0a45e4` |
| Guide source | `0ce7a7e0f10abee3d9d880e3632cfa17054073e4809660389226a182c7986016` |
| Main PDF, 32 pages | `79d7a43b449e76e70387b583539f1eafb6b488e90bc1132197ba6d06508801ae` |
| Guide PDF, 7 pages | `4005f85aadbe6f501776030fc93baf554ebc2b07131c69af9df76c3b413491d1` |

The complete entry list and exact textual differences are retained in `assembled-v7-evidence.json`. The three supporting audit hashes also match the task packet.

## Mathematical and source checks

### AV7-C1. Centered-matrix specialization

Accepted. The inspected [Han and Niles-Weed preprint](https://arxiv.org/html/2607.23836v1) defines its matrix polynomial with the factor $1/h!$ in equation (2). For each row subset, the permanent sum enumerates $(n)_h$ injections. Averaging their products gives $\mu_h(n,0)$. Hence

\[
e_h(nI-J)=\frac{\binom nh(n)_h}{h!}\mu_h(n,0)
=\binom nh^2\mu_h(n,0).
\]

The squared Frobenius norm is $n(n-1)^2+n(n-1)=n^2(n-1)$. Applying Theorem 1.2 to $(nI-J)/\sqrt{n-1}$ gives the displayed bound with $8e^2$. Nonnegativity comes from the manuscript's positive moment formula. The standing hypothesis $n\ge2$ avoids a zero scaling denominator. The source supplies an inequality, not the manuscript's mixed-class attainment assertion.

### AV7-C2. Permanent coefficient and bibliography

Accepted. Expanding the permanent directly gives

\[
\frac{n^n}{n!}\operatorname{Perm}\left(\frac{J+t(nI-J)}n\right)
=\mathbb E\prod_{i=1}^n(1+t(n\mathbf1_{\sigma(i)=i}-1)).
\]

Every subset of $h$ rows has the same expected product. Its coefficient is therefore $\binom nh\mu_h(n,0)$. The inspected [earlier preprint, equation (29) and Lemma 5.5](https://arxiv.org/pdf/2408.09341v3), printed pages 23 and 25, contains the corresponding homogeneous permanent expansion and bound. For $0\le t<1$, this matrix is doubly stochastic and positive semidefinite, with eigenvalues $1,t,\ldots,t$. Thus the cited overlap is concrete.

The journal volume and pages are independently confirmed by reference HN26 in the later authors' preprint. The publisher DOI endpoint was unavailable during this check. The manuscript correctly identifies its equation and lemma locators as belonging to the inspected preprint. No journal-body numbering is certified here.

### AV7-C3. Laguerre parameter comparison

Accepted. The substitution degree $k$, parameter $-N-1$, argument $-N$ gives $A_k=(N+1)/k$. In the inspected [Kuijlaars and McLaughlin preprint](https://arxiv.org/pdf/math/0204248v1), equation (7.1), Theorem 7.1 and Remark 5.4 require a finite limiting ratio in $(1,\infty)$, with the stated uniformity on compact parameter sets. This supports the new interior proportional-degree wording.

The [Dai and Wong institutional abstract](https://scholars.cityu.edu.hk/en/publications/global-asymptotics-for-laguerre-polynomials-with-large-negative-p/) announces the same finite-ratio regime. Its full journal body was unavailable, so the word “announced” is appropriate. The inspected [Dunster-Gil-Segura preprint](https://arxiv.org/pdf/1705.01190v1), equation (1.6) and Cases 1a, 1b and 2 on page 3, has $\alpha=(k+1/2)(a^2-1)$ with $a\ge0$. Thus $\alpha\ge-k-1/2>-N-1$ for $k\le N$, confirming the stated exclusion. The [published Dai-Ismail-Wang PDF available through a mirror](https://www.researchgate.net/profile/Pinchas-Malits/post/Infinite_order_of_Laguerre/attachment/60244a22fcc1e200015b864c/AS%3A989770188611584%401612991010629/download/Asymptotics%2Bfor%2BLaguerre%2Bpolynomials%2Bwith%2Blarge%2Border%2Band%2Bparameters.pdf), Theorem 1 on printed page 16, assumes positive $\alpha_n$ and $\alpha_n/n\to\infty$. Its primary text supports the sign comparison. Direct publisher access was unavailable. The discussion no longer treats those particular domain exclusions as excluding other classical methods.

### AV7-C4. Whittaker overlap and parity

Accepted. The directly inspected [DLMF 13.20(iii)](https://dlmf.nist.gov/13.20.iii) gives equations 13.20.11 and 13.20.12 on $x>0$, $-(1-\delta)\mu\le\kappa\le\mu$, and attributes them to Olver. Put $\kappa=N/2-k$, $\mu=(N+1)/2$. For $0<c<1$, $k\le cN$, choosing $\delta=1-c$ gives

\[
\kappa+c\mu\ge\frac{(1-c)N+c}{2}>0,
\qquad \kappa<\mu.
\]

Thus the domain claim holds, including the sublinear range. This audit inspected the DLMF formulas and the [Olver publisher synopsis and metadata](https://doi.org/10.1017/S0308210500012130), not the original article body or its internal theorem numbering.

The connection is nonsingular at these parameter values. Using [DLMF 13.14.2, 13.14.3 and 13.14.32](https://dlmf.nist.gov/13.14), or directly using the [Kummer integrals 13.4.1 and 13.4.4](https://dlmf.nist.gov/13.4), gives

\[
Q_k=k!e^{-N/2}N^{N/2}
\left(\frac{M_{\kappa,\mu}(N)}{(N+1)!}
 +(-1)^k\frac{W_{\kappa,\mu}(N)}{(N-k)!}\right).
\]

The Kummer parameters are $a=k+1$ and $b=N+2$, so all real-integral conditions hold for $0\le k\le N$. The two terms are positive before the parity sign. Individual relative errors cannot simply be subtracted to obtain an odd-moment relative error. The manuscript explicitly preserves that limitation. It asserts a classical route and domain overlap, not an unchecked uniform error transport.

### AV7-C5. Exact Gamma integral

Accepted by direct reconstruction. Expanding $(N-s)^k$ gives

\[
\frac1{(N-k)!}\int_0^\infty e^{-s}s^{N-k}(N-s)^k\,ds
=\sum_{j=0}^k\binom kj(-1)^{k-j}N^j\frac{(N-j)!}{(N-k)!}.
\]

Multiplying the indicator expansion of the diagonal centered moment by $(N)_kN^k$ gives exactly this sum. The split substitutions contribute $N^{N+1}e^{-N}$, with sign $(-1)^k$ only on the upper half. No factorial or power of $N$ is missing.

For $0<k<N$, the logarithmic derivatives of the two integrands are

\[
\frac{k-Nt^2}{t(1-t)},\qquad
\frac{k-Nt^2}{t(1+t)}.
\]

Each has its unique interior maximum at $\sqrt{k/N}$. At $k=0$, the stationary point is the boundary $t=0$. The endpoint $k=N$ is correctly excluded from the interior stationary-point sentence. The integral remains exact there. Standard Laplace analysis can therefore supply an alternative route, while parity cancellation and low fixed orders remain matters to handle. The manuscript's own accepted proofs do not depend on treating this discussion paragraph as a new uniform proof.

### AV7-C6. Wording and priority scope

Both v6 wording notes are resolved. AV6-E1 is fixed by $1\le h<a$ in the introduction and discussion. AV6-E2 is fixed by “exact asymptotic worst-case constant” in the guide.

The contribution discussion distinguishes known identities and methods from the finite mixed maximum, acknowledges the direct HN overlap, and labels the historical search as bounded. The guide makes the same distinction. No claim that every equivalent classical formula has been excluded remains. This acceptance does not upgrade the bounded search to a theorem about historical priority.

## Verification and reader findings

All 31 extracted theorem, lemma, proposition, corollary, definition, example, remark and proof blocks are byte-identical to v6. The theorem-bearing section files, including the mixed proof, asymptotics, rates and Appendix A, have unchanged hashes. Changed source files are limited to the introduction, discussion, bibliography and guide. Three regenerated figure PDFs render identically to v6 at the checked resolution.

Both documents were rebuilt in three passes from the frozen sources, with all outputs confined to the owned review prefix. The extracted text is identical to each supplied PDF. There are no compilation, reference, citation, overflow or underflow warnings. The main PDF has 32 pages and the guide has seven.

Visual inspection covered main pages 3, 26, 27, 28, 29, 31 and 32 and guide pages 6 and 7. The new formulas, source locators, parity explanation and final guide caveat are readable. No clipping, collision or broken reference was found. This was delta inspection, not a second visual pass over all unchanged pages.

Exact arithmetic also checked 1,323 Gamma-sum cases against the recurrence for $2\le N\le50$, $0\le k\le N$. The matrix polynomial and permanent coefficient identities each passed all 25 cases with $2\le n\le6$, $0\le h\le n$. These finite checks corroborate normalization. The algebra above supplies the general deductions.

No repair is requested. The integrator may record v7 as accepted for this source and wording delta, preserving the v6 mathematical acceptance and the explicit limits on novelty and inaccessible original journal bodies. The separate one-conflict packet was not used as input and is outside this decision.
