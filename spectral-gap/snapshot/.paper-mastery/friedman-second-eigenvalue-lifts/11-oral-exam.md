# Oral exam

## Exam protocol

Run one question at a time. Ask for a response before showing the model answer. Grade first against the listed criteria, identify the strongest correct part and the precise gap, then reveal the model answer when useful. Do not give hints unless the user requests one or is stuck. A correct answer need not reproduce the model wording.

## Current question

Question 1 has been posed. Wait for the user's answer, grade it, and then decide whether Question 2 or a short repair example is the better next step.

## Level 1: comprehension and retrieval

### Question 1: the two figures and their two jobs

**Prompt.** Without consulting the notes, explain:

1. In Figure 2, why does summing separately over tangle-free prefixes and suffixes overcount the original tangle-free path family? Which set difference defines the remainder?
2. In Figure 4, times $4,7,10$ are all important times. Why do they not require three independent cycle marks? Name their roles and connect them to cycle rank.

**Rubric.** Four points, one for each item:

- Separate pieces may each contain one cycle while their union contains two.
- The remainder is supported on $F_k^\ell\setminus F^\ell$, not merely on arbitrary tangled paths.
- Time $4$ is the short cycling time, while times $7$ and $10$ are superfluous returns through the same unique cycle.
- Only genuinely new excess edges require long-cycle marks. Their number is controlled by $g$, not by the total number of returns.

**Model answer.** The original family $F^\ell$ requires the entire support $G_\gamma$ to have at most one cycle. Splitting $\gamma$ into $\gamma',\gamma'',\gamma'''$ and requiring only each piece to be tangle-free gives the larger family $F_k^\ell$. As in Figure 2, orange and cyan pieces can each have a cycle, so their union has two. The matrix-product term therefore counts $F_k^\ell$, whereas the target counts $F^\ell$. The correction is precisely the contribution of $F_k^\ell\setminus F^\ell$, assembled into $R_k^{(\ell)}$.

In Figure 4, first visits construct a spanning tree, and an important time uses an excess edge. The first return at time $4$ closes the unique triangle and is designated short cycling. Times $7$ and $10$ traverse the same excess edge again and are superfluous. They do not create new independent cycles. One enhanced short-cycle mark can encode all repeated tours, while other excess edges are recorded by long-cycle marks. The latter are bounded using $g=a-s+1$, so entropy is controlled by independent cycles rather than raw revisit counts.

### Question 2: deletion and centering in the correct order

**Prompt.** Define $B^{(\ell)}$ and $\underline B^{(\ell)}$ in words. Why is $\underline B^{(\ell)}$ generally different from $\underline B^\ell$ even on an $\ell$-tangle-free configuration?

**Rubric.** Checks the tangle-free path restriction in both definitions, the centered weight, and the presence of negative off-match contributions. Recognizes the phantom-path mechanism.

**Model answer.** $B^{(\ell)}$ sums products of uncentered matching entries over tangle-free non-backtracking paths. $\underline B^{(\ell)}$ sums the same restricted paths after replacing $M$ by $\underline M=M-(dn)^{-1}\chi\chi^*$. The centered entry is $1-1/(dn)$ on a matched pair but $-1/(dn)$ off a matched pair. Thus $\underline B^\ell$ gives nonzero weight to combinatorial paths that were impossible under $M$. On a globally tangle-free configuration these phantom contributions can have tangled supports, so $\underline B^\ell$ need not equal the tangle-free restricted matrix $\underline B^{(\ell)}$.

## Level 2: technical reconstruction

### Question 3: telescoping at $\ell=2$

**Prompt.** Let $x_s=M_{\gamma_{2s-1}\gamma_{2s}}$ and $y_s=\underline M_{\gamma_{2s-1}\gamma_{2s}}$. Expand $x_1x_2$ in terms of $y_1y_2$ and correction terms. What does each correction represent after summing over paths, and where can Figure 2 invalidate exact factorization?

**Rubric.** Checks exact algebra, the $1/(dn)$ correction size, mixed centered and uncentered segments, and awareness of the splice overcount.

**Model answer.**

$$
x_1x_2=y_1y_2+(x_1-y_1)x_2+y_1(x_2-y_2).
$$

The first term keeps both weights centered. The other terms center only after position $1$ or before position $2$, with one correction $x_s-y_s=1/(dn)$. After path summation, these mixed products attempt to factor into lower-length centered and uncentered matrices. But at the splice, separate tangle-free restrictions do not imply global tangle-freeness, so the $F_k^\ell\setminus F^\ell$ correction must be retained.

### Question 4: cycle rank versus important times

**Prompt.** In Lemma 16's encoding, for a connected trace support with $s$ vertices and $a$ distinct visited pairs, prove that the number of distinct excess edges is $g=a-s+1$. Explain why the number of important times can nevertheless be much larger than $g$.

**Rubric.** Uses a spanning tree and distinguishes edge multiplicity from distinct support cardinality. Figure 4 should supply a valid example.

**Model answer.** A spanning tree has $s-1$ edges. Every other distinct support edge is an excess edge, so there are $a-(s-1)=a-s+1=g$. Important times record traversals, not distinct edges. The same excess edge may be traversed repeatedly. In Figure 4, distinct excess support consists only of the chord $4-2$, but that chord is used at times $4,7,10$. Tangle-freeness lets the encoding absorb these repeated traversals into the short cycling mark instead of assigning each a new independent mark.

### Question 5: recover the deterministic norm reduction

**Prompt.** Starting from

$$
B^{(\ell)}=\underline B^{(\ell)}
+\frac{d-1}{dn}\sum_k\underline B^{(k-1)}\chi\chi^*B^{(\ell-k)}
-\frac1{dn}\sum_kR_k^{(\ell)},
$$

show what happens when this acts on $x\perp\chi$ on an $\ell$-tangle-free graph. Why does $\underline B^\ell$ fail to give the same path-restricted conclusion?

**Rubric.** Correctly uses $B^{(\ell)}=B^\ell$ and $\chi^*B^{(j)}=(d-1)^j\chi^*$, then obtains Proposition 8's two norms and explains phantom paths.

**Model answer.** On the good event, $B^{(\ell)}=B^\ell$ and $\chi^*B^{(j)}=(d-1)^j\chi^*$. Therefore $\chi^*B^{(\ell-k)}x=0$, so the middle sum vanishes. Hence

$$
B^\ell x=\underline B^{(\ell)}x-\frac1{dn}\sum_kR_k^{(\ell)}x.
$$

Taking norms and applying the eigenvalue restriction gives Proposition 8. $\underline B^\ell$ does not provide this tangle-free path decomposition because centered off-match entries contribute negative weights to phantom paths. It contains additional terms outside $F^\ell$ that the matrix $B^{(\ell)}$ never contained.

## Level 3: research defense and extensions

### Question 6: can the remainder simply be dropped?

**Prompt.** Suppose someone discards $R_k^{(\ell)}$ from Proposition 8. What raw norm scale would they lose in their final bound if they keep it instead? Why can the paper tolerate the remainder's $(d-1)^\ell$ scale?

**Rubric.** Compares $(d-1)^{\ell/2}$ with $(d-1)^\ell$, includes the $1/(dn)$ discount, and uses $\ell\sim\kappa\log_{d-1}n$ with $\kappa<1/4$.

**Model answer.** Dropping $R_k^{(\ell)}$ loses the exact action of $B^\ell$ on $\chi^\perp$. The remaining matrix need not represent the desired spectral operator. With the remainder retained, its total norm is of raw order $(d-1)^\ell$, much larger than the centered scale $(d-1)^{\ell/2}$. Proposition 8 multiplies it by $1/(dn)$, giving $O((\log n)^{30}(d-1)^\ell/n)$. Since $(d-1)^\ell=n^{\kappa+o(1)}$ and $\kappa<1/4$, this term is $o(1)$ and does not affect the final $\sqrt{d-1}$ root.

### Question 7: local tangle-freeness versus global trace supports

**Prompt.** Each strand in $W_{\ell,m}$ is tangle-free, but $G_\gamma$ is assigned an arbitrary cycle rank $g\geq0$. Isn't that a contradiction? What would go wrong if individual strands were allowed to be tangled?

**Rubric.** Distinguishes individual path supports from their union and identifies the encoding consequence.

**Model answer.** Tangle-freeness is imposed separately on each $G_{\gamma_i}$. The closed trace support is the union of all these strands, and distinct strands can bring different cycles. Therefore the union may have many independent cycles, parameterized by $g$, without any single strand violating its bound of one cycle. Figure 2 already exhibits this local-to-global effect. Allowing a tangled strand would introduce at least two cycles on one strand, so one short-cycle mark could no longer capture all superfluous returns and Lemma 16's stated entropy control would fail.

### Question 8: is Figure 4 only an illustration, or a proof obligation?

**Prompt.** Figure 4's caption and the $\hat t$ definition have an indexing tension. Identify what a rigorous use of the encoding must establish beyond pointing at the picture. Does this automatically invalidate Lemma 16?

**Rubric.** Requires reconstructibility and careful exit-time conventions, and distinguishes a local source ambiguity from a counterexample to the theorem.

**Model answer.** The encoding must specify exactly when the path leaves the unique cycle, which half-edge or edge records the exit, and how marks allow unique reconstruction using non-backtracking paths on the spanning tree. At the displayed $\hat t=12$, the first half-edge $(3,2)$ belongs to the triangle while the traversed pair exits toward $5$. This requires a clarified convention. The ambiguity does not by itself refute the existence of a compressed encoding or Lemma 16, but a formal proof use should repair and verify the reconstruction rather than silently quoting the figure.

### Question 9: which parts survive random lifts?

**Prompt.** What replaces $\chi^\perp$ in the lift proof, and what remains unchanged about deletion before centering? Which later ingredient changes fundamentally?

**Rubric.** Identifies $H^\perp$, fiberwise permutation centering, the same splice remainder, and base-path growth $\rho$.

**Model answer.** New lift eigenvalues live on $H^\perp$, where vector coordinates sum to zero on each base directed-edge fiber. Centering becomes $\underline M_e=M_e-n^{-1}\chi\chi^*$. Tangled path supports are still deleted before centering, and Figure 2 still forces splice remainders. Proposition 28 changes the random weights from matching entries to fiber permutations. The genuinely new path-counting input is Lemma 31: regular branching is replaced by projected base-path growth $\|(B^*)^s\delta_e\|_1\leq c_\rho\rho^s$.

## Follow-up recommendations after the first response

- If Question 1 is answered accurately, proceed to Question 3 to test algebra rather than recognition.
- If the set inclusion is unclear, use two explicit unicyclic pieces and compute $F_k^\ell\setminus F^\ell$ before repeating Question 1.
- If Figure 4 is clear but centering order is not, ask Question 2 immediately and emphasize off-match negative weights.
- If both parts are difficult, use the small triangle example in the teaching note, re-explain with $s=5$, $a=5$, $g=1$, then repeat the retrieval task before advancing.
