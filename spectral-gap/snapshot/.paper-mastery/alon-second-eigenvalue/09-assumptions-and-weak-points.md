# Assumptions, limitations, and weak points

This file distinguishes **Paper** statements, **Derived** checks, and **Interpretation** about significance. Local source defects are not silently repaired in the other notes.

# Part I: Assumptions and what they do

## A1. Fixed degree and fixed additive error

- **Paper:** $d$ and $\epsilon>0$ are fixed as $n\to\infty$ (Theorems 1.1 to 1.3).
- **Why needed:** The finiteness of types below an order, all tangle probabilities, spectral comparison $\eta(\epsilon)$, and constants in expansion errors use this.
- **Technical convenience or essential:** Fixed $d$ is fundamental to this formulation. Fixed $\epsilon$ is essential to the final logarithmic scale as proved here.
- **Without it:** Growing $d$ requires tracking every $d$-dependent threshold and type count. Letting $\epsilon\to0$ makes $\eta\to0$, so the final choice $\alpha r-1>\tau_{\mathrm{fund}}$ loses uniformity.

## A2. Explicit pseudograph models and parity

- **Paper:** $\mathcal G_{n,d}$ and $\mathcal H_{n,d}$ use even $d$. $\mathcal I_{n,d}$ needs even $n$, and $\mathcal J_{n,d}$ uses odd $n$ and half-loops (Section 1).
- **Why needed:** Feasible tangles, factorial formulas, word alphabets, and adjacency conventions change across models.
- **Technical convenience or essential:** Some parity is forced by existence and model construction. Using pseudographs is a proof choice later bridged to other models.
- **Without it:** A different model requires all six conditions in Section 14 to be checked again.

## A3. Loops and multiplicities counted precisely

- **Paper:** Whole-loops contribute 2 to adjacency, half-loops contribute 1, and each counts as one edge for order (pages 20 and 36).
- **Why needed:** Tangle order and $\lambda_{\mathrm{Irred}}$ determine both the local spectral threshold and its probability exponent.
- **Technical convenience or essential:** Essential arithmetic.
- **Without it:** The $m-1$ order of a one-vertex $m$-loop tangle and the probability $n^{1-m}$ would be wrong.

## A4. Relabelling symmetry and bounded coincidence probabilities

- **Paper:** Walk classes assume vertex-relabelling symmetry, and Section 14 requires a coincidence bound $c/(n-ck)$ after $k$ determined edges (Definitions 5.2 and Section 14).
- **Why needed:** Finite equivalence classes and $k/(n-k)$ coincidence estimates underpin the expansion error.
- **Technical convenience or essential:** Symmetry is structurally essential to this organization. The exact coincidence bound has some room for variation if equivalent controls exist.
- **Without it:** Expansion coefficients need no longer be polynomial in letter counts, and the same truncation proof can fail.

## A5. Expansion coefficients with d-Ramanujan control

- **Paper:** The selective coefficients satisfy $|f_i(k)-(d-1)^kp_i(k)|\leq ck^c(d-1)^{k/2}$ (Definition 2.1 and Theorem 8.1).
- **Why needed:** This separates the tree contribution from the permitted Ramanujan error scale.
- **Technical convenience or essential:** Essential to the spectral trace argument.
- **Without it:** Terms with intermediate growth between $(d-1)^{k/2}$ and $(d-1)^k$ can hide a genuine eigenvalue or destroy the final comparison.

## A6. Sufficiently large $S$ and $B>S$

- **Paper:** Theorem 6.6 and Theorem 8.1 hold after choosing sufficiently large scales.
- **Why needed:** Long-tail generating functions must be small enough for alternating-series convergence.
- **Technical convenience or essential:** The particular values are technical, but the ability to choose them uniformly for each finite type set is essential.
- **Without it:** Denominators in Theorem 6.6 need not stay positive, so the strict base $\sqrt{d-1}-\eta$ need not follow.

## A7. Expansion order $r$ chosen last

- **Paper:** Section 13 chooses the trace length using $r$, then takes $r$ large enough for $\tau_{\mathrm{fund}}$.
- **Why needed:** The sidestepping remainder scales roughly as $n^{1-r/3}$, while the outlier loss depends on $\eta$.
- **Technical convenience or essential:** Essential flexibility.
- **Without it:** A fixed short expansion may only recover the older weaker eigenvalue bounds.

## A8. Positive-order tangles in Theorem 9.3

- **Paper:** $\Psi$ is finite, pruned, nonempty, and of order at least 1.
- **Why needed:** It makes low-order derived tangles finite and permits high-order truncation.
- **Technical convenience or essential:** Essential to the proof given, though the paper says it believes the theorem may extend to cycles.
- **Without it:** Arbitrarily many disjoint cycles yield infinitely many derived tangles of order 0. The existing truncation argument breaks directly.

## A9. External identity and separation inputs

- **Paper:** Ihara-Bass is cited in Theorem 3.13, infinite closed-walk norm facts in Section 3.7, Alon's magnification estimate in Section 12, and contiguity results in Section 1.
- **Why needed:** These connect different spectral representations or models.
- **Technical convenience or essential:** Structurally essential, even though not rederived here.
- **Without it:** The tree threshold, spreader-to-spectrum inference, or model transfer needs an independent proof.

# Part II: Honest limitations of the results and experiments

## L1. No typical exact Ramanujan theorem

- **Paper:** Section 1 and Section 15 explicitly leave $\epsilon=0$ open, as well as negative $\epsilon(n)$.
- **Assessment:** This is a real limitation, not a technicality. The main theorem is near-Ramanujan for every fixed positive additive error.
- **Why the proof stops:** The non-backtracking margin $\eta$ controls both the final expansion order and outlier exponent. It vanishes with $\epsilon$.

## L2. The exponents need not match exactly

- **Paper:** The upper failure exponent $\tau_{\mathrm{fund}}$ is the smallest supercritical order, while the lower exponent $s$ is the smallest hypercritical order. They can differ by 1 (page 3 and Section 15).
- **Assessment:** A genuine information gap at critical equality. The text itself calls this interesting and unresolved.
- **Derived example:** At $d=10$, a two-loop tangle is critical of order 1 and the next loop tangle is hypercritical of order 2.

## L3. Contiguity transfers less than the main explicit rates

- **Paper:** Corollary 1.4 gives probability $1-o(1)$ for dominated models.
- **Assessment:** It does not claim the same implicit polynomial rate in general. A uniform simple graph conclusion through contiguity is qualitative as presented.

## L4. Model transfer is conditional on checklist verification

- **Paper:** Section 14 verifies the six properties for the three additional models.
- **Assessment:** This is good modular design, not a theorem for arbitrary random regular graph ensembles. A new model requires concrete occurrence and word-sum calculations.

## L5. The relative Alon conjecture remains a proposal in this paper

- **Paper:** Section 15 suggests extensions to new eigenvalues of random covers and to a direct analysis of selectivity.
- **Assessment:** These are research directions, not results proved here. No later literature is imported into this dossier to settle them.

## L6. No experimental validation is displayed

- **Paper:** Section 15 mentions numerical experiments suggesting a negative average $\epsilon(n)$.
- **Assessment:** There are no numerical values, datasets, methods, plots, or experimental tables in this paper. Nothing empirical can be reproduced from that remark alone. The proof is theoretical.

## L7. No formal verification of every line is claimed by this dossier

- **Derived:** All pages and both figures were read, and central arguments were expanded. Not every numerical constant, tail bound, automorphism enumeration, or model-specific special case was independently exhaustively recomputed.
- **Assessment:** No fatal gap in the main $\mathcal G_{n,d}$ architecture was identified. That is not equivalent to referee-grade certification or a Lean-checked proof.

# Part III: Specific source defects and unresolved tensions

## W1. Incorrect value $q_k(d)$ on page 12

- **Paper:** Immediately below Lemma 2.6's setup, the text says $q_k(d)=(d-1)^k$.
- **Derived check:** Lemma 2.3 gives $q_1(x)=x$, hence $q_1(d)=d$. Applying $A_k$ to the constant vector gives
  $$q_k(d)=d(d-1)^{k-1}$$
  for every $k\geq1$. Theorem 2.7 also states the consistent leading term $d(d-1)^{k-1}$.
- **Severity:** Clear local algebraic defect. The surrounding recurrence and later statement make the intended correction evident. It should not be quoted as printed.

## W2. Square root inconsistency in Theorem 6.10, pages 68 and 69

- **Paper:** For the $d=6$ tangle, the text says $\lambda_{\mathrm{Irred}}(\psi)$ is the square root of the Perron value of
  $$M=\begin{pmatrix}4&2\\6&1\end{pmatrix},$$
  computes $\lambda_1(M)=(5+\sqrt{57})/2$, and then says this $\lambda_1$ is just $\lambda_{\mathrm{Irred}}(\psi)$.
- **Derived check:** The two-step walk reduction requires $\lambda_{\mathrm{Irred}}=\sqrt{\lambda_1(M)}$. Since $\lambda_1(M)>6$, the intended $\lambda_{\mathrm{Irred}}>\sqrt6>\sqrt5$ follows.
- **Severity:** Local notation or proofreading defect with an evident correction. The threshold conclusion survives under the square-root reading. Directly identifying the Perron value with $\lambda_{\mathrm{Irred}}$ would also clash with the bounded non-backtracking outdegrees.

## W3. Reversed inclusion in Lemma 9.2, page 82

- **Paper:** After deleting type edges whose lengths diverge, the final contradiction says $\psi_\infty$ properly contains all $\psi_i$.
- **Derived check:** Deletion gives a smaller graph $\psi_\infty$ contained in sufficiently large $\psi_i$. That smaller graph has lower order and retains supercritical growth, contradicting minimality of $\psi_i$. The next paragraph's statement that a $\psi_i$ occurrence implies a $\psi_\infty$ occurrence agrees with this smaller-graph direction.
- **Severity:** A literal reversal in a central lemma's proof. The surrounding construction supplies a coherent intended reading, but the printed sentence cannot stand unmodified.

## W4. $\mathcal J_{n,d}$ exponents are not reconciled

- **Paper:** Theorem 1.3 says Theorem 1.1 holds with $\mathcal G_{n,d}$ replaced by $\mathcal J_{n,d}$. That imports
  $$\tau_{\mathrm{fund}}=\left\lceil\frac{\sqrt{d-1}+1}{2}\right\rceil-1,
  \qquad s=\left\lfloor\frac{\sqrt{d-1}+1}{2}\right\rfloor.$$
  Theorem 6.12 instead proves $\tau_{\mathrm{fund}}(\mathcal J)=\lceil\sqrt{d-1}\rceil-1$, while Theorem 4.13 uses $s=\lfloor\sqrt{d-1}\rfloor$. Section 12.4 confirms that $\mathcal I$ and $\mathcal J$ share tau.
- **Derived check:** The lower occurrence rates in Theorem 4.13 apply to explicit hypercritical tangles. Their larger exponent cannot generally be weakened to the smaller Theorem 1.1 exponent by monotonicity, because a lower bound of order $n^{-s}$ with larger $s$ is smaller as $n\to\infty$.
- **Severity:** The most substantive presentation tension identified here. For the upper high-probability Alon conclusion, the larger computed failure exponent implies the weaker imported rate, so the qualitative result is unaffected. For the lower probability of $\lambda_2>2\sqrt{d-1}$, the supplied proof does not reconcile the imported stronger statement. This dossier does not assert it false, but recommends quoting the detailed Theorem 4.13 exponent pending an external erratum or separate proof.

## W5. Figure 2 has an abstract-name ambiguity

- **Paper:** The figure labels the branch vertex `4 (or v2)`, while adjacent text proposes replacing first vertex 5 by $v_1$, second vertex 2 by $v_2$, and so on.
- **Derived check:** First-visit naming would make $4=v_3$ in the form. After suppression, vertex 4 is the second surviving type vertex after 5, so $v_2$ is coherent only for the type's renumbering.
- **Severity:** Visual presentation ambiguity, not a mathematical problem in the walk data. The full reconstruction is in the visual inventory.

## W6. Sign typo in the discussion after Equation 35

- **Paper:** Equation 35 decomposes a finite convolution into $\Sigma_1-\Sigma_2$, while the sentence after the subsequent estimates calls $\Sigma_1(k)+\Sigma_2(k)$ the decomposition into principal and error terms (pages 77 to 80).
- **Derived check:** The established formula is $\Sigma_1-\Sigma_2$. Since $\Sigma_2$ is an error term whose absolute value is bounded, changing its formal sign does not affect the final magnitude bound.
- **Severity:** Minor local sign typo, easily normalized when reading but included here for completeness.

## W7. Figure 2 does not depict a strongly irreducible example

- **Paper:** Figure 2 is introduced as a possible contribution to $\operatorname{IrredTr}(A,10)$, not to $\operatorname{SIT}$. Strong irreducibility is defined much later on page 89.
- **Derived check:** The word begins $\pi_2^{-1}$ and ends $\pi_2$. Across the cyclic closure, the last letter is the inverse of the first, so the walk is not strongly irreducible.
- **Severity:** Not an error, because Section 5 has not introduced strong traces. It is a reading trap if one carries the example forward without checking the cyclic condition. The dossier makes that distinction explicit.

# Part IV: Concerns that should not be exaggerated

- **Loops and multiple edges are not a hidden flaw.** They are explicit in $\mathcal G_{n,d}$, and transfer to other models is addressed separately.
- **Unknown expansion coefficients are not an omitted calculation.** Their avoidance is the purpose of Lemma 11.1.
- **Deleting selective walks is not automatically a gap.** Section 9 and the tangle-free identity in Section 13 are specifically designed to close it, subject to the scrutiny of their local defects.
- **The visual sparsity is not missing evidence.** This version has two mathematical diagrams and no claimed empirical plots to inspect.
- **The version issue is not silently resolved.** The supplied arXiv v1 PDF is the object studied. A later memoir edition may correct defects or alter statements, but it was not bundled into this digest or used to overwrite the supplied text.

# Strongest remaining objections to use in an oral defense

1. Can you justify the transition from Theorem 6.6's typewise convergence to a uniform sum over every relevant new type and multiplicity?
2. Can you explain exactly why Lemma 9.2's intended inclusion direction proves minimality finiteness?
3. Can you show that the $\Omega$-type modifications add only polynomial-in-$k$ losses and preserve the selective walk bound?
4. Can you derive Lemma 11.1's reality and circle conditions from the $\mu$ root representation?
5. Can you account for the implicit constants when $r$ is chosen after $\eta$, and explain why they remain fixed as $n$ grows?
6. Which exact $\mathcal J_{n,d}$ lower probability exponent are you quoting, and which theorem justifies it in this arXiv version?

These are the places where a detailed understanding matters more than reciting the main theorem.
