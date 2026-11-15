# First review of the directed-spectrum submission

## Outcome

Rejection for correction, not acceptance. The normal aperiodic reduction and the exact peripheral-spectrum index are useful, but the arbitrary-period construction and the complex Ihara-Bass assertion are false as written.

## Fatal issues

1. The argument that $P_m\otimes A_{D_0}$ has period $m$ because $P_m$ acts freely by automorphisms is invalid. For the line digraph of $K_{3,3}$ and $m=3$, the input has period 2 and the constructed matrix has period 6, not period 3. The peripheral spectrum and $\operatorname{lcm}(m,\operatorname{period}(D_0))$ must be analyzed. Thus the arbitrary-period attainment claim does not follow. Starting with an aperiodic construction and proving that the lift has period exactly $m$ is a possible repair for suitable degrees, not a proof for every $k$.

2. Proposition 4 asserts for complex $\lambda$ that $|\lambda|\le2\sqrt k$ is equivalent to $|\mu|=\sqrt k$ for a root of $\mu^2-\lambda\mu+k=0$. At $k=1$ and $\lambda=2i$, the roots are $i(1\pm\sqrt2)$, with moduli $\sqrt2\pm1$, not $1$. Restrict to real $\lambda$ in $[-2\sqrt k,2\sqrt k]$, or state an appropriate complex-domain version.

3. The double-cover proposition needs a clean SVD statement. Its displayed union $\{\pm\sigma_i(A)\}$ followed by a zero contribution is incorrect as an unqualified multiset statement. The $\lambda_2=\sigma_2$ consequence needs the connected Perron setup and the usual second singular value. Also, $\sigma_2(A)\ne\lambda_2(G)$ for a general symmetric digraph, as $K_4$ gives $\sigma_2=1$ and signed $\lambda_2=-1$. Use the non-Perron absolute eigenvalue here. These corrections preserve the intended universal lower bound, but the asserted equalities cannot remain as written.

4. The exact-tree calculation is missing the root degree. For the 2-regular tree the closed length-two walk count at a root is 2, while the displayed formula $(k-1)^t\mathrm{Cat}_t$ gives 1 at $k=2,t=1$. Use $k(k-1)^{t-1}\mathrm{Cat}_t$ in that case, or derive the general formula explicitly.

## Source and reproduction checks

The selected scripts `exact_examples.py`, `periodic_and_line.py`, and `line_digraph_transfer.py` ran successfully. Numerical pathological behavior in eigenvalue computation was not a disguised proof. The exact_examples output marks $K_{3,3}$ and Heawood as `Ramanujan=False` under its chosen modulus test, contradicting the narrative's assertion that all seven examples are Ramanujan. The separate transfer simulation classifies them as Ramanujan under its different criterion. This demonstrates exactly why inherited and peripheral eigenvalues need consistent definitions.

Parzanchevski Section 5.3 already records Ramanujan line-digraph constructions. Thus the line-digraph sharpness is already supported by the cited literature, and its novelty should not be overstated.

## Retained counterexample evidence

See [d6_counterexamples.py](d6_counterexamples.py) and [d6_counterexamples.json](d6_counterexamples.json). The period test examines closed walks up to $5n$ steps and obtains period 2 for the line digraph of $K_{3,3}$ and period 6 for $P_3\otimes A_{D_0}$. The quadratic roots and exact symmetric adjacency identities were also checked numerically.

## Required resubmission standard

Repair the period, complex-domain, signed-versus-singular, and multiset formulations. Update the narrative and raw-data interpretations to use one consistent notion of trivial spectrum. Keep open cells only after checking how the corrections affect them. The ordinary aperiodic normal argument, Proposition D, and the real Joukowski correspondence can be retained.
