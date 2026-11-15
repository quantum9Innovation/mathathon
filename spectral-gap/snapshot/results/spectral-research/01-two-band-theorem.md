# First internal-gap statement: a biregular two-band base

## Assessment

There is enough for a rigorous specialization of modern quantitative strong convergence. There is not yet enough for an optimal tangle-controlled theorem. No matching lower bound or certified novelty claim is made here.

Updated 14 November 2026 after checking the relevant definitions and primary statements of Huang-Xu, Bordenave-Collins, and Chen-Garza-Vargas-Tropp-van Handel.

## 1. Concrete model

Take $H=K_{4,3}$. Its first side has four vertices of degree 3, and its second side has three vertices of degree 4. Its biadjacency matrix is the rank-one all-ones 4 by 3 matrix. Hence

$$
\sigma(H)=\{-\sqrt{12},0,0,0,0,0,\sqrt{12}\}.
$$

A uniform random $N$-lift assigns independent uniform perfect matchings between the 12 pairs of fibers. Old functions are constant on each fiber. They have matrix $1_N\otimes A_H$ under the usual tensor convention. Their orthogonal complement is the new space. Write

$$
M_N=A_N\mid_{\mathcal H_N^{\mathrm{new}}}.
$$

The old spectrum contains zero with multiplicity 5. Independently of inherited dimensions, every lift has at least $N$ zero eigenvalues because its biadjacency matrix has shape $4N$ by $3N$. This is why the target interval must avoid zero.

## 2. Two bands and the inner edge

The universal cover is the $(3,4)$-biregular tree. Put $a=3-1=2$ and $b=4-1=3$. At the critical circle $|x|=\sqrt{ab}$, the Ihara-Bass singular-value relation is

$$
\xi^2=x+\frac{ab}{x}+a+b.
$$

The positive singular-value band is $[\sqrt b-\sqrt a,\sqrt a+\sqrt b]$. The two positive and negative adjacency bands therefore have inner edge

$$
\beta=\sqrt3-\sqrt2\approx0.317837245195782.
$$

The relevant intervals are compact $I\subset(0,\beta)$. They avoid zero, all old eigenvalues, and both band edges. The separate zero spectral contribution caused by unequal rectangular geometry must be handled independently rather than hidden in the band approximation.

Complex points on $|x|=\sqrt{ab}$ correspond to the critical singular values. An interior real adjacency gap need not be accompanied by a corresponding excess nonbacktracking radius. This is exactly where an outer-radius-only Hashimoto method becomes too coarse.

## 3. Quantitative strong-convergence input

Chen, Garza-Vargas, Tropp and van Handel, [arXiv:2405.16026v3](https://arxiv.org/abs/2405.16026v3), Theorem 3.9, proves a quantitative norm tail bound for every fixed self-adjoint noncommutative polynomial $P$ with matrix coefficients in independent uniform permutations restricted to mean-zero vectors. For fixed $P$ and positive $\varepsilon$, its consequence is

$$
\Pr\left[\|P(S_N,S_N^*)\|\ge\|P(s,s^*)\|+\varepsilon\right]
\le C_{P,\varepsilon}N^{-1}.
$$

The full statement records the dependence on polynomial degree, matrix dimension, and full-group algebra norm. This is not only a theorem about the adjacency matrix of a random regular graph.

As in Bordenave-Collins Section 1.5, the relative adjacency matrix $M_N$ is such a polynomial with matrix dimension 7 and one inverse-paired color per base edge. The limiting operator $M_*$ on the free representation has the universal-cover spectrum described above.

## 4. First statement: an isolated internal-gap bound

**Statement, a specialization of the quantitative strong-convergence theorem.** Fix a compact interval $I\subset(0,\sqrt3-\sqrt2)$. Let $E_N(I)$ be the event that $M_N$ has an eigenvalue in $I$. There is a constant $C(H,I)$ such that for every $N\ge1$,

$$
\boxed{\Pr[E_N(I)]\le C(H,I)N^{-1}.}
$$

### Proof from the cited inputs

Select a real nonnegative $C_c^\infty$ function $f$ satisfying:

1. $f\ge1$ on $I$.
2. $f=0$ on an open neighborhood of the two universal-cover bands and zero.
3. $f=0$ on an open neighborhood of the old spectrum.

These requirements are compatible because $I$ is compact and strictly separated from those closed and finite sets.

Functional calculus gives $f(M_*)=0$. If $E_N(I)$ occurs through an eigenvalue $\lambda\in I$, then

$$
\|f(M_N)\|\ge f(\lambda)\ge1.
$$

The polynomial $P_f$ obtained by applying $f$ to the linear adjacency polynomial remains a fixed self-adjoint noncommutative polynomial. Applying the quantitative bound with $\varepsilon=1$ proves the assertion, after enlarging $C(H,I)$ to handle the finitely many initial $N$.

**Review status.** This is a direct deduction from an imported theorem, not an independent proof of strong convergence and not a new optimal-rate result.

## 5. The actual research target

Set $p_N(I)=\Pr[E_N(I)]$. A meaningful next theorem would identify

$$
\kappa_I=\lim_{N\to\infty}-\frac{\log p_N(I)}{\log N},
$$

assuming existence, and identify which finite combinatorial mechanism determines it.

One can ask whether $N\Pr[E_N(I)]$ has a nonzero limit, or whether the generic $N^{-1}$ estimate is improvable. The first hypothesis to test is that an order-one relative tangle forces an inner-gap eigenvalue. This is not a theorem yet: a local spectral defect must be tied to a new eigenvalue of the lift, not just to an eigenvalue of an auxiliary graph.

A critical-tangle definition must compare the finite subgraph's tree extension with the particular interval $I$. The usual critical condition based only on the outer Hashimoto radius does not distinguish inner-band behavior from an interior gap.

## 6. Computational checks and their limits

- All $2^{12}=4096$ signed 2-lifts were checked. None has a nonzero eigenvalue strictly below $\beta$. The base matrix is rank one, and numerical eigenvalues agree with $\pm\sqrt{12}$ and five zeros.
- A seeded random study found positive inner-gap eigenvalues in some 8-lifts and larger lifts. The first retained 8-lift witness has eigenvalue approximately $0.22824570$ with multiplicity two. Its complete 12 permutation data are retained.
- There is no deterministic exclusion from the small search, but the numerical hit frequencies are not treated as asymptotic estimates.
- A simple $K_{2,3}$ relative tangle candidate was examined through its symmetric left-vertex mode and an integrated-tree boundary equation. The eliminant simplifies exactly to $(z^2-12)(z^2-10)$, so it has no positive root below $\beta$. See [theta_boundary_checks.py](theta_boundary_checks.py). This is evidence against that easiest order-one obstruction, not a complete classification of order-one candidates and not a proof that $\kappa_I>1$.
- The scalar boundary calculation and the selected numerical witnesses still need independent mathematical review before being used in a sharp theorem.

The base checks and enumeration are in [two_band_checks.py](two_band_checks.py) and [two_band_checks.json](two_band_checks.json). The enumeration is exact combinatorial enumeration with numerical eigensolvers, not a proof of any asymptotic statement.

## 7. What Huang-Xu does and does not settle

[Huang-Xu arXiv:2610.37463v1](https://arxiv.org/abs/2610.37463v1) requires a connected simple base with minimum degree at least three. The chosen $K_{4,3}$ satisfies this, unlike the earlier subdivision proposal.

Section 2.1 formulates the directed-edge Dyson equation, spectral measures, atoms, and regular-edge regimes. Theorem 1.2 estimates eigenvalue counts in the regular bulk down to logarithmic scales over $N$. Theorem 1.3 delocalizes normalized eigenvectors away from singular energies. The off-support and regular-edge analysis are directly relevant here.

Those statements do not by themselves provide the smallest exceptional probability for the first new eigenvalue inside a fixed spectral hole. Zero limiting density in an off-support interval does not imply an $N^{-1}$ first-excursion probability. The special statement above relies on quantitative strong convergence rather than a claim that Huang-Xu already solved the problem.

Huang-Xu excludes neighborhoods of singular energies. Here zero requires exactly that separate treatment. Their theorem should not be paraphrased as controlling every eigenvalue without qualification.

## 8. Exact next proof or computation

1. Verify the scalar $K_{2,3}$ calculation, classify all minimal pruned relative tangles, and compute their possible eigenvalues in the interval.
2. Analyze the retained 8-lift witness and identify the smallest subgraph or other mechanism responsible for its inner-gap eigenvalues.
3. Determine whether that local mechanism forces an eigenvalue in the relative spectrum with a quantitative perturbation estimate.
4. Review source applicability before calling the sharpened problem open in a publication draft.

The deliverable at this stage is a rigorous model and baseline bound with an unresolved sharp problem, not an assertion that the sharp problem has been solved.
