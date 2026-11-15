# Bounded intertwiner moments under positive symmetric omissions

Derived November 15, 2026. This is a new proof packet; every source in the parent regular-frame packet remains frozen. Historical novelty is not certified. The assertion below is strictly narrower than minimum total degree three: every active factor must have a positive strict omission weight.

## The frame and the positive certificate

Fix a connected nonnegative integer frame `F=(d_ij)`, positive integer size multipliers `a_i`, and reversibility

`a_i d_ij=a_j d_ji`.

Type `i` contains `n_i=a_i N` physical vertices, of total degree `d_i=sum_j d_ij`. These totals may differ. Use independent uniform internal stub pairings and cross-stub bijections, exactly as in the parent configuration model, counting internal loops twice in adjacency. Admissible scales satisfy internal stub parity. Let `D=max_i d_i` and `dmin=min_i d_i`.

Assume a symmetric certificate on **every active factor**, including internal factors:

```
theta_ij=theta_ji,
0<theta_ij<1/2,
sum_j d_ij theta_ij=1 for every i.                     (P)
```

Absent factors have no weight or term. The condition forces `dmin>=3`. A real certificate may be chosen rational if desired: the affine constraints have rational coefficients and the strict box is open in their rational affine solution space. The graph law and algorithm do not depend on which certificate is chosen.

## Main theorem

Let `A_N` be the adjacency matrix. For every fixed prime `p` and dimension `r`, there is a finite constant `C=C(F,a,p,r)` such that, uniformly over `R in Mat_r(F_p)`,

`sup_(N admissible) E #{Y in F_p^(n by r): A_N Y=Y R} <= C`.

The bound also holds after directly conditioning all factors on simplicity, at scales where the simple factors exist. This is precisely the independent uniform simple internal-regular and cross-biregular frame law. No contiguity argument is needed for this unbounded expectation.

No growing-field, growing-frame, zero active omission, half-weight boundary, or all-minimum-degree-three assertion is made. The common-degree theorem is recovered by `theta_ij=1/d`, but equality of the `d_i` is not required here.

## 1. Exact count and weighted entropy identity

The labeled-star type count is exactly the same factorial expression as in the frozen regular-frame packet, with local lengths `d_i`: vertex-profile multinomials times pooled cross factors `prod m_ij!/(n_i d_ij)!` and internal factors

`[prod_x(m_ii(x,x)-1)!! prod_(x<y)m_ii(x,y)!]/(n_i d_ii-1)!!`.

Internal tables must be symmetric with even diagonal, and cross tables must reverse. Loops and repeated physical slots remain present. The root labels are already assigned by the profile multinomial.

Writing `P_i` for star laws, `nu_ij` for pooled pair laws, and normalizing per `N`, the entropy exponent is

```
Phi=sum_i a_i H(P_i)
    -sum_(i<j) a_i d_ij H(nu_ij)
    -sum_i (a_i d_ii/2)H(nu_ii).
```

There are polynomially many types, and each type contribution is `exp(N Phi+O(log(N+1)))`, uniformly including zero entries.

Symmetrize slots only within one old target type. This preserves pooled tables and legal sums while increasing star entropy. At a symmetric star, omission of any slot is lossless because the omitted label is uniquely determined. Let `J_it` be the conditional total correlation of all retained neighbors given the root and `I_ij` the root-neighbor mutual information. Average the lossless chain rule with weight `theta_it` on slot `t`:

```
H(P_i)=(2-d_i)H(mu_i)
       +sum_j d_ij(1-theta_ij)H(nu_ij)
       -sum_t theta_it J_it.
```

Reversibility, symmetry, and the unit-row certificate cancel every root entropy. The exact identity is

```
Phi= -sum_(i<j) a_i d_ij(1-2theta_ij)I_ij
     -sum_i (a_i d_ii/2)(1-2theta_ii)I_ii
     -sum_i a_i sum_t theta_it J_it <=0.                (1)
```

Every present mutual-information coefficient and **every physical omission coefficient** is positive. Thus a zero forces all pair mutual informations and all omission total correlations to vanish. An unsymmetrized zero has no entropy gain under symmetrization and is already symmetric. The full details and exact relation to the frozen strict-weight entropy source are in [boundary-positive.md](boundary-positive.md).

## 2. Every phase and the closed induction class

At zero, conditional on a root, every retained `d_i-1` neighbor tuple has its root-independent product law. The finite-group reflection/translation lemma applies because `d_i>=3`: every marginal is uniform on an affine coset of one common neighbor subspace. Consequently the root subspaces are constant on even-walk components of the connected old-type support.

- For nonbipartite support, use one alphabet `V` and type-dependent linear maps `T_i:V->V`. Phases have one common `H<=V`, preserved by every `T_i`, with cosets `c_i+H` satisfying `T_i c_i-sum_j d_ij c_j in H`.
- For bipartite support, use alphabets `V_L,V_R` and maps `T_i:V_side(i)->V_opposite(i)`. Phases have `H_L,H_R`, with the corresponding inclusions and quotient coset equations on the opposite side.

An internal factor is an odd self-incidence in this support. Repeated physical slots do not create extra parity components. For each phase the legal star law is uniquely uniform on its affine legal support. There are finitely many phases. A proper phase strictly reduces the common dimension, or the sum of the two side dimensions. The restricted maps are still in the same class. The all-zero-dimensional system has exactly one assignment.

This argument is precisely where `theta>0` on every active factor is used. With a zero weight, some omission defects need not vanish and the same phase classification has not been proved here.

## 3. The mixed-degree central estimate

[central-positive.md](central-positive.md) proves this input in full rather than appealing to the earlier common-degree statement.

Retain a table for each physical slot. At type `i`, let `V_i` be the root alphabet and `U_i` the common neighbor alphabet. Let `P` sample a uniform legal star and `Q` sample root and all `d_i` neighbors independently uniformly. Put

`K_N=prod_i [|V_i||U_i|^(d_i-1)]^(n_i)`.

With the exact pooled pairing weight `W`,

```
E Z=K_N E_P W,
K_N E_Q W=prod_i(|V_i|/|U_i|)^(n_i).                   (2)
```

For one common alphabet the last product is one. In the bipartite induction it is `(u/v)^(n_L-n_R)`. The required equality of total physical side sizes follows from `(P)`, not from common degree:

```
sum_(i in L)n_i
 =sum_(i in L,j in R)n_i d_ij theta_ij
 =sum_(j in R,i in L)n_j d_ji theta_ji
 =sum_(j in R)n_j.                                    (3)
```

Therefore `K_N E_Q W=1` in both induction classes. The normalized weighted `Q` law is exactly a random configuration with iid uniform vertex labels. This identity remains true for every restricted pair of side alphabets.

Local full-slot covariance is identical for `P,Q` and positive on the common-root-row real space:

`Sigma_i=(|V_i||U_i|)^(-1)[Id+(d_i-1)Pi_row,i]`.

The maximal legal lattice has index `|U_i|^(|V_i|)` in the unrestricted local lattice, by the same three-slot additive-character calculation, valid for each `d_i>=3`. Uniform exponential tilting and maximal-lattice Fourier inversion on a fixed neighborhood give

```
P(M=m)/Q(M=m)<=C I exp(C||Delta||^3/N^2),
I=prod_i |U_i|^(|V_i|),
```

and ratio `I(1+o(1))` in the `sqrt(N)log N` window. The estimate is relative, includes every lattice period, and proves positive mass at the relevant central affine-lattice points.

Under the exact weighted reference law, stub-permutation transpositions change at most four physical incidences and a root-label change affects at most `2D`. The exposure martingale has `O(N)` bounded increments, so full-table deviations are subgaussian at scale `sqrt(N)`. Internal loops contribute only `O(1)` mean bias. Integrating the cubic likelihood ratio against this subgaussian tail removes the surrounding fixed neighborhood with no polynomial loss. The exact reference normalizer bounds the inner window by `I+o(1)`. Thus the full-uniform contribution has finite limsup.

## 4. Proper phases: mixed-degree boundary bound

Quotient by a proper phase and subtract its type-constant quotient point map. The defect solves the homogeneous quotient equations. A fixed defect assignment has an affine fiber, empty or of size exactly the lower-dimensional homogeneous kernel count `Z_H(G)`.

For support `S`, let `s=|S|`, let `i` incident edges be internal to `S`, `j` go outside, and `ell` exterior vertices be reached. Every reached exterior zero vertex receives at least two support incidences, counted with multiplicity. Hence

```
2i+j=sum_(v in S)d_v>=dmin s,
ell<=j/2,
E=i+j<=D s,
E-(s+ell)>=(dmin-2)s/2.                               (4)
```

The exact forcing couplings for cross bijections and internal pairings do not depend on the total degree. Each prescribed edge takes at most one switch, gives exactly the uniform law conditional on that pair, preserves earlier pairs, and changes at most four physical rows. Therefore

`E[Z_H|certificate]<=p^(4r_* E) E Z_H`.

Combining this correlation-safe rank charge with the actual prescribed-stub probabilities and placements gives

```
E #{solutions with s defects}
 <=M_H(N) D s L^s(s/N)^((dmin-2)s/2),                  (5)
```

for a sufficiently small fixed support fraction. The proof and constants are given in [boundary-positive.md](boundary-positive.md). In particular the sum starts at `s=1` in the multigraph law. The whole proper-phase neighborhood is bounded by

`[1+O(N^(-(dmin-2)/2))] M_H(N)`.

The lower-dimensional moment is bounded by induction. No independence between rare defect certificates and the bulk kernel is assumed.

## 5. Completing the theorem and conditioning

Choose the controlled full-uniform neighborhood and the root-coset neighborhoods of the finitely many proper phases. They cover every zero of the continuous entropy exponent `(1)`. On the compact complementary feasible-type region its maximum is strictly negative, so the exact factorial count contributes only `poly(N)exp(-cN)`.

Dimension induction therefore gives a finite limsup of each raw moment. There are finitely many maps at fixed field and dimensions, and finitely many smaller admissible scales, so the supremum bound follows uniformly in the target matrices.

Every independent fixed-degree internal or cross factor has positive limiting simplicity probability. Their finite product remains bounded below. Conditioning gives exactly uniform simple factors because each simple factor has the same number of labeled-stub realizations. A bounded factor in the unbounded expectation proves the simple-model theorem directly, at scales where its factors exist.

## 6. Expected near-quadratic blind recovery

Use the already proved strict-weight structural theorem in the frozen frontier packet: under the present positive certificate, with high probability every nonempty equitable partition into at most a fixed `K` classes is a compatible planted coarsening. Its hypotheses include internal degrees zero or one and varying total degrees. The actual source combines the weighted real one-hot gap, a mixed-degree small-support bound, and a clean unchanged vertex in each old class; no candidate mass lower bound or known size vector is required.

Enumerate all integer candidate matrices `R` of order at most `K`, with nonnegative entries and row sums at most the fixed observed degree bound `D`. For every candidate use the certified sparse-kernel primitive on the nonsymmetric operator

`K_R=I_r tensor A-R^T tensor I_n`.

Obtain and project its complete **right** kernel over a fixed prime field (for example `F_3`), enumerate its `p^(h_R)` vectors by an odometer update, and keep only one-hot matrices with nonempty classes satisfying the original **integer** equation `AY=YR`. Choose an accepted partition of largest class count. The true indicator and frame are included. On the structural event every accepted candidate is a planted coarsening, so the largest has exactly the true classes up to names, and its integer neighbor counts recover the unknown frame.

The existing fully charged certified primitive has per-input expected bit work `soft-O(n^2(h_R+1))`; odometer generation and exact verification take `soft-O(n p^(h_R))`. These bounds include preconditioning, failed trials, certification, field descent, and rare large kernels. The new moment gives `E(h_R+1)=O(1)` and `E p^(h_R)=O(1)` under the simple law, so the **untruncated unconditional expected bit work is soft-O(n^2)** for the fixed finite candidate family. No high-probability small-kernel event is substituted for this expectation.

The algorithm needs `A,K,D`, not the frame, sizes, or certificate. At fixed `K,D` the family of connected qualifying true frames is finite, their reversible size ratios are fixed, and one may maximize the proved constants over that family. The source-specific composition audit is in `full-chain-positive-audit.md`. The moment theorem alone is not an independent proof of the certified sparse-linear-algebra primitive or one-hot structural theorem.

## 7. Concrete covered classes and exclusions

- Common total degree `d>=3`: choose `theta=1/d` on every active factor.
- Connected `k>=2` frames with every internal degree `h_i=d_ii>=2`, and arbitrary mixed cross totals `b_i=sum_(j!=i)d_ij`: connectedness gives `b_i>0`. With `epsilon=1/(4D)`, set every active cross weight to `epsilon` and `theta_ii=(1-epsilon b_i)/h_i`. These are symmetric, positive, strictly below one half, and have unit weighted rows. This includes every previously covered mixed-internal-degree class.
- The no-internal simple base `K_5` minus one edge: assign `1/3` to edges from its two degree-three vertices to its three degree-four vertices, and `1/6` to edges between degree-four vertices. Every row sum is one and all active weights are positive and below one half. Its independent lifts are included without conditioning.

Minimum degree three alone is insufficient. The `N`-lift of `K_(3,12)` has bipartite sides of sizes `3N,12N`, so its adjacency matrix has rank at most `6N` and nullity at least `9N` over every field. Its scalar zero-eigenvalue moment is therefore at least `p^(9N)`. It cannot satisfy `(P)`, because `(3)` would force equal side sizes.

Certificates with zero weights on active factors are not part of this theorem. Their more heterogeneous finite-field phase structure is not silently replaced by the all-omissions classification above. The result likewise makes no growing-frame/field, noisy-factor, or arbitrary deterministic-factor assertion.
