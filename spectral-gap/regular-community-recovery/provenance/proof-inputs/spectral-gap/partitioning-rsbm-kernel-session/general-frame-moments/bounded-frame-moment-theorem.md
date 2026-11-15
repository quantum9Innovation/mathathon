# Bounded intertwiner moments for every fixed regular configuration frame

Derived November 15, 2026. This note assembles the complete central and boundary estimates proved in this directory. The new input is not an inference from nonpositive entropy: the central estimate retains exact pairing weights, a relative lattice local limit theorem, and concentration under an exactly normalized reference law. Historical novelty is not asserted.

## Model and theorem

Fix finitely many old types `i=1,...,k`, positive integers `a_i`, and nonnegative integers `q_ij` satisfying

```
sum_j q_ij=d>=3 for every i,
a_i q_ij=a_j q_ji.
```

The undirected type support is connected; `q_ii>0` is a loop in this support. At scale `N`, type `i` has `n_i=a_i N` vertices, each with `q_ij` labeled physical stubs directed at type `j`. Independently for every present cross factor `i<j`, use a uniform bijection between its two stub sets. Independently for every present internal factor, use a uniform pairing of its stubs. An internal loop contributes two incidences to adjacency. Admissible scales satisfy `n_i q_ii` even. Multiple edges and loops are retained until any optional conditioning on simplicity.

Let `A_N` be the resulting adjacency matrix on `m_N=(sum_i a_i)N` physical vertices. Fix a prime `p`, an integer `r>=0`, and a matrix `R in Mat_r(F_p)`. Define

`Z_R(A_N)=#{Y in F_p^(m_N by r): A_N Y=Y R}`.

**Theorem.** There is a finite constant `C=C(Q,a,p,r)`, independent of the admissible scale `N` and of `R`, such that

`sup_(N admissible) E Z_R(A_N) <= C`.

The same bound, with a possibly larger constant, holds after conditioning every factor on simplicity, at sizes where those simple factors exist. This gives exactly independent uniform simple internal regular graphs and cross biregular graphs. No change-of-model contiguity is needed.

The theorem permits repeated physical slots aimed at the same old type, internal factors, unequal fixed type proportions, singular or nonsemisimple `R`, primes dividing any degree, and every admissible size residue. The constant is for fixed data; no growing-field, growing-frame, degree-two, or nonregular-total-degree statement is asserted.

## The induction class

The following slightly stronger homogeneous systems are proved at the same time.

- If the type support is nonbipartite, use one space `V=F_p^r` and an arbitrary type-dependent linear map `T_i:V->V` in the equation `sum_neighbors Y=T_i(Y_root)`.
- If the support is bipartite, use spaces `V_L,V_R`, allowing either to have dimension zero, and arbitrary maps `T_i:V_side(i)->V_opposite(i)`. The equation at type `i` is in the opposite-side space.

In the bipartite case, common total degree and reversibility imply equal total physical sizes on the two sides: `sum_L n_i=sum_R n_i`. Individual type sizes need not be equal. This equality is used in the exact central normalizer. The original intertwiner system is the case of a common alphabet and common map `x->xR`.

We prove boundedness by induction on `r` in the nonbipartite case, or on `dim V_L+dim V_R` in the bipartite class. Type-dependent maps are retained under restriction. At total dimension zero there is exactly one assignment.

## Exact type formula and entropy

A legal ordered star at old type `i` records its root and all `d` physical neighbor labels, satisfying its local linear equation. Let `t_i(omega)` be its empirical profile counts and let `m_ij(x,y)` be the pooled table of all its `q_ij` slots. Compatibility requires `m_ji=m_ij^T`; an internal pooled table is symmetric with even diagonal. The exact type contribution is

```
product_i n_i!/product_omega t_i(omega)!
 * product_(i<j) [product_(x,y) m_ij(x,y)!/(n_i q_ij)!]
 * product_i [product_x(m_ii(x,x)-1)!!
              product_(x<y)m_ii(x,y)!/(n_i q_ii-1)!!].
```

Absent factors are omitted. All vertices, stubs, loops, and parallel edges are counted explicitly. Root-label assignments appear in the star multinomials and are not multiplied in a second time.

Put `P_i=t_i/n_i` and `nu_ij=m_ij/(n_i q_ij)`. Uniform Stirling bounds, including zero entries, give the logarithm of a contribution as `N Phi+O(log(N+1))`, with

```
Phi=sum_i a_i H(P_i)
    -sum_(i<j) a_i q_ij H(nu_ij)
    -sum_i (a_i q_ii/2)H(nu_ii).
```

The number of types and the prefactor are polynomial in `N` at fixed data.

Symmetrize the physical slots aimed at each same old type. This preserves the pooled tables and local equation, and increases star entropy. Equality in this symmetrization requires that the original law already be symmetric. For symmetric stars, average the conditional entropy inequality over every omitted physical slot. The omitted neighbor is determined with coefficient one in every characteristic. Reversibility and common total degree cancel the root entropy terms, yielding

```
Phi=-(d-2)/d [sum_(i<j)a_i q_ij I_ij
                         +sum_i(a_i q_ii/2)I_ii]
     -(1/d)sum_i a_i sum_(physical slots s) J_i,s <=0.
```

Here `I_ij` is root-neighbor mutual information and `J_i,s` is the conditional total correlation of all retained neighbor slots given the root. Section 2 of [boundary-frame.md](boundary-frame.md) proves this identity and its exact equality conditions, including the symmetrization step.

## Every entropy-zero phase

At zero entropy, every present edge pair is a product and every retained `d-1` neighbor tuple is a root-independent product. The elementary finite-group lemma in [boundary-frame.md](boundary-frame.md) then forces each root law to be uniform on an affine coset. At every old type all its physical neighbors have the same support-difference subspace.

Consequently these subspaces are constant on even-walk components of the old support. In the connected nonbipartite case they are one common `H<=V`, with

```
T_i(H) subseteq H,
T_i(a_i^*)-sum_j q_ij a_j^* in H,
root law Uniform(a_i^*+H).
```

The notation `a_i^*` denotes coset representatives, not the fixed size multipliers. In the connected bipartite case they are `H_L,H_R`, with

```
T_i(H_side(i)) subseteq H_opposite(i),
T_i(a_i^*)-sum_j q_ij a_j^* in H_opposite(i).
```

An internal factor is a self-incidence and hence makes the old support nonbipartite. Repeated physical slots do not create extra even-walk components. For given cosets the legal star laws are uniquely uniform on their legal affine supports. There are finitely many phases. A phase is proper unless its one subspace, or both side subspaces, equal the ambient alphabets. Every proper restriction strictly lowers the induction dimension.

## Full-uniform contribution, with the actual prefactor

[central-frame.md](central-frame.md) supplies the separate central theorem for the above induction class, even allowing affine maps. It records a table for **each physical slot**, while the exact matching weight `W` depends on their pooled tables.

Let `P` independently sample a uniform legal star at each vertex, and `Q` independently sample the root and every neighbor label uniformly without the sum constraint. If `K_N` is the product of the numbers of legal stars, exact counting gives

`E Z=K_N E_P W`, while `K_N E_Q W=1`.

In the bipartite two-space class the latter identity uses the already-established equality of total side sizes. The normalized weighted reference law `nu_N=K_N W Q` is exactly the law obtained by sampling the configuration and then iid uniform root labels.

Full physical-slot table means and covariance agree under `P,Q`; degree `d>=3` makes every two neighbor labels independent uniform conditional on the root. The common covariance is positive on precisely the space of slot tables with common root-row margins. Its maximal legal lattice has finite index

`I=product_i |U_i|^{|V_i|}`

inside the unrestricted full-table lattice, where `U_i` is the neighbor alphabet. An explicit character argument proves completeness of these lattice periods.

Uniform exponential tilting and Fourier inversion on compact tilt neighborhoods give, on the legal affine lattice,

`P(M=m)/Q(M=m) <= C I exp(C ||m-mu_N||^3/N^2)`

throughout a fixed small `epsilon N` neighborhood, and the sharper ratio `I(1+o(1))` in the `sqrt(N)log N` window. The local estimate is relative and positive at every relevant affine lattice point, rather than an absolute-error estimate.

Under the exact weighted law `nu_N`, internal pairings and cross bijections are represented by independent uniform stub permutations. A transposition changes at most four physical incidences; changing one vertex label affects at most `2d`. The exposure martingale therefore gives

`nu_N(||M-mu_N||>=t)<=C exp(-c t^2/N)`

for `t>=C0 sqrt(N)`, with only `O(1)` bias from internal loops. For sufficiently small fixed `epsilon`, the cubic likelihood ratio is bounded by `C exp(eta ||M-mu_N||^2/N)` with `eta<c`. Integrating the subgaussian tail removes the annulus outside `sqrt(N)log N` with no polynomial loss. The exact normalizer bounds the inner window by `I+o(1)`.

Thus the expected full-uniform-neighborhood contribution has finite limsup at most `I`. No pooled Gaussian determinant or entropy-only assertion substitutes for this calculation.

## Proper phases: sparse quotient support and correlation-safe rank forcing

For a proper phase, quotient by its subspaces and subtract its type-constant quotient point map. The quotient defect solves the homogeneous induced system. Let `s` count its nonzero physical vertices. Every exterior zero vertex touched by its support receives at least two support incidences, counted with multiplicity. The certificate of all edges incident to the support therefore obeys

`E-V >=(d-2)s/2`, with `E<=ds`.

For a fixed quotient assignment, its lifts form an affine fiber, empty or of size exactly `Z_H(G)`, the homogeneous restricted kernel count. This remains true when the coset representatives are not exact solutions in the ambient spaces.

The conditional certificate law is controlled explicitly. A cross-stub pair is forced by one image swap; an internal stub pair is forced by replacing `{u,x},{v,y}` by `{u,v},{x,y}`, unless already present. A permissible internal output has exactly `m-1` preimages when `m` free stubs remain; the cross output has exactly `m`. Thus the coupled output is exactly uniform conditional on the prescribed pairs, preserves earlier prescriptions, and uses at most `E` switches. At most `4E` physical rows change, so

`E[Z_H(G)|certificate] <=p^(4r_* E) E Z_H(G)`,

with a fixed ambient dimension bound `r_*`. This is the needed correlation control, not an independence assumption.

The weighted certificate count in [boundary-frame.md](boundary-frame.md) gives, for `1<=s<=epsilon N`,

`E #{solutions with s quotient defects}
 <= M_H(N) ds L^s (s/N)^((d-2)s/2)`.

Configuration supports of size one are retained. Summing the geometric tail from `s=1` proves

```
E #{solutions in the phase cosets} <= M_H(N),
E #{solutions with 1,...,epsilon N defects}
 <= O(N^{-(d-2)/2}) M_H(N).
```

By induction `M_H(N)` is bounded for every proper phase, because its common subspace or side-subspace pair has lower total dimension. There are finitely many phases.

## Completing the induction

Choose the central physical-table neighborhood and proper root-coset neighborhoods just described. They cover every zero of the continuous entropy exponent. The complementary feasible type region is compact and has a strictly negative maximum. Its exact type sum is therefore `poly(N) exp(-cN)`.

The total moment is at most the bounded central contribution, the finitely many bounded proper-phase contributions, and that vanishing complement. This proves a finite limsup in the given induction dimension. There are finitely many on-site maps over the fixed finite spaces, so their bounds can be maximized uniformly. Finally the finitely many admissible sizes below an eventual threshold have finite moments. This proves the stated supremum theorem.

For simplicity conditioning, every independent factor has a positive limiting probability of being simple at fixed degrees. Internal pairing loop and parallel-edge counts have the usual bounded Poisson limits; cross factors have only bounded parallel-edge defects. Conditioning all finitely many factors therefore costs a bounded factor independent of `N`. Their simple projections are exactly uniform because each simple graph has the same number of labeled-stub realizations. The conditional theorem follows directly.

## Charged algorithm composition

The moment theorem controls all fixed powers, not only one exponential kernel moment. If `h_R=dim ker(Y->AY-YR)`, then for each fixed integer `s>=1`,

`Z_R(A)^s=Z_diag(R,...,R)(A)`.

Apply the theorem to the fixed block-diagonal target of dimension `sr` to obtain `sup_N E p^(s h_R)<infinity`. For a fixed finite family of candidate targets, a joint block-diagonal target similarly controls any fixed product of their exponential kernel counts.

Consequently a separately established certified kernel/enumeration primitive with conditional charged work bounded by

`C N^2 (log(N+2))^c p^(s h_R)`

has expected work `O(N^2 (log(N+2))^c)` here. The same holds after the direct simplicity conditioning and for a fixed finite candidate family. The primitive must expose/project the correct right kernel and account for its certification/retry costs; the moment estimate alone does not supply sparse linear algebra, output verification, or identifiability of an unknown frame. Dense Gaussian elimination alone would instead give only a cubic work bound. The source-specific algorithm audit is recorded separately in `full-chain-audit.md`.
