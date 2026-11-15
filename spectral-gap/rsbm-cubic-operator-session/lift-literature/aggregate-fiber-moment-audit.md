# Audit of the aggregate-table fiber entropy bound

Checked 2026-11-15. The proposed aggregation removes the exponential-in-
degree number of profile types from the **power of N** in the coarse
moment bound. I found no hidden exponential prefactor or invalid
exchangeability assumption. The argument below gives the claimed
`O_{a,b}(N^24)` binary moment for every fixed `a>b>=1`.

## 1. Define a fiber of actual ordered arrays

Fix three aggregate tables `(m^+,m^-,h)`. Let Omega be the finite set of
ordered star-profile arrays on the N labeled vertices in each planted
block such that:

* Each profile satisfies its local field equation
  `sum internal labels + sum cross labels = (a-b) root`.
* The two internal aggregate tables are `m^+,m^-`.
* The plus-oriented cross table and transposed minus-oriented cross table
  both equal h.

The slots at every vertex are distinguished. These are full profile
arrays, not a list of profile types or a list of graphs. Empty fibers
contribute zero and may be omitted.

Distinguished-stub enumeration gives exactly

```
E |ker_Fp(A-(a-b)I)|
 = sum_(m+,m-,h) |Omega|
       W(m+) W(m-)/((aN-1)!!)^2
       product_(u,v) h_uv!/(bN)!.
```

For one fixed profile array, every compatible internal pairing is
counted by W and every compatible cross-stub bijection by the displayed
factorials. Conversely, a graph configuration and a kernel vector
determine one ordered profile array. Thus this grouping is precisely a
partition of the original exact first-moment count.

## 2. Fiber invariance is enough

Give Omega its uniform probability law. Its full-array entropy is
exactly `log|Omega|`.

The fiber is invariant under every permutation of labeled vertices
within either block. More importantly, it is invariant under a
permutation of the a internal slots and of the b cross slots at each
individual vertex, independently for each vertex. These actions preserve
all three aggregate tables and preserve the local equation because they
preserve each neighbor sum.

Let `T_+,T_-` be the one-vertex profile laws in the two blocks. Vertex
invariance makes the laws identical within a block, and slot invariance
makes each law separately exchangeable in its internal and cross slots.
Entropy subadditivity, without assuming independence, gives

```
log|Omega| <= N[H(T_+)+H(T_-)].                         (1)
```

Even vertex exchangeability could be dispensed with: subadditivity
followed by concavity bounds the sum of individual entropies by N times
the entropy of the averaged vertex law. The actual uniform-fiber
invariance supplies both properties directly.

Because the aggregate tables are fixed **pointwise** on Omega, the
averaged slot marginals are exactly

```
F_+=m^+/(aN),  F_-=m^-/(aN),  G=h/(bN).
```

For instance the average of `1{X=u,A_i=v}` over i and vertices equals
`m^+_uv/(aN)` deterministically; exchangeability identifies each slot
law with that average. Internal symmetry and cross-table consistency
therefore imply all the root/neighbor marginal identities used in the
coarse entropy argument.

The laws T here are generally mixtures of many empirical profile types.
That is harmless: the entropy inequality applies to arbitrary
probability laws supported on valid profiles with the specified edge
marginals. It does not require one empirical type or integral profile
frequencies.

## 3. The existing entropy inequality applies exactly

For `a>=2`, one internal neighbor is determined by the root and all the
other neighbors. Conditional subadditivity, the slot symmetries, and the
fixed edge marginal identities yield

```
H(T_+)+H(T_-)
 - a/2[H(F_+)+H(F_-)] - bH(G)
 <= -(a/2-1)[I(X;A)+I(Y;C)] - b I(X;B)
 <= 0.
```

This is valid over `F_2` too. Combining with (1) proves the exact bound

```
|Omega| <= exp{N[a/2(H(F_+)+H(F_-))+bH(G)]}.           (2)
```

There is no error term, no profile-type count, and no missing
multinomial coefficient in (2). Its entropy is the entropy of the full
uniform fiber, which already includes all assignments and all type
multiplicities.

## 4. Prefactors and exponents

Use the already proved zero-safe factorial estimates, with
`q=p(p+1)/2`:

```
W(m)/(aN-1)!!
 <= exp(q+1)(aN+1)^(q+1) exp[-(aN/2)H(F)],

product h_uv!/(bN)!
 <= exp(p^2)(bN+1)^(p^2) exp[-bN H(G)].
```

Multiplying these estimates for the two internal tables and the cross
table with (2) cancels the entropy factors exactly. One aggregate triple
therefore contributes at most

```
exp[p(p+1)+2+p^2]
 (aN+1)^[p(p+1)+2] (bN+1)^(p^2).
```

The number of aggregate triples is at most

```
(aN+1)^(2p^2) (bN+1)^(p^2).
```

This very loose count treats every table entry as independently taking
any value from zero to its total. It includes invalid triples and hence
is certainly an upper bound. Summing yields

```
E |ker_Fp(A-(a-b)I)|
 <= exp[p(p+1)+2+p^2]
    (aN+1)^[p(p+1)+2+2p^2] (bN+1)^(2p^2).             (3)
```

At p=2, this is exactly

```
E 2^nullity_F2 <= exp(12)(aN+1)^16(bN+1)^8
               = O_(a,b)(N^24).                       (4)
```

The configuration-to-uniform-simple conditioning costs only a fixed
positive reciprocal simplicity probability for each fixed a,b. It
changes the multiplicative constant, not the power 24. No matching-sum
contiguity or parity of block size beyond aN even is used.

## 5. Scope of the improvement

The moment's power 24 is independent of the fixed degrees. Consequently
the existing binary affine algorithm may use one universal cutoff
`2^k<=n^27`, with abort probability `O_(a,b)(N^-3)` and fixed-degree
worst-case running time `O_(a,b)(n^28)`. The uncapped listing algorithm
has expected running time `O_(a,b)(n^25)`.

This does not by itself give a uniform theorem for degrees growing with
N: the simplicity-conditioning cost then need not be bounded. It also
does not improve the separate Boolean rigidity input or prove real
eigenvalue simplicity. It improves the general coarse moment and the
degree dependence of the recovery exponent exactly as proposed.
