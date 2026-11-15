# Macroscopic Boolean rigidity: exact type count and an explicit entropy gap

This is an independent audit of the proposed star-profile argument. The
type exponent, its entropy decomposition, and the resulting strict gap
are correct. There is no missing root-label entropy. The argument applies
to every admissible `N`, including odd `N` when the internal degree is
even; it does not use a random-lift representation.

Fix integers `a>b>0`, `a>=3`, and put `D=a+b`, `delta=a-b`. Each planted
block has `N` vertices. The internal configuration models have degree
`a`, so `aN` is even, and the cross-block configuration is a uniform
bijection between the `bN` cross-stubs on each side.

We count sign vectors `z` satisfying `Az=delta z`. This is a Boolean
statement; it does not assert simplicity of the real eigenspace.

## Star profiles and compatibility

A plus-block star profile is an ordered tuple

`(X;Y_1,...,Y_a;Z_1,...,Z_b)`

with all entries in `{+1,-1}`. Here `X` is the root sign, the `Y` entries
are signs at internal-stub neighbors, and the `Z` entries are signs at
cross-stub neighbors. Its allowed support obeys

`sum_i Y_i + sum_j Z_j = delta X`.

There is an analogous minus-block profile. Let their empirical laws be
`pi_+,pi_-`, and let their root marginals be `mu_+,mu_-`.

Let `Q_++` be the average of the `a` joint laws `Law(X,Y_i)` in the plus
block, and define `Q_--` analogously. Let `Q_c` be the average of the `b`
joint laws `Law(X,Z_j)` in the plus block. An actual pairing requires

* `Q_++` and `Q_--` symmetric, with both marginals respectively `mu_+`
  and `mu_-`;
* the corresponding minus-block cross law to equal the transpose of
  `Q_c`, whose marginals are `mu_+,mu_-`.

All these are linear constraints. Integrality and parity constraints on
the counts are imposed when taking the exact combinatorial count.

Writing `m_+,m_-` for the root means, averaging the plus local constraint
already gives

`a m_+ + b m_- = (a-b)m_+`, hence `m_-=-m_+`.

Thus every feasible profile pair has the balance expected from the
eigenvector equation. If `alpha=mu_+(-1)`, then
`mu_-(+1)=alpha`; this is the fraction flipped in each planted block.

## Exact profile count: the root entropy is already present

For each allowed star `s`, write `n_s^+=N pi_+(s)` and
`n_s^-=N pi_-(s)`. Assigning these profiles to the labeled vertices can
be done in

`[N!/prod_s n_s^+!] [N!/prod_s n_s^-!]`

ways. This count assigns the root signs as well as the neighbor-stub
signs. Therefore its exponent is `N[H(pi_+)+H(pi_-)]`, with no further
root entropy to add or subtract.

For one internal block, set `m_st=aN Q(s,t)`, for `s,t` in `{+1,-1}`.
Compatibility requires `m_+-=m_-+` and both `m_++`, `m_--` even. The exact
number of compatible internal pairings is

`(m_{++}-1)!! (m_{--}-1)!! m_{+-}!`.

Divide this by `(aN-1)!!`. The same factor is used for the other block.

For the cross configuration set `ell_st=bN Q_c(s,t)`. If the opposite
block has the transposed counts, the exact number of compatible cross
bijections is `prod_{s,t} ell_st!`; divide by `(bN)!`.

Multiplying these five exact factors gives the expected number of sign
vectors and their prescribed neighbor-sign profiles of this type. No
independence assumption concerning neighboring signs is used.

Uniform Stirling estimates give the exponent `N Phi`, where

`Phi=H(pi_+)+H(pi_-)-(a/2)[H(Q_++)+H(Q_--)]-b H(Q_c)`.

The statement is valid when some counts vanish, using `0 log 0=0` and
`(-1)!!=1`.

One explicit uniform prefactor is also available. Put
`M=2^(D+1)`, an upper bound on the number of star profiles. The multinomial
coefficients are at most their entropy exponentials. For an individual
compatible type the pairing factors are at most

`e^13 (aN+1)^8 (bN+1)^5`

times their entropy exponentials. To obtain this bound, use
`0<=log(n!)-n log n+n<=log(n+1)+1`; the corresponding double-factorial
error has absolute value at most the same bound. Each internal pairing
ratio has four such errors and the cross ratio has five.

There are at most `(N+1)^(2M)` profile pairs. Consequently an entropy
upper bound `Phi<=-c` on a family of types gives the expected-count bound

`e^13 (aN+1)^8 (bN+1)^5 (N+1)^(2M) exp(-cN)`.

## Symmetrization and the exact entropy-defect identity

Average each profile law over all permutations of its internal slots and
over all permutations of its cross slots. This preserves the allowed
support, root marginals, and averaged edge laws. It increases profile
entropy by concavity. Thus it increases `Phi`, and an upper bound for
symmetrized laws is an upper bound for the original type.

For symmetrized profiles define

```
I_+ = 2H(mu_+) - H(Q_++),
I_- = 2H(mu_-) - H(Q_--),
I_c = H(mu_+) + H(mu_-) - H(Q_c).
```

These are the three nonnegative root-neighbor mutual informations.

Drop one internal neighbor, say `Y_a`. The local equation reconstructs
it exactly as

`Y_a=delta X-sum_{i<a}Y_i-sum_j Z_j`.

Consequently the entropy of the full star equals the entropy of the root
and retained neighbors. Let `T_+` be the conditional total correlation of
the retained neighbors given the plus root:

```
T_+ = sum_{i<a} H(Y_i|X) + sum_j H(Z_j|X)
      - H(Y_1,...,Y_(a-1),Z_1,...,Z_b|X) >= 0.
```

Define `T_-` analogously. Direct substitution into the type exponent
gives the **identity**

`Phi=-(a/2-1)(I_++I_-)-b I_c-T_+-T_-`.

Thus `Phi<=0`. For `a>=3,b>0`, equality forces all three mutual
informations and both conditional total correlations to vanish.

For example, conditional on the plus root, the retained neighbors then
become independent, with `a-1` laws `mu_+` and `b` laws `mu_-`. The
eliminated internal neighbor also has conditional law `mu_+`. Taking
conditional variances yields

`v_+=(a-1)v_+ + b v_-`,

where `v_+,v_-` are the two root variances. Thus
`(a-2)v_+ + b v_-=0`, forcing both root laws to be deterministic. The
local equation then forces their signs to be opposite, giving exactly
the planted vector or its negative.

## Explicit strict gap, avoiding a compactness-only constant

There is a quantitative version of the equality argument. Write
`L=-Phi` for a symmetrized profile pair. Let `P` be the joint law of the
plus root and its retained neighbors, and let

`R=mu_+ tensor mu_+^(tensor(a-1)) tensor mu_-^(tensor b)`.

The relative entropy is exactly

`KL(P||R)=T_+ +(a-1)I_+ + b I_c <= 4L`,

since `(a-1)/(a/2-1)<=4` for `a>=3`. Pinsker's inequality, with total
variation equal to half the L1 distance, gives

`TV(P,R)<=sqrt(2L)`.

On the retained-coordinate space define

`W=delta X-sum_{i<a}Y_i-sum_j Z_j`.

Under `P`, the local eigenvector constraint gives `W^2=1` exactly.
Under `R`, all retained coordinates, including the root, are independent.
Their means satisfy `m_-=-m_+=-m`, and their common variance is

`v=1-m^2=4alpha(1-alpha)`.

It follows that

```
E_R W = m,
Var_R W = (delta^2+D-1)v,
E_R W^2-1 = (delta^2+D-2)v.
```

The deterministic bound `|W|<=delta+(a-1)+b=2a-1` implies

`(delta^2+D-2)v <= (2a-1)^2 TV(P,R)`.

Therefore every symmetrized feasible profile satisfies

`-Phi >= 8(delta^2+D-2)^2 alpha^2(1-alpha)^2/(2a-1)^4`.

Symmetrization only increases `Phi`, so the same upper bound for `Phi`
holds for every original compatible type.

For any fixed `0<epsilon<=1/2`, define the explicit positive constant

`c_epsilon=8(delta^2+D-2)^2 epsilon^2(1-epsilon)^2/(2a-1)^4`.

For `epsilon<=alpha<=1/2`, the expected number of alternative sign
vectors in the configuration model is at most

`e^13 (aN+1)^8 (bN+1)^5 (N+1)^(2^(D+2)) exp(-c_epsilon N)`.

Markov's inequality gives the same bound for the probability that any
such vector exists. This is exponentially small for fixed degrees and
fixed `epsilon`, with an effective prefactor and exponent. Global sign
exchange permits the usual choice `alpha<=1/2`.

## Conditioning on simple graphs and parity

Conditioning all three configurations on simplicity gives precisely the
model with independent uniform simple `a`-regular internal graphs and a
uniform simple `b`-regular bipartite cross graph. Every fixed simple graph
has the same number of stub representations.

For fixed degrees the simplicity probability has a positive limit. For
one internal block it is `exp(-(a^2-1)/4)`; for the cross configuration it
is `exp(-(b-1)^2/2)`. Thus the joint limit is

`exp(-(a^2-1)/2-(b-1)^2/2)>0`.

These constants can be obtained directly from fixed factorial moments:
internal loops and double edges converge to independent Poisson laws
with means `(a-1)/2` and `(a-1)^2/4`; cross double edges have mean
`(b-1)^2/2`. Overlapping fixed patterns and triple edges contribute
`O(1/N)`, while disjoint patterns give the displayed Poisson factorial
moments. No parity condition beyond `aN` even enters this computation.

Dividing the configuration probability bound by the joint simplicity
probability therefore preserves the exponential bound, uniformly along
every admissible sequence of `N`. In particular this covers odd block
sizes when `a` is even.

## Audit limitations

The argument proves exclusion of macroscopic alternative **sign**
eigenvectors. It does not exclude another real eigenvector in the planted
eigenspace. An independent near-planted support estimate is needed to
turn this macro estimate into Boolean rigidity over all overlaps.

The coefficient `a/2-1` vanishes at `a=2`. Consequently this audit does
not extend the mutual-information equality argument to `(a,b)=(2,1)`;
that case is covered by the separate exact low-degree count.
