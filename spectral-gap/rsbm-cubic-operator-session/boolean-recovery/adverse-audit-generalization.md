# Adverse audit of the general fixed-degree recovery argument

Prepared 2026-11-15. Parameters are fixed integers `a=d1>=3`,
`b=d2>=1`, `a>b`, with `d=a+b` and `lambda=a-b`. The model has two
independent uniform simple internal `a`-regular graphs and an independent
uniform simple bipartite `b`-regular cross graph. All limits are along
admissible `N`, namely `aN` even and the elementary size constraints.

I find the proposed extension valid at the entropy and Boolean-rigidity
level. The argument does not require a central Gaussian integral or a
real simple-spectrum theorem. For Boolean rigidity, the integer local
equation and conditional expectations make a finite-field equality
classification unnecessary. Initial slot symmetrization must still be
included when deriving the entropy inequality.

## 1. Exact type mechanism

Use configuration models with `a` distinguished internal stubs and `b`
distinguished cross stubs at each vertex. A full left profile has central
label `X`, internal labels `A_1,...,A_a`, and cross labels
`B_1,...,B_b`, subject to

```
sum_i A_i + sum_j B_j = lambda X.
```

The right profile has center `Y`, internal labels `C_i`, and cross labels
`D_j`, with the analogous equation. On each side the last internal label
is uniquely determined by all the other entries. For the binary moment
these equations are in `F_2`; for Boolean rigidity they are equations
over the integers with every label restricted to `+1,-1`.

Let the profile laws be `qL,qR`. Define the averaged internal edge laws
`rhoL=law(X,A_J)` and `rhoR=law(Y,C_J)` using a uniformly chosen internal
slot. Both must be symmetric. The averaged cross law `rho=law(X,B_K)`
must be the reversal of `law(Y,D_K)`. These are precisely the stub
pairing/bijection constraints, supplemented by even internal diagonal
counts at the integer level.

For a fixed pair of integral profile tables, the vertex assignment factors
are the two multinomial coefficients. Internal pairing counts are

```
P(m)=prod_(u<v) m_uv! prod_u (m_uu-1)!!,
```

divided by `(aN-1)!!` in each block. The cross matching count is
`prod_(u,v) m_uv!/(bN)!`. Therefore the exact logarithmic exponent is

```
Phi = H(qL)+H(qR)
      -(a/2)(H(rhoL)+H(rhoR))-b H(rho).              (1)
```

This derivation counts loops and parallel edges correctly in the temporary
configuration model. Each simple internal graph has `(a!)^N` pairing
preimages, and each simple bipartite cross graph has `(b!)^(2N)` matching
preimages. Conditioning all factors simple therefore gives exactly the
required independent uniform simple laws. Their joint simplicity
probability stays bounded away from zero for fixed degrees along every
admissible size sequence, including odd `N` when `a` is even.

## 2. Entropy inequality, including the unsymmetrized domain

Average each profile law over permutations of its internal slots and
over permutations of its cross slots. This preserves its local linear
constraint, central marginal, and all three averaged edge laws. It cannot
decrease profile entropy. It is enough to bound the averaged laws; zero
exponent additionally forces the original laws to have already been
slot invariant by strict concavity.

For an invariant law, write `mu=law(X)`, `nu=law(Y)`, and use one internal
slot `A` or `C` and one cross slot `B` or `D`. Marginal consistency gives

```
law(A)=mu, law(C)=nu, law(B)=nu, law(D)=mu,
rhoL=law(X,A), rhoR=law(Y,C), rho=law(X,B)=law(D,Y).
```

Delete the last internal label, since it is determined. Conditional
entropy subadditivity gives

```
H(qL) <= H(mu)+(a-1)H(A|X)+b H(B|X),
H(qR) <= H(nu)+(a-1)H(C|Y)+b H(D|Y).
```

Substitution into (1), followed by writing each edge entropy as the
sum of its marginal entropies minus mutual information, yields exactly

```
Phi <= -(a/2-1)(I(X;A)+I(Y;C))-b I(X;B) <= 0.        (2)
```

All central marginal entropy coefficients cancel. This calculation
requires no assumption that the original integral table is symmetric in
its slots.

## 3. Integer Boolean equality and rigidity

For this part count only actual sign vectors, with every profile label
in `+1,-1` and the local equation holding as an integer equation. The
same exact enumeration and entropy inequality (2) apply: the constraint
still determines one internal label, and only finitely many profiles
are allowed.

Because `a>=3` and `b>=1`, all coefficients in (2) are positive. At
zero exponent, all three pair mutual informations vanish after slot
averaging. Internal edge symmetry and cross consistency then give

```
E[A_i|X]=E[X],    E[B_j|X]=E[Y].
```

Taking conditional expectation in the integer local equation yields

```
lambda X = a E[X]+b E[Y]  almost surely.             (3)
```

The right side is constant. Since `lambda=a-b>0`, `X` is deterministic.
The right block gives the same conclusion for `Y`. Write their
deterministic signs as `c,e`. The local equation becomes
`ac+be=(a-b)c`, or `b(c+e)=0` over the integers. Thus `e=-c`, giving
exactly the planted pair of sign phases.

This proof needs neither a Fourier argument nor equality in conditional
entropy subadditivity. Pair independence alone is enough. It also
handles original nonsymmetric profiles: symmetrization keeps the central
marginals fixed, so zero exponent forces these original central
marginals to be deterministic too; edge consistency then forces their
neighbor labels to be deterministic.

The finite Boolean feasible domain is compact. Its only exponent zeros
are these two phases, so there is a strictly negative exponent away
from small neighborhoods of them. Uniform Stirling bounds and the
polynomial type count make the expected number of candidates in that
macroscopic region exponentially small.

Near either planted phase, if a candidate sign vector is `tau`, the real
vector `tau-sigma` or `tau+sigma` is an eigenvector of eigenvalue
`lambda`, supported precisely on the changed coordinates. The existing
small-support proposition in
`../../partitioning-rsbm-kernel-session/deterministic-reductions.md`
rules out such a vector on at most `epsilon N` coordinates with
probability `1-O(N^(-(d-2)(lambda+1)))`. This proposition is independent
of block parity. Taking constant-phase neighborhoods small enough to
fall within that support bound leaves no uncovered overlap range.

Therefore the proposed argument proves Boolean partition rigidity for
every admissible size sequence, including even internal degree and odd
block size. It does not infer real eigenspace simplicity from rigidity.

## 4. Explicit polynomial binary moment and recovery cutoff

The exponent inequality (2) holds over `F_2`; no equality classification
is needed for a polynomial moment bound. Group full ordered-star
assignments by the two aggregate internal stub tables and the aggregate
cross table. A uniform law on each nonempty fiber is invariant under
vertex permutations and local slot permutations. Its common profile
marginals therefore have exactly those aggregate edge laws. Entropy
subadditivity for the whole fiber, followed by (2), bounds its cardinality
by the exponential of the pairing entropies, without a local-type count.

The aggregate tables have only twelve binary entries. Combining their
polynomial count with uniform factorial bounds gives

```
E 2^dim ker_F2(A-lambda I)
 <= e^12(aN+1)^16(bN+1)^8 = O_(a,b)(N^24).           (4)
```

The complete independent audit of this fiber step is in
`aggregate-fiber-moment-audit.md`. Conditioning simplicity preserves the
exponent 24, with a degree-dependent multiplicative constant.

Encode actual signs as `(-1)^z`. Their prescribed crossing degree `b`
implies the affine binary system

```
(A+dI)z=b 1  over F_2.
```

Its coefficient matrix equals `A-lambda I` over `F_2`, since
`d-lambda=2b`. The promised planted labeling ensures consistency. If
its nullity is `k`, stop before enumeration when `2^k>N^27`.
By (4), this stop event has probability `O_(a,b)(N^-3)`. Otherwise
enumerate the affine solutions, verify crossing degree exactly `b` using
integer counts, and identify global complementation. This takes
deterministic polynomial time for fixed `a,b`. Boolean rigidity proves
that the accepted partition is the planted one with high probability.

The binary affine system need not be consistent for an arbitrary
unpromised regular graph; the algorithm may report inconsistency in
that case. Its consistency in the planted model is sufficient.
