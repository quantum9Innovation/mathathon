# Polynomial Boolean recovery for the uniform simple RSBM(2,1)

Prepared 2026-11-15. This is an independent proof audit and algorithmic
consequence of the exact type formula in
`../../partitioning-rsbm-obstruction-session/finite-field-21-entropy.txt`.
The argument proves polynomial recovery; it does **not** prove real
one-dimensionality of the eigenvalue-1 eigenspace.

## Theorem

Let a graph on `2N` vertices be sampled by taking two independent uniform
simple 2-regular graphs on the two planted classes of size `N`, and a
uniform perfect matching between the classes. There is a deterministic
algorithm, with runtime `O(N^28 + N^3)` in a straightforward bit
implementation, that recovers the planted partition up to exchange of
its two classes with probability `1-O(N^-2)`.

The algorithm uses only the observed adjacency matrix and the promised
model parameters. It needs neither the matching nor the internal cycles.
The deliberately loose exponent makes the implication completely
explicit; no useful numerical runtime is asserted.

The proof has two ingredients:

1. The binary matrix `A+I` has a kernel with at most polynomially many
   elements with high probability. A crude global entropy bound suffices.
2. With probability `1-O(N^-2)`, the planted partition and its exchange
   are the only perfect matching cuts. The second ingredient was proved
   in `../../partitioning-rsbm-kernel-session/low-degree-identifiability.md`.

The first ingredient and the complete algorithm are proved below.

## 1. A binary affine system containing every perfect matching cut

Use bits `z_i` for class labels and signs `s_i=(-1)^(z_i)`. In a cubic
graph, let `r_i` be the number of neighbors with a label different from
that of vertex `i`. Then

```
((A+I)z)_i = r_i  (mod 2).
```

Consequently, every perfect matching cut satisfies

```
(A+I)z = 1  over F_2.                                  (1)
```

A solution of (1) has `r_i` equal to 1 or 3 at every vertex. It is a
perfect matching cut exactly when all these numbers equal 1. This last
condition is directly checked in linear time. Equivalently, check
`As=s` using the original integer adjacency matrix.

For completeness, (1) is consistent for every simple cubic graph. Put
`M=A+I` over `F_2`. It is symmetric with diagonal entries 1. For any
`u` in its kernel,

```
0 = u^T M u = sum_i u_i,
```

because the off-diagonal terms cancel in characteristic 2. Thus `1` is
orthogonal to `ker M`, and symmetry gives `1 in im M`. Consistency also
follows immediately from the planted labeling in our promised model.

If `k=dim_F2 ker(A+I)`, binary elimination therefore gives a particular
solution `z_0` and a basis `h_1,...,h_k`, and all solutions are

```
z_0 + t_1 h_1 + ... + t_k h_k,  t_j in F_2.            (2)
```

Unlike reduction of sign vectors modulo 2, the bit encoding in (1)
preserves the distinction between the two signs.

## 2. A polynomial first-moment bound

First use independent 2-regular configuration pairings in the planted
classes. Each vertex has two distinguished stubs; loops and parallel
edges are temporarily permitted. Relabel the cross matching to the
identity. Then, in this analytical labeling,

```
A+I = [[C_+ + I, I], [I, C_- + I]]  over F_2.
```

Writing a kernel vector as `(x,d)`, the equations are

```
C_+ x = x+d,    C_- d = x+d.                          (3)
```

Let the local values at index `i` be `(a,d,b,e) in F_2^4`, where `a=x_i`,
`d=d_i`, `b` is the `x`-value seen by the first plus stub, and `e` is the
`d`-value seen by the first minus stub. The values at the other two stubs
are forced to be

```
c=a+d-b,    f=a+d-e.
```

Let `n_{a,d,b,e}` be the numbers of these 16 local profiles. Define the
two stub tables, each of total mass `2N`, by

```
m^+_{uv} = sum n_{a,d,b,e} 1{a=u}(1{b=v}+1{c=v}),
m^-_{uv} = sum n_{a,d,b,e} 1{d=u}(1{e=v}+1{f=v}).
```

Admissible tables are symmetric and have even diagonal entries. For a
symmetric table `m` with even diagonal entries put

```
W(m) = m_{01}! (m_{00}-1)!! (m_{11}-1)!!,
```

with `(-1)!!=1`. Assigning the local profiles to vertices and then
pairing the prescribed stubs gives the exact identity

```
E |ker_F2(A+I)|
 = sum_n [N! / product n_{a,d,b,e}!]
         W(m^+) W(m^-) / ((2N-1)!!)^2,                (4)
```

where the sum is over nonnegative integral profiles of total `N` with
admissible tables. Stub order is retained, so this identity has no missing
orientation or factor-of-two correction.

Let `T=n/N`, let `Q^+=m^+/(2N)` and `Q^-=m^-/(2N)`, and write `H` for
entropy using natural logarithms. The key inequality, valid for every
admissible profile, is

```
H(T) - H(Q^+) - H(Q^-) <= 0.                         (5)
```

Here is a short proof including the symmetrization needed for (5).
Replace `T` by its average under the commuting involutions `b<->c` and
`e<->f`. This leaves both stub tables fixed and cannot decrease `H(T)`.
For the averaged law,

```
Q^+=law(a,b),    Q^-=law(d,e).
```

Entropy subadditivity for the two pairs `(a,b)` and `(d,e)` now gives
`H(T)<=H(a,b)+H(d,e)`, proving (5). No classification of equality cases,
local central limit theorem, or analysis near an entropy maximizer is
needed for a polynomial upper bound.

For clarity, elementary factorial bounds give an explicit prefactor.
For any integer `r>=0`, with `0 log 0=0`,

```
r log r-r <= log(r!)
           <= r log r-r + log(r+1)+1.                (6)
```

For an even `r`, use `(r-1)!!=r!/(2^(r/2)(r/2)!)` in (6). Applying
the upper bounds to the three factors of `W(m)`, and the lower bound to
`(2N-1)!!`, yields

```
W(m)/(2N-1)!!
 <= e^4 (2N+1)^4 exp[-N H(m/(2N))].                 (7)
```

The main logarithmic terms here are exactly
`N log(2N)-N-N H(m/(2N))` in the numerator and
`N log(2N)-N` in the denominator. Thus no exponential constant is
absorbed into the polynomial factor.

The multinomial coefficient in (4) is at most `exp[N H(T)]`. Equations
(5) and (7) show that each summand in (4) is at most
`e^8(2N+1)^8`. There are at most `(N+1)^16` profiles. Hence

```
E_config |ker_F2(A+I)|
 <= e^8 (2N+1)^8 (N+1)^16 = O(N^24).                (8)
```

Each simple labeled 2-regular graph corresponds to the same number of
configurations. The probability that both independent configuration
graphs are simple tends to `exp(-3/2)>0`. Conditioning (8) on this event
therefore proves, in precisely the requested uniform simple model,

```
E_simple 2^k <= C N^24                               (9)
```

for an absolute constant `C` and all sufficiently large `N`. The matching
gauge affects neither the binary rank nor the correctness of (1).

## 3. Bounded-runtime algorithm and success probability

The algorithm is as follows.

1. Compute a basis of `ker_F2(A+I)` and its dimension `k`, and solve (1).
2. If `2^k > N^27`, report failure and stop.
3. Otherwise enumerate all vectors in (2). For each, count the crossing
   neighbors at every vertex; retain a vector if every count is 1.
4. Output the retained partition up to global complementation. If
   multiple inequivalent partitions are retained, report failure.

Comparing `2^k` to `N^27` uses exact integers, so a numerical logarithm
is unnecessary. Binary elimination takes `O(N^3)` elementary bit
operations. A Gray-code enumeration updates and checks each candidate
in `O(N)` elementary operations. The cutoff gives deterministic runtime
`O(N^28+N^3)`.

By Markov's inequality and (9),

```
P(2^k>N^27) <= C N^-3.                              (10)
```

On the complement of this event, the true planted bit labeling and its
complement occur in the exhaustive list and pass verification. The
partition-rigidity theorem in the earlier note makes them the only
accepted partitions with probability `1-O(N^-2)`. A union bound with
(10) proves the theorem.

Every accepted sign vector is balanced: `As=s` and `A1=3 1` give
`3<1,s>=<1,As>=<1,s>`, hence `<1,s>=0`. Thus no separate balance
constraint or balance search is required.

## What this resolves and what it leaves open

This proves polynomial exact recovery in the hard `(2,1)` case under
the uniform simple 2-regular block law. It only requires an intentionally
weak polynomial moment bound. It therefore avoids the unresolved sharp
fixed-prime moment asymptotics needed to prove a one-dimensional real
eigenspace by taking a prime to infinity.

It does not prove `dim_R ker(A-I)=1` with high probability, and it makes
no transfer from the noncontiguous uniform-permutation 2-factor model.
