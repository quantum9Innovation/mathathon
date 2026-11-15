# Independent audit of the central lattice and local limit step

Prepared 2026-11-15. Written by the sparse-support worker. The initial
sections below independently derive the lattice and a form of the local
limit assertion needed in the uniform calculation. The final section
records review of `central-types.md` once that file is available.

## Full lattice of the directed stub totals

At one site take independent uniform `a,b,u,c in Fp`, and set
`v=a-b-u`, `d=b-a-c`. Its directed-stub increment is the pair of matrices

```
Z1=e_(a,u)+e_(a,v),    Z2=e_(b,c)+e_(b,d).
```

Each matrix has total two. For an integer pair `m1,m2` with respective
totals `2N`, write its row totals as `R_a,S_b`. The affine support lattice
has the following necessary conditions:

1. Every `R_a,S_b` is even.
2. Modulo `p`, with `n_a=R_a/2` and `h_b=S_b/2`,

```
sum_(a,z) z m1_az -sum_a a n_a +sum_b b h_b =0,
sum_(b,z) z m2_bz +sum_a a n_a -sum_b b h_b =0,
sum_(a,z) az m1_az -sum_(b,z) bz m2_bz
                 -sum_a a² n_a +sum_b b² h_b =0.          (L)
```

Here division by two in the definitions of `n,h` is integer division,
and modulo `p` it is also legitimate because `p` is odd.

These conditions are exhaustive. One direct proof classifies the
annihilating torus characters. Suppose coefficients `theta1(a,z)` and
`theta2(b,z)` make

```
theta1(a,u)+theta1(a,a-b-u)
 +theta2(b,c)+theta2(b,b-a-c)
```

constant in `a,b,u,c` modulo `2pi`. Varying `u` and then `b` shows that
each row of `theta1` is affine as a function on the cyclic group:

```
theta1(a,z)=alpha_a +(2pi/p) k_a z,
theta2(b,z)=delta_b +(2pi/p) l_b z,
```

with `k_a,l_b in Fp`. To see the first assertion without a smoothness
assumption, for a fixed row the equation `f(u)+f(s-u)=g(s)` holds for
every `s,u`; substituting `u=0` gives the additive Cauchy equation for
`f-f(0)`, whose homomorphisms from `Fp` into the circle are exactly the
displayed slopes.

Taking the mixed difference in `a,b` then gives

```
k_a=k0+k1 a,         l_b=l0-k1 b.
```

The remaining single-coordinate terms force

```
2alpha_a = const1 -(2pi/p)[(k0-l0)a+k1 a²],
2delta_b = const2 +(2pi/p)[(k0-l0)b+k1 b²],
```

modulo `2pi`. Conversely every such choice is an annihilator. Thus,
after removing the two continuous characters for the fixed total
counts, the annihilator has exactly

```
2^(2(p-1)) p³
```

elements: `p³` slope parameters and the row-parity choices, with one
redundant global parity per block. Since a closed integer lattice is
determined by its torus annihilator, this proves exhaustiveness of
the above support conditions and the index relative to the unrestricted
integer lattice with the two fixed totals.

This argument also proves that the real span has codimension exactly
two (the two total-count restrictions), so the covariance is positive
definite after removing those restrictions. No unmentioned real linear
relation is allowed by the increment distribution.

## Restriction to symmetric pairing tables

Set `m_j=m_j^T` and require its diagonals to be even, as in the exact
pairing formula. The first two congruences in (L) become the **same**
condition

```
sum_a a R_a +sum_b b S_b =0 mod p.
```

The third remains. These two congruences are independent on the
fixed-total symmetric edge-count lattice for every odd prime `p`.
For instance their coefficient functions on diagonal edges involve
the independent nonconstant functions `a` and `a²` on `Fp`; these remain
independent for `p=3`.

More explicitly, use integer undirected-edge coordinates
`k_aa=m_aa/2`, `k_ab=m_ab` for `a<b`, with `sum k=N` in each block.
The even-row requirements amount to even degrees in the mod-two graph
of off-diagonal edges, giving `p-1` independent parity restrictions per
block. Hence the arithmetic index here is

```
2^(2(p-1)) p².
```

Factors from changing between Euclidean directed, symmetric, and
undirected-edge coordinates are metric factors, separate from these
arithmetic indices. The ratio of the odd-primary parts before and
after symmetry is exactly `p³/p²=p`.

## Affine cosets, including p dividing N

The all-zero local choice has increments `Z1=Z2=2e_(0,0)`.
Consequently the affine lattice for `N` sites has fixed totals `2N`,
and all the displayed parity and field congruences remain homogeneous.
There is no extra condition that `p` or `p²` divide `N`.

The continuous mean `2N/p²` need not be an integer. A local limit theorem
is evaluated on the actual affine lattice, centered at this continuous
mean. For fixed `p`, every such affine lattice has a representative at
bounded distance from its continuous center after restricting to the
fixed-total space. Its displacement divided by `sqrt N` tends to zero.
Thus the limiting Gaussian Riemann sum is unchanged by `p|N`, by the
residue class of `N` modulo `p²`, or by parity of `N`.

One must keep the even diagonal restriction explicitly. It is part of
the symmetric pairing table lattice, not a consequence of symmetry
alone.

## Local limit theorem in a growing central window

For any fixed `p`, the increment distribution has finite support with
strictly positive probabilities, full real span in the fixed-total
space, and the maximal lattice just classified. These facts suffice
for a relative Gaussian local limit approximation uniformly at lattice
points `m` with

```
||m-N mu|| <= sqrt(N) log N.                            (W)
```

Here is the standard finite-dimensional Fourier justification in a
form that addresses positive factorial weights. First solve the
exponential-tilt equation for the mean `m/N` near `mu`; the inverse
function theorem applies because the covariance is positive definite.
The tilt parameter is `O_p(log N/sqrt N)`. Under this tilt, inversion
on a fundamental domain of the maximal lattice has a unique modulus-one
peak. The complement of a fixed neighborhood of that peak is uniformly
bounded away from one in modulus, including all these small tilts. Near
the peak, the characteristic function has its quadratic expansion
with uniformly bounded third derivatives. Gaussian scaling gives a
relative `1+o_p(1)` approximation at the tilted mean. Undoing the tilt
and Taylor-expanding its rate function yields

```
P(sum_i Z_i=m)
 = [covol(L)/(2pi N)^(d/2) sqrt(det Sigma)]
   * exp[-(m-Nmu)^T Sigma^(-1)(m-Nmu)/(2N)]
   * (1+o_p(1)),
```

uniformly in (W), where `d=2p²-2`. The rate-function remainder is
`O_p(log³N/sqrt N)=o(1)`, and the tilted covariance determinant differs
from its original value by `o_p(1)`.

Thus relative approximation, rather than only an additive uniform
`o(N^(-d/2))`, is available. This distinction matters because the exact
pairing factorials contribute positive Gaussian exponential weights.
Stirling expansion is likewise relative-uniform on (W), as all central
entries are `2N/p²+O_p(sqrt N log N)`.

The proof uses only fixed-dimensional, finite-support Fourier analysis;
it claims no estimate uniform in a prime growing with `N`.

## Completed review of central-types.md

I read all six sections of `central-types.md` after it was written.
Its convention replaces `y` by `-z`, so the two local sums become
`C1 x=x+z`, `C2 z=x+z`. This harmless gauge change turns the first two
congruences in (L) into negatives of each other on symmetric tables.

The covariance calculation checks directly. Conditional on the first
central label, the two neighbor labels are independent uniform. For a
mean-zero test table `f`, its variance is

```
(2/p²)||f||² +(2/p³) sum_a (sum_b f_ab)².
```

Each coordinate-pair statistic from one block is independent of each
coordinate-pair statistic from the other, by invertibility of the
respective four linear forms in the four uniform site labels. Thus
the cross-covariance is zero. The asserted covariance
`Sigma=(2/p²)(I+R)` and its determinant follow.

The exact Stirling prefactor also checks. There are
`d=p(p-1)/2` off-diagonal undirected cells. With
`t=2N/p²`, at the continuous uniform point the numerator is asymptotic
to

```
(2pi t)^(d/2) 2^(p/2) (t/e)^N,
```

whereas `(2N-1)!! ~sqrt(2)(2N/e)^N`. Hence its ratio is

```
p^(-2N) (4pi N/p²)^(d/2) 2^((p-1)/2),
```

with quadratic exponent `p²||X||²/8` for
`m=tJ+sqrt(N)X`. No missing orientation or loop factor appears.

On symmetric mean-zero tables the compression of the row projection
has eigenvalue `1/2` on the `p-1` dimensional additive row-plus-column
space and zero on the `d` dimensional row-zero space. Thus the final
weighted precision has eigenvalues `p²/8` and `p²/4` with precisely
these multiplicities. In particular there is no residual flat Gaussian
direction that would require a non-Gaussian local analysis.

One definitional defect in the first draft was identified independently
by both the parent and this reviewer: the symmetric summation lattice
must impose **even diagonals in addition to** membership in `L` and
symmetry. The draft's covolume already counted the correct extra
parities, so this defect did not alter its calculation. The definition
has been corrected. Its resulting Euclidean covolumes are

```
covol(L)=p^5 2^(2p-2),
covol(K)=p^4 2^(d+4p-4),
covol(L)/covol(K)=p 2^(-d-2p+2).
```

These agree with the independent arithmetic calculation above after
the metric factors from diagonal halving and symmetric off-diagonal
duplication are included.

Finally, using `s=d+p-1`, the Gaussian integral `I` in that draft obeys

```
I²/det(Sigma)=(2pi)^s 2^(p-1) p^(2d).
```

The full analytic factor before multiplying covolumes is therefore
`2^(d+2p-2)`. Multiplication by the displayed covolume ratio leaves
exactly `p`.

The growing-window local limit lemma in its Section 6 uses the required
relative tilted estimate, not an inadequate additive-error CLT.
Its fixed-neighborhood tail argument combines the analytic rate
function with the strictly positive weighted precision; outside
`sqrt(N)log N`, its Gaussian decay beats every polynomial number of
tables. These steps cover all tables in the chosen uniform neighborhood.

**Audit conclusion:** after the corrected definition of `K`, the
central contribution `p+o_p(1)` is justified. The argument covers every
odd prime, including `p=3`, and every sequence of `N`, including
`p|N`, odd `N`, and arbitrary residues modulo `p²`. Combined with the
sparse and entropy estimates, I find no remaining prefactor, parity,
coset, or local-limit gap in the fixed-prime moment argument.
