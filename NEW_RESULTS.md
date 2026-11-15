# New results and their significance

Snapshot based on research records dated November 14–15, 2026. This memo
covers the four candidates discussed in the side conversation. It records
their claims and evidence; it does not independently reprove them.

**Assessment: credible candidates for specialist research papers, with two
potentially substantial mathematical results. An established seminal
breakthrough, a general quadratic-time algorithm, and global
state-of-the-art superiority have not been demonstrated.**

## How big are they?

| Result | Significance if correct and new | Present assessment |
|---|---|---|
| Faust–Fawzi conjectured approximation bounds | Resolves two focused published open questions with positive constructions and the full conjectured rates. | The cleanest externally identifiable research claim; potentially a breakthrough within that particular approximation problem. |
| Uniform fractional-matrix constants and transitions | Gives sharp universal constants, matching extremizers/compression ranks, exceptional analytic families, and dimension/coefficient transition laws. | Possibly the strongest original mathematical contribution; credible substantial specialist work. |
| Sharp-rank matrix-function update algorithms | Realizes intrinsic-error corrections with conventional arithmetic and asymptotically optimal leading output ranks. | A useful algorithmic theorem, with substantial risk that the runtime bound is already implicit in known methods. |
| Small-block quantum-entropy certificates | Turns the approximation theorem into explicit lower/upper SDPs, including a certified finite 25-pole example. | A concrete application and construction. The small-block principle itself has prior antecedents. |

These are related results, rather than four independent breakthroughs.
The constants and algorithms share resolvent/quadrature machinery; the
quantum application depends on the rational-approximation theorem.

## 1. Faust–Fawzi approximation conjectures

For

$$
f_a(x)=\frac{x^a-a(x-1)-1}{a(a-1)},\qquad
f_1(x)=x\log x-x+1,
$$

the manuscript constructs positive rational sums with $m$ poles and proves,
for fixed $1\le a<b\le2$,

$$
\sup_{x>0}\frac{|f_a(x)-\widehat f_m(x)|}{f_b(x)}
\le C_{a,b}\exp\!\left[-2\pi\sqrt{\frac{a(b-a)}{b}\,m}\right].
$$

The multiplicative constant is independent of $m$. The negative-parameter
range follows by an involution. A second theorem gives positive Stieltjes
lower approximants $R_m$ of type $[m-1/m]$ with

$$
\sup_{0<x\le1}x^d\bigl(x^{-c}-R_m(x)\bigr)
\le C_{c,d}e^{-2\pi\sqrt{(d-c)m}},
\qquad 0<c<d\le1.
$$

These are the bounds requested in Conjectures 1 and 2 of
[Faust–Fawzi (2023)](https://arxiv.org/abs/2305.12405). In the entropy case
$a=1,b=2$, the rate is $Ce^{-\pi\sqrt{2m}}$, compared with their proved
$Cm^{3/2}e^{-\pi\sqrt m}$. This improves the leading pole budget for a
small target error by a factor approaching two relative to that bound.

**Why it matters:** this addresses precise stated conjectures and preserves
positive weights, which support convex semidefinite representations.
Those are focused approximation-theory questions, not evidence by
themselves of a field-wide foundational breakthrough. A conjecture's name
does not establish its importance.

**Limits:** the result supplies the conjectured upper bounds, not matching
lower bounds or exact asymptotic multiplicative prefactors. Coefficient
preparation charges polynomial root extraction separately. Numerical
stability and bit complexity are not established. A bounded literature
search found no later resolution; that does not certify priority.

- [Integrated paper](matmul/positive-rational-approximation.pdf)
- [Source](matmul/positive-rational-approximation.tex)
- [Scalar proof audit](matmul/faust-fawzi-independent-audit.txt)
- [Integrated quantum/source audit](matmul/quantum-small-block-independent-audit.txt)

## 2. Exact fractional-matrix constants: the 1:2:4 law

For fixed $0<\alpha<1$, define the optimal Schatten **power** constant

$$
H_s(f)=\sup_{A\ne B}
\frac{\operatorname{tr}|f(B)-f(A)|^s}
{\operatorname{tr}|B-A|^{\alpha s}},
$$

with finite Hermitian inputs and the appropriate positive-input restriction
for the PSD power case. The reported exact limits are:

| Input/function class | Limit of $s^2H_s$ |
|---|---|
| PSD inputs, $f(x)=x^\alpha$ | $1/[2\pi^2\alpha(1-\alpha)]$ |
| One analytic branch, $f(x)=(\mp ix)^\alpha$ | $1/[\pi^2\alpha(1-\alpha)]$ |
| Nonzero real homogeneous fractional function on the full line | $2/[\pi^2\alpha(1-\alpha)]$ |

The stronger theorem covers every complex homogeneous function
$f(x)=a x_+^\alpha+b(-x)_+^\alpha$. Write

$$
f=\kappa g_++\lambda g_-,
\qquad g_\pm(x)=(\mp ix)^\alpha.
$$

Uniformly over all nonzero coefficient pairs,

$$
\frac{s^2H_s(f)}{|\kappa|^s+|\lambda|^s}
\longrightarrow \frac{1}{\pi^2\alpha(1-\alpha)}.
$$

For fixed coefficients, one active analytic branch gives the intermediate
constant and two give the full constant. The exceptional families are
$b=a e^{\pm i\pi\alpha}$. The uniform theorem also handles coefficients
approaching those families arbitrarily quickly.

There are matching worst-case approximation-rank constants at intrinsic
operator error $\varepsilon\|B-A\|^\alpha$. For each fixed perturbation
rank $r$, the leading coefficient of $\log^2(1/\varepsilon)$ is half
the corresponding moment coefficient, multiplied by $r$.

The dimension dependence is also explicit. If $c$ is the rank-one count
coefficient and $ns^2\to t$, then for a fixed nonzero function,

$$
s^2H_{s,n}\longrightarrow
2c\left[1-\left(1+\sqrt{t/c}\right)e^{-\sqrt{t/c}}\right].
$$

The joint vanishing-branch law replaces the capped quadratic profile by
$b_\alpha[x^2+(x-u)_+^2]$, where
$b_\alpha=1/[2\pi^2\alpha(1-\alpha)]$ and
$u=-s\log|\theta_s|$ for $g_++\theta_sg_-$. Its limit is

$$
\int_0^\infty e^{-x}
\min\{t,b_\alpha[x^2+(x-u)_+^2]\}\,dx.
$$

**Why it matters:** the substantive content is the uniform classification,
matching lower constructions, and transition laws. It goes beyond
improving one numerical constant.

**Important interpretation:** the factor four concerns power constants.
The ordinary quasi-norm constant is $H_s^{1/s}$; its ratio is not simply
four. Nor does this theorem imply a fourfold hardware speedup or a new
matrix-multiplication exponent. These are small-$s$ asymptotics, not exact
best constants for every fixed exponent.

**Priority limits:** Laptev (1974) already proves exact weighted-Cauchy
spectral constants using related localization, and Arazy–Zelenko (2006)
already connect nonlinear rank-one functional calculus to two Hankel/Riesz
channels. Root-exponential compression and operator Hölder existence are
also established. The possible new content is the precisely normalized
universal nonlinear matrix theorem and its uniform transitions.

- [Classification paper](matmul/fractional-channel-classification.pdf)
- [Basic constant paper](matmul/sharp-fractional-holder.pdf)
- [Verification record](matmul/channel-classification-proof-checks.txt)
- [Uniform-law audit](matmul/vanishing-branch-independent-audit.txt)
- [Adversarial priority assessment](matmul/channel-classification-priority-audit.txt)

## 3. Nongalactic matrix-function update algorithms

The square-root case takes $A=XX^T$, with $X$ of size $N\times m$,
and a supplied rank-at-most-$r$ symmetric update $E=UKU^T$. Under the
promise $B=A+E\succeq0$, it constructs a signed low-rank factor $F$ with

$$
\|F-(B^{1/2}-A^{1/2})\|_2
\le\varepsilon\|E\|_2^{1/2}
$$

with probability at least $1-\delta$, in conventional arithmetic

$$
\widetilde O(Nmr+m^3).
$$

The bounds include singular endpoints, critical downdates and cancellation
in the supplied factors. They do not require a supplied base square root,
spectral gap or condition number. Accuracy/confidence dependencies are
logarithmic. The output width is $O(r\log^2(2r/\varepsilon))$ and attains
the sharp leading worst-case rank coefficient at fixed $r$ as
$\varepsilon\downarrow0$.

The construction also covers specified whole-line Hermitian fractional
maps and rectangular absolute/polar fractional-map corrections. For
rectangular right-absolute and polar corrections, full output expansion
fits the same asymptotic cost. Dense square/left-absolute expansion has
an additional output cost.

The proved same-guarantee comparison is:

| Realization | Conventional construction cost |
|---|---|
| Explicit Gram construction | $\widetilde O(Nm^2+m^3)$ |
| Proposed raw-factor construction | $\widetilde O(Nmr+m^3)$ |

The speedup can approach $m/r$ when $Nr$ is large compared with $m^2$.
For $N=\Theta(m)$ both remain cubic; for $r=m$ there is no order gain.

**Why it matters:** this is a concrete theoretical algorithm using ordinary
operations, with fully charged inverse actions and sharp leading output
ranks. It fits the requested meaning of nongalactic.

**Limits:** this improves a proved explicit-Gram baseline, not a certified
global state-of-the-art bound. Rational updates and randomized
preconditioning are old, and the full bound might follow from a routine
composition of prior methods. It approximates the correction on the
update scale, not relative to the possibly much smaller correction norm.
It does not compute the entire updated root from scratch.

The square-root case uses exact field operations, comparisons, scalar
square roots and randomness. General non-dyadic powers retain an explicit
scalar-power qualification. Finite-word stability is not proved.
“Sharp” describes the asymptotic leading output rank, not optimal running
time or the exact best rank for a particular input.

- [Algorithm paper](matmul/sharp-matrix-function-updates.pdf)
- [Verification record](matmul/sharp-update-proof-checks.txt)
- [Source audit](matmul/sharp-update-algorithm-independent-audit.txt)
- [Prior-work comparison](matmul/sqrt-update-sota-audit.txt)
- [Existing rational-Krylov update methods](https://arxiv.org/abs/2008.11501)

## 4. Concrete quantum relative-entropy certificates

For trace-one positive definite states,

$$
D(\rho\Vert\sigma)=\operatorname{Tr}\rho(\log\rho-\log\sigma),
\qquad
\chi_{\rm P}^2=\operatorname{Tr}(\rho^2\sigma^{-1})-1.
$$

A classical inverse-of-sum infimal-convolution identity gives an exact
Petz rational-kernel epigraph using two complex-Hermitian PSD blocks of
order $2n$ per pole. Combining that lift with the positive approximants
gives convex lower and upper functions satisfying

$$
D_m^-\le D\le D_m^+,\qquad
D_m^+-D_m^-=\frac{\eta}{2}\chi_{\rm P}^2.
$$

The upper construction needs one additional $2n$ block. An independently
reviewed outward-rounded interval certificate verifies the ideal
25-pole construction with

$$
e\le5\times10^{-7},\qquad
\eta=\frac{2e}{1+e}<10^{-6}.
$$

Consequently **50 lower blocks and 51 upper blocks**, each of order $2n$,
suffice, with bracket width below $5\times10^{-7}\chi_{\rm P}^2$.
This is a chi-squared-scaled guarantee, not a universal absolute
$10^{-6}$ entropy error.

For a nonempty feasible optimization set with $\chi_{\rm P}^2\le R$,
the corresponding optimal-value bracket has width at most $\eta R/2$.
A lower optimizer, when it exists, supplies an a posteriori bound using
its own chi-squared value. Validated feasible lift values and a valid
dual lower bound also give a certificate without a matrix-log evaluation.

**Why it matters:** this gives a finite, explicit representation-size and
error guarantee with manageable pole counts.

**Limits:** the small-block structure was already asserted in
Faust–Fawzi Theorem 5, and the lift uses a classical identity. Its invention
is not a new claim. The interval certificate concerns the ideal exact
rational construction; it does not certify numerical pole/residue
preparation, a solved SDP instance, or a fast generic SDP solver.
Block size alone does not establish quadratic or cubic solver runtime.

- [Integrated paper](matmul/positive-rational-approximation.pdf)
- [Quantum and interval-code audit](matmul/quantum-small-block-independent-audit.txt)
- [Reproducible interval certificate](matmul/quantum-product-certificate.py)

From the repository root, the certificate can be run with assertions enabled:

~~~sh
python3 matmul/quantum-product-certificate.py
~~~

## Evidence standard and breakthrough status

The manuscripts have separate AI-agent proof reviews, including
source-specific reviews. The finite certificate has directed-rounding
checks and matching C/pure-Python Decimal runs. These are meaningful
checks, but AI reviews share failure modes and do not replace outside
specialist scrutiny or establish priority.

The remaining questions are:

1. Do external experts confirm the proofs, especially the uniform
   nonlinear lower bounds and transition limits?
2. Are the exact claims new, rather than consequences of older results
   that the bounded searches missed?
3. Does the algorithm improve the strongest available method under the
   same input, error, output and arithmetic model?
4. Are the results influential enough to warrant a broader “breakthrough”
   label? That judgment requires more evidence than internal audits.

No hardware benchmark is required for the requested theoretical notion
of practicality. Finite-precision implementation claims would require
additional analysis.

**Current conclusion:** the conjecture proofs and uniform matrix theorem
could be substantial specialist advances if externally validated and new.
The algorithm and quantum construction are useful consequences with
greater prior-art overlap. Calling the collection a demonstrated seminal
breakthrough would overstate the present evidence. None of these results
establishes the original general $N^2$ matrix-product target or $\omega=2$.
