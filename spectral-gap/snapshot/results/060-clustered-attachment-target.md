# Batch 060 target: clustered-attachment secular law

## Why this is a new problem

The separated-case result uses disappearance of off-diagonal tree resolvent terms
between fixed labels at random positions. That argument is now fixed and accepted.
It does not apply to attachment vertices with persistent bounded geodesic distances.

For a clustered set $T$, the local tree gadget leads to

$$\Phi_T(\lambda)=\lambda-G_d(\lambda)\sum_{s,t\in T}r(\lambda)^{\rho(s,t)},$$

where $\rho$ is the distance in the local tree pattern and $r, G_d$ are the usual
branch functions. The previous formula $-\Delta G_d$ is exactly the case where
$\rho(s,t)=\infty$ for all $s\ne t$. It is not a universal clustered answer.

The target is the complete secular law, **not** merely this resolvent identity.

## Model to make precise

Fix $d\ge3$ and a finite marked rooted-tree pattern $(C,T)$ of radius at most $R$.
The host $G_n$ is uniformly random simple $d$-regular on $[n]$, with a fixed centre
label $c$. The attachment vertices $T_n$ are obtained by a fixed deterministic
procedure from a radius-$R$ neighbourhood of $c$. The graph $G_n'$ adds one new vertex
adjacent exactly to $T_n$. The new vertex has fixed degree $|T|$ independent of $n$.

**Primary test families.** An adjacent pair $\{c,u\}$ with a prescribed neighbour
$u$ of $c$, and the full neighbourhood $T=N(c)$. They have unambiguous rooted
gadgets. Every pair has distance one in the first case, and every distinct pair has
distance two in the second. With probability tending to one, the required bounded
neighbourhood of host $c$ is the expected $d$-regular tree ball.

**No ill-posed broadening.** A claim for general patterns must specify the rooted
embedding or a finite family of distance matrices supported by this host. An
arbitrary graph-dependent or random $T$ is not silently included. A generic
local-convergence argument is not sufficient to give a deterministic pattern law.

## Mathematical target

For an admissible fixed pattern, use the rank-one Perron splitting or another fully
verified method to prove that on every compact interval $J$ away from the bulk edge,
Perron pole $d$, and any singularities of the local kernel,

$$\mathbf1_{T_n}^T(A_n-\lambda I)^{-1}\mathbf1_{T_n}
\longrightarrow -G_d(\lambda)\sum_{s,t\in T}r(\lambda)^{\rho(s,t)}$$

in probability. Consequently, after removing the known Perron term on compact sets
avoiding $d$,

$$\Sigma_n(\lambda)\longrightarrow \Phi_T(\lambda)$$

in probability, where $\Sigma_n$ is the exact added-vertex secular function and
$\Phi_T$ is the pattern-specific limit function.

Then prove:

- the algebraic threshold for exterior secular roots, including its initial
  $r(2\sqrt{d-1})=1/\sqrt{d-1}$ evaluation,
- which intervals genuinely contain roots and their order of contact,
- which eigenvalue each root represents, with Cauchy interlacing and host-eigenvalue
  multiplicity handled explicitly,
- both limiting eigenvalues where the statement applies,
- any differing displacement near $d$, rather than replacing only $\Delta$ in the
  old constant without derivation.

If $\Phi_T$ has a repeated root or the integer pattern gives $\lambda_f=d$, keep that
case as a real branch of the target. Do not import the separated-model exclusion
$\lambda_f\ne d$.

## Leading examples to compute exactly

### Adjacent pair

For $T=\{c,u\}$ with $\rho(c,u)=1$,

$$K_{\rm adj}(\lambda)=G_d(\lambda)(2+2r(\lambda)).$$

Using $G_d=r/(1-r^2)$ gives the equivalent form
$K_{\rm adj}(\lambda)=2r(\lambda)/(1-r(\lambda))$. The graph secular limit should be
$\lambda-K_{\rm adj}(\lambda)$, with the first one replaced by the full exact form
in every numerical implementation. Derive its exterior roots and their meaning from
scratch. Do not infer them from the original degree-two formula.

At the bulk edge $b=2\sqrt{d-1}$,

$$K_{\rm adj}(b)=\frac{2}{1-1/\sqrt{d-1}}.$$

This already distinguishes $d=3,4$ from larger-degree cases and must not be
masked by an asymptotic expansion that loses the branch point.

### Neighbourhood of one centre

For $T=N(c)$ in the $d$-regular tree, the explicit block inverse has diagonal
$G_d+r^2/(\lambda-dr)$ and every off-diagonal entry $r^2/(\lambda-dr)$,
wherever that expression is nonsingular. The sum is also available in the
positive-coordinate form

$$K_{N(c)}(\lambda)=G_d(\lambda)\left[d+d(d-1)r(\lambda)^2\right].$$

The equivalent $d\lambda r/(\lambda-dr)$ form may be used only after its domain is
verified. A pole of this representation must not be confused with an actual spectral
zero elsewhere in the argument. Implementations should prefer the positive explicit
coordinates when working near the branch point or pole.

## Required root-level result

The primary theorem must establish the complete finite-host secular law for at least
one of these two explicitly clustered families. A meaningful result contains:

1. Its precise resolvent limit, including pattern-dependent kernel and the removed
   host-Perron term.
2. Its exterior-root threshold and exact or algorithmically computable root function.
3. Its limiting second eigenvalue and its location relative to $d$.
4. Its leading eigenvalue formula, using both exterior roots and the unique above-$d$
   root, with Cauchy order and host-pole estimates.
5. A complete treatment of every exceptional repeated-root, pole or critical degree
   in the claimed range, or a clearly restricted parameter range excluding them.

A broader all-pattern generalisation is worthwhile only if it preserves the same
precision. A resolvent-only statement is a partial result and does not close the
batch's main target.

## Evidence required for acceptance

### Full success

- Complete proofs for the resolvent limit and root mapping for at least one family,
  with exact sensitivity to the attachment distances.
- Explicit threshold and order computations alongside a proof that no competing
  eigenvalue changes the claimed top-two identification.
- Pole and multiplicity audits at $d$ and at every singularity of the pattern kernel.
- Exact arithmetic or symbolic checks of the local inverse and threshold formulas.
- Numerical comparison of direct sparse eigensolvers to the asserted secular roots,
  with the uniform simple sampling model and raw seeds disclosed.
- Recovery of the previous separated-case formula as the limiting large-distance
  specialisation. That consistency test must not rewrite the frozen proof.

### Limited success

- A fully proved resolvent limit with a precise remaining root obstruction, or
- A complete eigenvalue theorem for a genuinely restricted family or degree range
  that excludes identified singular parameters, or
- A rigorously verified counterexample to a proposed threshold, with the corrected
  pattern formula and a precise statement of what it invalidates.

### What does not count

- Merely repeating the off-diagonal tree formula,
- Splicing the old $\Delta G_d$ theorem into a clustered model,
- Calling a root simple or avoiding $d$ without proof,
- Using a limiting fractional degree or nonintegral $\Delta$ as if it were an
  actual finite-graph example,
- Using disconnected raw runs without detecting pseudo-inverses,
- Treating the numerical agreement of finite graphs as an existence proof,
- Avoiding algebraic poles by an unexplained renormalisation,
- Retroactively changing the accepted separated-case proof.

## Execution proposal and gates

- **Proposed time:** three hours total, including the final 45 minutes for review.
- **Proposed members:** four, on `deepseek/deepseek-v4.1-flash` at maximum reasoning
  effort, with distinct local algebra, rooted-kernel, resolvent and adversarial roles.
- **Gate A, 45 minutes:** exact kernels for both test families have been verified and
  every compact domain excludes identified poles appropriately.
- **Gate B, 90 minutes:** at least one family has a full root-limit argument with a
  valid singular-case classification. Otherwise the report keeps only the strongest
  exact resolvent result and the explicit missing estimate.
- **Gate C, final 45 minutes:** independent proof audit, rerunning all discriminating
  calculations, and writing `results/060-clustered-attachment.md` with State,
  accepted facts, rejected arguments and the exact next action.

This target is pending. No batch, swarm or clock has been started by writing it.
The three-hour proposal and four-member size are not launches and can be changed
before a later explicit start.
