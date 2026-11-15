# Accepted review of m5: finite-root reduction

## Outcome

Accepted the exact reduction and its algebraic content. Together with the separately
accepted resolvent estimates, it yields the limiting top-two-eigenvalue formula for
fixed separated attachment sets and fixed degree.

## Reviewed proof structure

The host-pole multiplicity lemma is correct and sharpens the old survival statement:
a host eigenvalue can gain multiplicity when $P_\mu\mathbf1_T=0$ and the pseudoinverse
condition holds. The exact secular factor identity also checks.

Cauchy interlacing after deleting the new vertex gives $\lambda_2(G')\le d$, while
positivity or increased average degree gives $\lambda_1(G')>d$. The relative order is
therefore fixed without randomness. Strict monotonicity of the secular function
controls root locations, and the full Kesten-McKay transform rather than the one-sided
branch produces the threshold $2(d-2)$.

For $\Delta\le2(d-2)$, the correct lower bound is
$\lambda_2(G')\ge\lambda_2(G)$ by interlacing. With the known regular-host edge law,
this closes the second-eigenvalue statement up to the top edge.

## Boundary-case correction

The proof as written has a bad general inference in Step 3 when $h(d)=0$: an empty
one-sided sign set does not create a useful inequality by itself. The actual integer
model avoids that case. The requirement $\lambda_f=d$ forces
$\Delta=d^2(d-2)/(d-1)$, which is nonintegral for every integer $d\ge3$. Acceptance
therefore excludes that case and does not assert a continuum-critical theorem from
this text.

## Executed checks

- `scripts/exact_algebra.py` succeeded, including the scalar transform equations,
  closed forms, both branches and the exact secular identity.
- Its exhaustive host-pole comparison covered 149009 instances and reported zero
  mismatches across all three multiplicity cases.
- `scripts/finite_root_test.py` completed, reproducing the reference values and small
  secular residuals at the peak eigenvalues.
- [Host-pole analysis](host-pole-analysis.md) records the independent ordering check,
  including the integer-model qualification.

## Scope

The accepted combination includes no $1/n$ asymptotic, no edge fluctuation law and no
unproved resolvent rate. It does not extend the separated-degree threshold to clustered
attachments. For those, the m6 resolvent sum has extra off-diagonal terms and the root
calculation must use the corrected kernel. No formal proof assistant certificate or
comprehensive novelty audit is claimed.
