# Assembled manuscript audit

**Verdict: PASS. No mathematical gaps found in the reviewed source.**

Reviewed file: `../unweighted-degree-dichotomy.tex`.

SHA256 of the exact source reviewed:
`7fee1542cb46ef2267241233dd4ad292b16dad56c61749126b81360095e5965f`.
The preceding version was reread in full; the final mathematical
revision to Section 6 was independently rechecked, with the rest
unchanged. The final hash was checked after this read. Audit date:
2026-11-15. This audit makes no build/layout assessment; the parent is
handling those checks.

- The degree-two statements and cycle bound check. In the cycle Fourier
  basis `z_k=1/n` and
  `lambda_k>=16 min(k,n-k)^2/n^2`, giving
  `nu((0,delta])<=sqrt(delta)/2`; for `delta>=4` the same bound follows
  from total leverage at most one. The path/cycle upper and path lower
  therefore imply the stated degree-two order.
- The centered-limit reduction and constant are consistent: the
  logarithmic density has low-energy slope `1/2`; symbol comparison
  reduces to `K_(1/2)`; the substitution `u=exp(x/2)` gives precisely
  `2 sqrt(uv)/(u+v)` and Laptev parameter `rho=1`. The high-energy block
  has analytic-kernel exponential rank approximation even with the
  integrable endpoint density singularity. Loewner sandwiches and
  pinching preserve the leading constant. The fixed-endpoint corollary
  similarly gives `rho=3`, hence coefficient `1/(6 pi^2)`.
- The integrated separated-mass lemma preserves the independently
  audited proof: principal minors first establish separated eigenvalue
  scales; resolvent limits identify leverage weights; dominated
  convergence and off-diagonal decay yield reverse-pivot factors.
  Compact-family uniformity follows by subsequences.
- The fanout constants, determinant quotient, anchor grounding and
  finite-reservoir passage check. In the reservoir lemma, both low
  spaces are `O(s^-1/2)` from the indicator space. Thus the updated high
  fractional power compressed to the baseline low space is `O(s^-1)`;
  after relative scaling it vanishes as `s^(alpha-1)`. Common kernels
  and the fixed positive low gap justify the inverse-power limit.
  The final min-max transfer uses only this compression, as required.
- The final stronger Jensen outlier checks exactly. With
  `eta=||u||^2` and `a=u^TAu/eta`, convexity gives
  `m(t)>=eta/(a+t)`. Since `z^2/(1+z)` is increasing on nonnegative
  scalars, the Rayleigh numerator is at least
  `eta[(a+eta)^alpha-a^alpha]`; concavity gives denominator at most
  `eta a^alpha`. Thus the general lower bound is
  `(1+eta/a)^alpha-1`. For an existing unit edge, `eta=2` and
  `a=(deg(p)+deg(q)+2)/2<=d+1`, proving the displayed
  `zeta_(alpha,d)=(1+2/(d+1))^alpha-1`. Subtracting its logarithmic
  determinant cost gives precisely
  `limsup eps W_(d,alpha)(eps)
   <=alpha log[2(d+1)/(d+3)]`. Failure of full fixed-degree spectral
  closure follows as stated.

Primary theorem statements were already checked by the research team;
this pass rechecked their algebraic specialization and integration,
not the external papers' proofs. Historical priority and optimal
uniform leading constants remain explicitly unclaimed.
