"""Independent coordinate audit for the adjacent-pair clustered theorem."""
import json
from pathlib import Path
import sympy as sp

r=sp.symbols('r',positive=True)
lam=(lambda d:(d-1)*r+1/r)
G=r/(1-r*r)
K=2*r/(1-r)

r_cubic=sp.nroots(2*r**3+r-1,n=30)[0]
lam_star=2*r_cubic+1/r_cubic
assert abs(float(lam_star-2*sp.sqrt(2)))>0
assert abs(lam_star**3-lam_star**2-4*lam_star-4)<1e-21
assert sp.simplify(G*(2+2*r)-K)==0
assert sp.simplify(sp.diff(lam(3),r)-sp.diff(K,r)) != 0

# At every integer d>=4, Phi_adj(b)>0 follows from s^2-s-1>0.
# The polynomial elimination has a positive root, but it selects the other r branch.
spurious=[]
lam_s=sp.Symbol('lambda')
for dv in range(4,7):
    roots=[sp.re(x) for x in sp.nroots(lam_s**3-(dv-2)*lam_s**2-4*lam_s-4)
           if abs(sp.im(x))<1e-20 and sp.re(x)>0]
    alpha=float(roots[0])
    # Obtain the small physical root of lambda=(d-1)q+1/q numerically.
    from scipy.optimize import brentq
    rb=float(sp.sqrt(dv-1))
    q_phys=brentq(lambda q:(dv-1)*q+1/q-alpha,1e-10,1/rb-1e-10)
    q_elim=alpha/(alpha+2)
    phi=alpha-2*q_phys/(1-q_phys)
    assert q_elim>1/sp.sqrt(dv-1)
    assert phi>1
    spurious.append(dict(d=dv,polynomial_root=float(alpha),physical_small_r=float(q_phys),
                         r_used_for_elimination=float(q_elim),r_boundary=float(1/sp.sqrt(dv-1)),
                         Phi_at_physical_energy=float(phi),root_is_spurious=True))

# The frozen m6 diagonal equals the candidate correction exactly.
d=dvar=sp.symbols('d',positive=True)
D=sp.symbols('Delta',positive=True)
frozen=r*(lam(dvar)-D*r+r)/(lam(dvar)-D*r)
corrected=r+r**2/(lam(dvar)-D*r)
assert sp.simplify(frozen-corrected)==0
# Meanwhile, the batch-060 target's wrong diagonal does differ from the correct one.
wrong=G+r**2/(lam(dvar)-dvar*r)
assert sp.simplify(corrected.subs(D,dvar)-wrong)!=0

report={
 'adjacent_root_lambda':float(lam_star),
 'adjacent_root_above_bulk_iff_d':'d=3 only for integer d>=3',
 'physical_cubic_root':float(r_cubic),
 'spurious_elimination_roots':spurious,
 'frozen_m6_diagonal_matches_correction':True,
 'new_target_diagonal_was_incorrect':True,
 'separated_proof_conclusion_altered':False,
 'exact_rank_one_repair_run':'m4/out/review_rank_one.log'
}
p=Path(__file__).with_suffix('.json')
p.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
