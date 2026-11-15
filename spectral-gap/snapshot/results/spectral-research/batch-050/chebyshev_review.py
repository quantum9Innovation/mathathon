"""Independent numeric audit of the m1 Chebyshev Cauchy-kernel formulas."""
import json
from pathlib import Path
import numpy as np

checks=[]
for d in (3,4,7):
    for lam in (2.95,3.2,3.6):
        alpha=2*np.sqrt(d-1)
        if lam<=alpha:
            continue
        tau=lam/alpha
        rho=tau+np.sqrt(tau*tau-1)
        const=2/(alpha*np.sqrt(tau*tau-1))
        best=0
        worst_d=0
        for m in (4,10,20,40):
            x=np.linspace(-alpha,alpha,1001)
            q=np.full_like(x,const/2)
            for k in range(1,m+1):
                q=q+const*np.cos(k*np.arccos(x/alpha))/rho**k
            # The graph kernel is negative after rescaling:
            # 1/(x-lam) = -(t-x/alpha)^(-1)/alpha.
            q=-q
            err=np.max(np.abs(q-1/(x-lam)))
            tail=const*rho**(-m)/(1-1/rho)
            assert err<=tail*(1+1e-10),(d,lam,m,err,tail)
            rho_d=d/alpha+np.sqrt((d/alpha)**2-1)
            # Evaluate the polynomial at the Perron host value d.
            angle=np.arccosh(d/alpha)
            qd=const/2+sum(const*np.cosh(k*angle)/rho**k for k in range(1,m+1))
            ratio=rho_d/rho
            growth=max(ratio**m,m) if ratio<=1 else ratio**m
            geometric_cap=sum(ratio**k for k in range(m+1))
            assert abs(qd)<=const*geometric_cap*(1+1e-10)
            best=max(best,err)
            worst_d=max(worst_d,abs(qd))
        checks.append(dict(d=d,lam=lam,alpha=alpha,rho=rho,maximum_observed_chebyshev_error=best,
                           maximum_observed_perron_polynomial_value=worst_d,
                           formulas_passed=True))
result=dict(source='Independent implementation, no import of member code',
            tests='Cauchy Chebyshev tails and evaluation at the removed Perron pole',
            checks=checks)
p=Path(__file__).with_suffix('.json')
p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
