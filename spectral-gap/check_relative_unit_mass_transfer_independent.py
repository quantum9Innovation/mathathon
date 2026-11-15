"""Independent finite stress test of unit-mass fast-block transfer.

The proof is the manuscript; this is a separate numerical falsification check.
Use only symmetric eigensolvers on explicitly projected common supports.
"""
import json
from pathlib import Path
import numpy as np


def support_basis(kernel):
    n=len(kernel)
    v=np.asarray(kernel,dtype=float)
    v=v/np.linalg.norm(v)
    # Householder maps e_1 to v; remaining columns span v-perp.
    w=v.copy(); w[0]-=1.0
    if np.linalg.norm(w)<1e-12:
        return np.eye(n)[:,1:]
    w/=np.linalg.norm(w)
    return (np.eye(n)-2*np.outer(w,w))[:,1:]


def power(A,alpha):
    a,V=np.linalg.eigh((A+A.T)/2)
    assert a.min()>0, a
    return (V*a**alpha)@V.T


def correction_spectrum(A,B,kernel,alpha):
    Z=support_basis(kernel)
    a=Z.T@A@Z; b=Z.T@B@Z
    W=power(a,-alpha/2)
    C=W@(power(b,alpha)-power(a,alpha))@W
    return np.linalg.eigvalsh((C+C.T)/2)[::-1]


def laplacian(weights):
    L=np.zeros((len(weights)+1,len(weights)+1))
    for i,w in enumerate(weights):
        L[i,i]+=w;L[i+1,i+1]+=w
        L[i,i+1]-=w;L[i+1,i]-=w
    return L


# Quotient masses (9,4,1) correspond to an exactly represented positive-mass
# path. Its edges are 6 and 2; the first edge doubles, so leverage is 1.
blocks=[9,4,1]
M=np.asarray(blocks,dtype=float)
K=laplacian([6.0,2.0]); Kp=laplacian([12.0,2.0])
scale=1/np.sqrt(M)
H=K*scale[:,None]*scale[None,:]
Hp=Kp*scale[:,None]*scale[None,:]
rows=[]
for alpha in [.2,.5,.8]:
    target=correction_spectrum(H,Hp,np.sqrt(M),alpha)
    previous=float('inf')
    for fast in [1e2,1e3,1e4,1e5]:
        weights=[]
        for i,m in enumerate(blocks):
            weights.extend([fast]*(m-1))
            if i<2: weights.append([6.0,2.0][i])
        weights_updated=weights.copy()
        weights_updated[blocks[0]-1]=12.0
        L=laplacian(weights); Lp=laplacian(weights_updated)
        actual=correction_spectrum(L,Lp,np.ones(sum(blocks)),alpha)
        padded=np.r_[target,np.zeros(len(actual)-len(target))]
        error=float(np.max(np.abs(actual-padded)))
        assert error<previous, (alpha,fast,error,previous)
        previous=error
        # Independent exact determinant budget, numerically reconstructed.
        budget=float(np.sum(np.log1p(actual)))
        assert abs(budget-alpha*np.log(2))<2e-8
        rows.append(dict(alpha=alpha,internal_conductance=fast,
                         dimension=len(L),max_spectral_error=error,
                         logdet_budget_error=abs(budget-alpha*np.log(2))))
    assert previous<.004

out={'scope':'unit-mass path fast-block transfer diagnostic; not proof',
     'quotient_masses':blocks,'base_external_conductances':[6,2],
     'updated_external_conductances':[12,2], 'leverage':1,
     'rows':rows}
p=Path(__file__).with_suffix('.json')
p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
