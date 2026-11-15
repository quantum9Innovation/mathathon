#!/usr/bin/env python3
"""Dense corroboration of identities in the independent audit, not proofs."""
import json
from pathlib import Path
import numpy as np
from scipy.integrate import quad

ROOT = Path(__file__).resolve().parent

def power(a, exponent, singular=False):
    vals, vecs = np.linalg.eigh((a + a.T) / 2)
    if singular:
        vals[0] = 0
    assert vals.min() > -1e-9
    vals = np.maximum(vals, 0)
    p = np.where(vals > 0, vals ** exponent, 0)
    return (vecs * p) @ vecs.T

def mean(a, b, exponent):
    sq = power(a, .5)
    invsq = power(a, -.5)
    return sq @ power(invsq @ b @ invsq, exponent, True) @ sq

def laplacian(n, edges):
    l = np.zeros((n, n))
    for u, v, w in edges:
        b = np.eye(n)[u] - np.eye(n)[v]
        l += w * np.outer(b, b)
    return l

def hmat(l, d, alpha):
    sq = np.diag(np.sqrt(np.diag(d)))
    invsq = np.diag(1 / np.sqrt(np.diag(d)))
    return sq @ power(invsq @ l @ invsq, alpha, True) @ sq

def logpdet(a):
    return np.log(np.linalg.eigvalsh((a + a.T) / 2)[1:]).sum()

def basis(n):
    return np.linalg.qr(np.column_stack([np.ones(n), np.eye(n)[:, :-1]]))[0][:, 1:]

checks = []
for n in (4, 6, 9):
    edges = [(i, i+1, 1+.1*i) for i in range(n-1)]
    edges += [(0, n-1, .3), (0, n-2, .7)]
    l = laplacian(n, edges)
    d = np.diag(np.diag(l))
    v = np.diag(d).sum()
    e = np.eye(n)[:, :2]
    delta = 1.
    b = e[:, 0] - e[:, 1]
    m = l + delta * np.outer(b, b)
    dp = d + delta * e @ e.T
    s = d - np.outer(np.diag(d), np.diag(d)) / v
    sp = dp - np.outer(np.diag(dp), np.diag(dp)) / np.diag(dp).sum()
    f = e - np.outer(np.diag(d), np.ones(2)) / v
    k = delta*np.eye(2)-delta**2*np.ones((2,2))/(v+2*delta)
    short_error = np.linalg.norm(sp-s-f@k@f.T)
    q = basis(n)
    for alpha in (.2, .5, .8):
        h = hmat(l, d, alpha)
        hp = hmat(m, dp, alpha)
        determinant_error = abs(logpdet(h)-alpha*logpdet(l)-(1-alpha)*(np.log(n)+np.log(np.diag(d)).sum()-np.log(v)))
        rel_budget = alpha*np.log1p(delta*b@np.linalg.pinv(l)@b)+(1-alpha)*(np.log1p(delta/d[0,0])+np.log1p(delta/d[1,1])-np.log1p(2*delta/v))
        budget_error = abs(logpdet(hp)-logpdet(h)-rel_budget)
        a = q.T@l@q
        sr = q.T@s@q
        sq = power(a, .5)
        isq = power(a, -.5)
        hs = q @ (sq @ power(isq@sr@isq, 1-alpha) @ sq) @ q.T
        short_mean_error = np.linalg.norm(h-hs)/np.linalg.norm(h)
        checks.append(dict(n=n, alpha=alpha, determinant_error=float(determinant_error),budget_error=float(budget_error),shorted_update_error=float(short_error),shorted_mean_error=float(short_mean_error),min_response_eigenvalue=float(np.linalg.eigvalsh(q.T@(hp-h)@q).min())))

slow_checks = []
x = np.array([1.,1.,-1.,-1.])
b = np.array([1.,-1.,0.,0.])
e = np.eye(4)[:, :2]
alpha = .5
for h in (1e-2,1e-3,1e-4,1e-5,1e-6,1e-7):
    l = laplacian(4, [(0,1,1.),(1,2,h),(2,3,1.)])
    d = np.diag(np.diag(l))
    m = l + np.outer(b,b)
    dp = d + e@e.T
    hm = hmat(l,d,alpha)
    hmp = hmat(m,dp,alpha)
    den = x@hm@x
    response = x@(hmp-hm)@x
    def f(t):
        r = np.linalg.inv(l+t*d)
        q = np.linalg.inv(m+t*d)
        edge = t**alpha*(x@d@r@b)**2/(1+b@r@b)
        z = x@m@q@e
        mass = t**(alpha-1)*z@np.linalg.solve(np.eye(2)+t*e.T@q@e,z)
        return (edge+mass)/np.pi
    tail = quad(f,1e-2,np.inf,epsabs=1e-15)[0]
    slow_checks.append(dict(h=h,before_coefficient=float(den/h**alpha),after_coefficient=float((x@hmp@x)/h**alpha),relative_response=float(response/den),retained_relative_response=float(tail/den),predicted_relative_limit=float((4/3)**(1-alpha)-1)))

offdiag_checks = []
l = laplacian(4, [(0,1,1.),(1,2,1.),(2,3,1.)])
d = np.diag(np.diag(l))
m = l + np.outer(b,b)
dp = d + e@e.T
for alpha in (.25,.5,.8):
    dense = (hmat(m,dp,alpha)-hmat(l,d,alpha))[2,3]
    def scalar(t):
        z = t*(t+2)
        return np.sin(np.pi*alpha)/np.pi * 2*t**(alpha-1)*(1+t)**2/((t+2)*(3+4*z)*(4+6*z))
    integral = quad(scalar,0,1,epsabs=1e-12)[0]+quad(scalar,1,np.inf,epsabs=1e-12)[0]
    offdiag_checks.append(dict(alpha=alpha,dense_positive_entry=float(dense),scalar_integral_entry=float(integral),absolute_error=float(abs(dense-integral))))

out = dict(identity_checks=checks,slow_cutoff_checks=slow_checks,positive_offdiagonal_checks=offdiag_checks)
(ROOT/'normalized-audit-checks.json').write_text(json.dumps(out,indent=2)+'\n')
assert max(max(c[k] for k in ('determinant_error','budget_error','shorted_update_error','shorted_mean_error')) for c in checks)<1e-10
assert min(c['min_response_eigenvalue'] for c in checks)>-1e-10
assert abs(slow_checks[-1]['relative_response']-slow_checks[-1]['predicted_relative_limit'])<1e-5
assert min(c['dense_positive_entry'] for c in offdiag_checks)>0
assert max(c['absolute_error'] for c in offdiag_checks)<1e-10
print('PASS: 9 identity/PSD examples, 6 slow-cutoff examples, 3 positive-entry examples.')
print(json.dumps(slow_checks[-1],indent=2))
print(json.dumps(offdiag_checks,indent=2))
