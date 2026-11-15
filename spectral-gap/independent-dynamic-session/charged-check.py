"""Dense diagnostics of the charged proof, not an implementation of KOSZ.

Exact dense solves supply reference flows; controlled feasible flow errors
exercise the theorem's access guarantee. The separate balanced Gram check
tests the scalar quadrature implementation. No timing claim uses this file.
"""
from pathlib import Path
import json
import math
import numpy as np

rng = np.random.default_rng(81473)
rows = []
for span in (0.0, 4.0, 8.0):
    n = 9
    edges = [(i, i + 1) for i in range(n - 1)]
    edges += [(0, 3), (2, 6), (4, 8)]
    D = np.zeros((len(edges), n))
    for k, (p, q) in enumerate(edges):
        D[k, p], D[k, q] = 1.0, -1.0
    weights = np.exp(rng.uniform(-span / 2, span / 2, len(edges)))
    L = D.T @ (weights[:, None] * D)
    Q = np.linalg.qr(np.column_stack([np.ones(n), np.eye(n)[:, 1:]]))[0][:, 1:]
    A0 = Q.T @ L @ Q
    b = np.eye(n)[1] - np.eye(n)[7]
    u = Q.T @ b
    tau = 0.8
    d = tau / float(u @ np.linalg.solve(A0, u))
    weights = weights / d
    A = A0 / d
    lam, V = np.linalg.eigh(A)
    v = Q @ np.linalg.solve(A, u)
    Bvals, BV = np.linalg.eigh(A + np.outer(u, u))

    for alpha in (0.25, 0.5, 0.75):
        eps = 0.08
        ca = math.sin(math.pi * alpha) / math.pi
        tmin = eps / (100 * n * (1 + tau)**2)
        tmax = (100 * (1 + tau) / eps)**(1 / (1 - alpha))
        h = 0.18
        js = np.arange(math.floor(math.log(tmin) / h), math.ceil(math.log(tmax) / h) + 1)
        ts = np.exp(h * js)
        J = h * len(ts)
        eta = 1e-8
        zeta = min(1e-9, eps / (1000 * math.sqrt(n * tau**2 * J * max(ts))))
        error = Q @ rng.normal(size=n - 1)
        error *= eta * math.sqrt(tau) / math.sqrt(float(error @ (D.T @ (weights[:, None] * D)) @ error))
        vt = v + error
        vc = np.clip(vt, vt[7], vt[1])
        vc -= vc.mean()
        vs = Q.T @ vc
        normv2 = float(vc @ vc)
        cols = []
        flow_certificate = 0.0
        worst_flow_ratio = 0.0
        for t in ts:
            y = Q @ (V @ ((V.T @ vs) / (lam + t)))
            fs = weights * (D @ y)
            gs = t * y
            opt = float(vc @ y)
            df = rng.normal(size=len(edges))
            dg = -D.T @ df
            excess = float(np.sum(df**2 / weights) + (dg @ dg) / t)
            df *= zeta * math.sqrt(opt / excess)
            dg = -D.T @ df
            fh = fs + df
            gh = gs + dg
            x = D.T @ fh
            # Feasibility is assessed at the scale of the demand.
            assert np.linalg.norm(x + gh - vc) <= 1e-8 * (1 + np.linalg.norm(vc))
            e = Q.T @ (D.T @ df)
            relerr2 = float(np.sum((V.T @ e)**2 * lam**(-alpha)))
            theory = zeta**2 * opt * t**(1 - alpha)
            worst_flow_ratio = max(worst_flow_ratio, relerr2 / max(theory, 1e-300))
            assert relerr2 <= theory * (1 + 1e-7) + 1e-30
            s = float(np.sum((V.T @ u)**2 / (lam + t)))
            shat = s * (1 + eta * rng.uniform(-1, 1))
            a = ca * h * t**(alpha + 1) / (1 + shat)
            cols.append(math.sqrt(a) * x)
            flow_certificate += a * float(np.sum(fh**2 / weights))
        Z = np.column_stack(cols)
        Zs = Q.T @ Z
        invhalf = (V * lam**(-alpha / 2)) @ V.T
        T = invhalf @ Zs
        Delta = (BV * Bvals**alpha) @ BV.T - (V * lam**alpha) @ V.T
        C = invhalf @ Delta @ invhalf
        C = (C + C.T) / 2
        rawerr = float(np.linalg.norm(C - T @ T.T, 2))
        # Hhat=H+gamma I is an explicit allowed additive Gram error.
        U, sv, VT = np.linalg.svd(T, full_matrices=False)
        gamma = eps / 64
        keep = sv**2 + gamma > eps / 2
        X = Z @ VT[keep].T
        XS = invhalf @ (Q.T @ X)
        residual = C - XS @ XS.T
        residual_eig = np.linalg.eigvalsh((residual + residual.T) / 2)
        rank = int(keep.sum())
        budget = alpha * math.log1p(tau)
        assert rawerr < eps / 8
        assert residual_eig[0] >= -eps / 8
        assert residual_eig[-1] <= 3 * eps / 4
        assert rank == 0 or rank < budget / math.log1p(eps / 4)
        actual_a1 = float(np.sum((V.T @ Zs)**2 / lam[:, None]))
        assert actual_a1 <= flow_certificate * (1 + 1e-7)
        rows.append(dict(alpha=alpha, log_weight_span=span,
            condition=float(lam[-1] / lam[0]), raw_width=len(ts),
            raw_relative_error=rawerr, final_rank=rank,
            final_min_relative_residual=float(residual_eig[0]),
            final_max_relative_residual=float(residual_eig[-1]),
            determinant_budget=budget, rank_upper=budget / math.log1p(eps / 4),
            gram_moment=actual_a1, flow_moment_certificate=flow_certificate,
            worst_flow_bound_ratio=worst_flow_ratio, passed=True))

out = dict(status="passed", cases=rows,
    limitation="Dense diagnostic with injected feasible errors; KOSZ runtime is proved, not benchmarked here.")
path = Path(__file__).with_name("charged-checks.json")
path.write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(dict(status="passed", cases=len(rows), output=str(path))))
