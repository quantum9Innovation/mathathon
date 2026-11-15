#!/usr/bin/env python3
"""Dense diagnostics for graph-fractional-updates.tex, with deterministic seed.

These checks test identities and error estimates. They are neither a proof,
an implementation of a sparse SDD solver, nor a performance benchmark. Known
graph nullspaces are explicitly removed before fractional powers; otherwise
roundoff at a zero eigenvalue can obscure small fractional-power errors.
Requires NumPy. Prints a JSON verification summary.
"""

import json
import math

import numpy as np


SEED = 2026111427
RNG = np.random.default_rng(SEED)


def op(a):
    return float(np.linalg.norm(a, 2))


def symmetric(a):
    return (a + a.T) / 2


def laplacian(n, weights):
    result = np.zeros((n, n))
    for (u, v), weight in weights.items():
        assert weight >= 0
        result[u, u] += weight
        result[v, v] += weight
        result[u, v] -= weight
        result[v, u] -= weight
    return result


def kernel_basis(n, weights):
    neighbors = [[] for _ in range(n)]
    for (u, v), weight in weights.items():
        if weight > 0:
            neighbors[u].append(v)
            neighbors[v].append(u)
    unseen, columns = set(range(n)), []
    while unseen:
        stack, component = [min(unseen)], []
        unseen.remove(stack[0])
        while stack:
            u = stack.pop()
            component.append(u)
            for v in neighbors[u]:
                if v in unseen:
                    unseen.remove(v)
                    stack.append(v)
        column = np.zeros(n)
        column[component] = 1 / math.sqrt(len(component))
        columns.append(column)
    return np.column_stack(columns)


def spectral_parts(a, kernel):
    """Use the supplied exact mathematical nullspace, not eigenvalue clipping."""
    q = np.linalg.qr(kernel, mode="complete")[0]
    z = q[:, kernel.shape[1]:]
    if z.shape[1] == 0:
        return kernel @ kernel.T, np.empty(0), z
    values, vectors = np.linalg.eigh(symmetric(z.T @ a @ z))
    assert values.min() > 0, ("positive spectrum lost", values)
    return kernel @ kernel.T, values, z @ vectors


def power_from_parts(parts, alpha):
    _, values, vectors = parts
    return (vectors * values**alpha) @ vectors.T


def inverse_from_parts(parts, shift):
    projector, values, vectors = parts
    return projector / shift + (vectors / (values + shift)) @ vectors.T


def edits(n, old, new):
    keys = sorted(set(old) | set(new))
    changes = [(edge, new.get(edge, 0.0) - old.get(edge, 0.0)) for edge in keys]
    changes = [(edge, change) for edge, change in changes if change != 0]
    u = np.zeros((n, len(changes)))
    signs, degree_change = [], np.zeros(n)
    for j, ((v, w), change) in enumerate(changes):
        u[v, j], u[w, j] = math.sqrt(abs(change)), -math.sqrt(abs(change))
        signs.append(math.copysign(1.0, change))
        degree_change[v] += change
        degree_change[w] += change
    jmat = np.diag(signs)
    a = math.sqrt(float(degree_change @ degree_change)
                  + 2 * sum(change**2 for _, change in changes))
    b = 2 * sum(abs(change) for _, change in changes)
    return changes, u, jmat, a, b


def graph_cases():
    cases = []
    for trial in range(36):
        n = int(RNG.integers(4, 11))
        old = {(u, v): float(10**RNG.uniform(-1, 1))
               for u in range(n) for v in range(u + 1, n)
               if RNG.random() < 0.35}
        new = dict(old)
        pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
        for index in RNG.choice(len(pairs), size=min(5, len(pairs)), replace=False):
            edge = pairs[int(index)]
            new[edge] = (0.0 if RNG.random() < 0.4 else
                         float(10**RNG.uniform(-1, 1)))
        cases.append((f"random-{trial}", n, old, new))
    cases.extend([
        ("bridge-addition", 6, {(0, 1): 1., (1, 2): .7, (3, 4): .9, (4, 5): 1.2},
         {(0, 1): 1., (1, 2): .7, (3, 4): .9, (4, 5): 1.2, (2, 3): .8}),
        ("bridge-deletion", 6,
         {(0, 1): 1., (1, 2): .7, (2, 3): .8, (3, 4): .9, (4, 5): 1.2},
         {(0, 1): 1., (1, 2): .7, (3, 4): .9, (4, 5): 1.2}),
        ("mixed-connectivity", 5, {(0, 1): 1., (1, 2): 1., (3, 4): 1.},
         {(0, 1): 1., (2, 3): 1., (3, 4): 1.}),
        ("empty-to-edge", 4, {}, {(0, 1): .4}),
        ("edge-to-empty", 4, {(2, 3): .4}, {}),
        ("mixed-degree-cancellation", 4,
         {(0, 1): 2., (1, 2): 2., (2, 3): 2., (0, 3): 2.},
         {(0, 1): 3., (1, 2): 1., (2, 3): 3., (0, 3): 1.}),
    ])
    return cases


def energy_perturbation(a, x, eta):
    h = np.linalg.cholesky(a)
    error = RNG.normal(size=x.shape)
    for j in range(x.shape[1]):
        error[:, j] *= eta * np.linalg.norm(h.T @ x[:, j]) / np.linalg.norm(h.T @ error[:, j])
    return x + error


def identity_diagnostics(cases):
    worst = dict(scale_relative_error=0., resolvent_relative_error=0.,
                 energy_error_bound_ratio=0., symmetric_identity_error=0.,
                 chi_upper_ratio=0., scale_rank_upper_ratio=0.)
    trials = 0
    for name, n, old, new in cases:
        l, lp = laplacian(n, old), laplacian(n, new)
        changes, u, jmat, a, b = edits(n, old, new)
        k, e = len(changes), lp - l
        assert k > 0
        assert op(e - u @ jmat @ u.T) < 2e-13 * max(1., a), name
        scale_error = abs(a - np.linalg.norm(e, "fro")) / a
        worst["scale_relative_error"] = max(worst["scale_relative_error"], scale_error)
        assert scale_error < 2e-14, (name, scale_error)
        assert op(e) <= a * (1 + 2e-14)
        rank_ratio = a / (math.sqrt(k) * op(e))
        chi_ratio = b / (a * math.sqrt(2 * k))
        assert rank_ratio <= 1 + 2e-14 and chi_ratio <= 1 + 2e-14, name
        assert b / a >= 1 - 2e-14, name
        worst["chi_upper_ratio"] = max(worst["chi_upper_ratio"], chi_ratio)
        worst["scale_rank_upper_ratio"] = max(worst["scale_rank_upper_ratio"], rank_ratio)
        for relative_shift in (0.02, 0.3, 4.):
            t = a * relative_shift
            aa, bb = l + t * np.eye(n), lp + t * np.eye(n)
            v, w = np.linalg.solve(aa, u), np.linalg.solve(bb, u)
            target = np.linalg.solve(aa, np.eye(n)) - np.linalg.solve(bb, np.eye(n))
            error = op(v @ jmat @ w.T - target) / max(op(target), 1e-14)
            assert error < 2e-10, (name, t, error)
            worst["resolvent_relative_error"] = max(worst["resolvent_relative_error"], error)
            eta = 0.0125
            vh, wh = energy_perturbation(aa, v, eta), energy_perturbation(bb, w, eta)
            for mat, exact, approx in ((aa, v, vh), (bb, w, wh)):
                h = np.linalg.cholesky(mat)
                ratios = np.linalg.norm(h.T @ (approx-exact), axis=0) / np.linalg.norm(h.T @ exact, axis=0)
                assert ratios.max() <= eta * (1 + 1e-12), (name, ratios)
            node_error = op(vh @ jmat @ wh.T - v @ jmat @ w.T)
            bound_ratio = node_error / (3 * eta * b / t**2)
            assert bound_ratio <= 1 + 1e-12, (name, bound_ratio)
            worst["energy_error_bound_ratio"] = max(worst["energy_error_bound_ratio"], bound_ratio)
            z = np.column_stack((vh + wh, vh - wh))
            core = np.zeros((2*k, 2*k))
            core[:k, :k], core[k:, k:] = jmat / 4, -jmat / 4
            symtarget = symmetric(vh @ jmat @ wh.T)
            symerror = op(z @ core @ z.T - symtarget) / max(1., op(symtarget))
            assert symerror < 1e-12, (name, symerror)
            worst["symmetric_identity_error"] = max(worst["symmetric_identity_error"], symerror)
            trials += 1
    return dict(cases=len(cases), shifts_per_case=3, node_trials=trials, **worst)


def quadrature_diagnostics(cases):
    rows = []
    for name, n, old, new in cases[-6:]:
        l, lp = laplacian(n, old), laplacian(n, new)
        changes, _, _, a, _ = edits(n, old, new)
        left = spectral_parts(l, kernel_basis(n, old))
        right = spectral_parts(lp, kernel_basis(n, new))
        for alpha in (0.3, 0.5, 0.7):
            epsilon = 2e-4
            rho = epsilon / (100 * (len(changes) + 1))
            beta, c = 1-alpha, math.sin(math.pi*alpha)/math.pi
            smin = (rho*alpha/(4*c))**(1/alpha)
            smax = (4*c/(rho*beta))**(1/beta)
            h = min(.4, math.pi**2 / math.log(100/(rho*alpha*beta)))
            lo, hi = math.floor(math.log(smin)/h), math.ceil(math.log(smax)/h)
            result = np.zeros((n, n))
            # Evaluate t*(R_t-S_t)=L'(L'+tI)^-1-L(L+tI)^-1.
            # This avoids subtracting 1/t-sized common nullspace components
            # at small shifts or two almost identical identities at large t,
            # and diagnoses the quadrature without asserting finite-word
            # stability of the low-rank endpoint factor evaluation.
            _, vl, ql = left
            _, vr, qr = right
            for j in range(lo, hi + 1):
                t = a * math.exp(j*h)
                scaled = (qr * (vr/(vr+t))) @ qr.T - (ql * (vl/(vl+t))) @ ql.T
                result += c*h*t**alpha*scaled
            exact = power_from_parts(right, alpha) - power_from_parts(left, alpha)
            error = op(result-exact)
            normalized = error / (epsilon*op(lp-l)**alpha)
            assert normalized < .15, (name, alpha, normalized)
            rows.append(dict(case=name, alpha=alpha, nodes=hi-lo+1,
                             error_over_requested_bound=normalized))
    return dict(trials=len(rows), largest_error_over_requested_bound=max(
        row["error_over_requested_bound"] for row in rows), rows=rows,
        evaluation="dense spectral exact-node quadrature with explicit nullspace; no sparse backend")


def lanczos_negative(a, w):
    n, q, diagonal, offdiag = len(a), [], [], []
    vector = w.copy()
    for j in range(n):
        q.append(vector)
        aq = a @ vector
        diag = float(vector @ aq)
        diagonal.append(diag)
        residual = aq - diag * vector
        if j:
            residual -= offdiag[-1] * q[-2]
        # Full reorthogonalization makes finite-size cyclic tests robust.
        for _ in range(2):
            for old in q:
                residual -= old * (old @ residual)
        if j < n-1:
            off = -np.linalg.norm(residual)
            assert off < -1e-10, ("unexpected numerical breakdown", j, off)
            offdiag.append(off)
            vector = residual / off
    jmat = np.diag(diagonal) + np.diag(offdiag, 1) + np.diag(offdiag, -1)
    return jmat, np.column_stack(q)


def path_diagnostics():
    rows, max_similarity, max_nullspace, max_update_norm = [], 0., 0., 0.
    for trial in range(12):
        n = 3 + trial % 5
        orthogonal = np.linalg.qr(RNG.normal(size=(n, n)))[0]
        a = (orthogonal * np.geomspace(.15, 6., n)) @ orthogonal.T
        w = RNG.normal(size=n)
        w /= np.linalg.norm(w)
        jmat, q = lanczos_negative(a, w)
        similarity = op(q.T @ a @ q-jmat)
        assert similarity < 2e-12 and np.linalg.norm(q.T@w-np.eye(n)[:, 0]) < 2e-12
        max_similarity = max(max_similarity, similarity)
        d = np.linalg.solve(jmat, np.eye(n)[:, 0])
        assert d.min() > 0
        conductances = -np.diag(jmat, 1)*d[:-1]*d[1:]
        assert conductances.min() > 0
        weights = {(0, 1): float(d[0])}
        weights.update({(i+1, i+2): float(value) for i, value in enumerate(conductances)})
        base_l = laplacian(n+1, weights)
        alpha = (.3, .5, .7)[trial % 3]
        vals, vecs = np.linalg.eigh(jmat)
        target = (vecs*vals**alpha)@vecs.T
        ju = jmat.copy()
        ju[0, 0] += 1
        vals, vecs = np.linalg.eigh(ju)
        target = (vecs*vals**alpha)@vecs.T-target
        ambient_target = np.zeros((n+1, n+1))
        ambient_target[1:, 1:] = target
        errors = []
        for multiplier in (1., 16., 256., 4096.):
            r = max(1., float(d.max()))*multiplier
            mass_sqrt = np.r_[r, d]
            hr = base_l / mass_sqrt[:, None] / mass_sqrt[None, :]
            formula = np.zeros_like(hr)
            formula[1:, 1:] = jmat
            formula[0, 0], formula[0, 1], formula[1, 0] = d[0]/r**2, -1/r, -1/r
            assert op(hr-formula) < 2e-11, (trial, op(hr-formula))
            nullerror = np.linalg.norm(hr@mass_sqrt) / max(1., op(hr)*np.linalg.norm(mass_sqrt))
            max_nullspace = max(max_nullspace, nullerror)
            assert nullerror < 2e-14
            update_vector = np.r_[-d[0]/r, 1., np.zeros(n-1)]
            er = np.outer(update_vector, update_vector)
            updated_weights = dict(weights)
            updated_weights[(0, 1)] += d[0]**2
            from_graph = (laplacian(n+1, updated_weights)-base_l)/mass_sqrt[:, None]/mass_sqrt[None, :]
            assert op(er-from_graph) < 2e-12, trial
            scale = 1/(1+d[0]**2/r**2)
            normerror = abs(op(scale*er)-1.)
            max_update_norm = max(max_update_norm, normerror)
            assert normerror < 2e-14
            kernel = (mass_sqrt/np.linalg.norm(mass_sqrt))[:, None]
            part0 = spectral_parts(scale*hr, kernel)
            part1 = spectral_parts(scale*(hr+er), kernel)
            # Both endpoint operators must be PSD with exactly the graph kernel.
            correction = power_from_parts(part1, alpha)-power_from_parts(part0, alpha)
            errors.append(op(correction-ambient_target))
        assert errors[-1] < errors[0]/100, (trial, errors)
        assert errors[-1] < 2e-3, (trial, errors)
        rows.append(dict(trial=trial, alpha=alpha, dimension=n,
                         error_at_R_multipliers_1_16_256_4096=errors))
    return dict(trials=len(rows), max_similarity_error=max_similarity,
                max_normalized_nullspace_error=max_nullspace,
                max_update_norm_error=max_update_norm, rows=rows)


def main():
    cases = graph_cases()
    summary = dict(seed=SEED, numpy_version=np.__version__,
                   scope="dense numerical diagnostics, not proof, sparse implementation, or stability theorem",
                   identities=identity_diagnostics(cases),
                   quadrature=quadrature_diagnostics(cases),
                   path_realization=path_diagnostics())
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
