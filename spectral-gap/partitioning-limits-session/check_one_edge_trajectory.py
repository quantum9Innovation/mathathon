#!/usr/bin/env python3
"""High-precision diagnostics for one-edge-trajectory.tex, not a proof.

Run with mpmath installed. Tiny prescribed eigengaps are intentional;
ordinary binary64 eigensolvers cannot resolve this construction.
"""
import json
from pathlib import Path

import mpmath as mp


def outer(x, y):
    return x * y.T


def maxabs(a):
    return max(abs(x) for x in a)


def check(k, n, eta):
    mp.mp.dps = max(120, 30 + 10 * k)
    eta = mp.mpf(eta)
    c = mp.mpf(1) / (10 * k)
    ratio = (eta / 100) ** 2
    d1 = eta ** 2 * c / (10 ** 6 * n)
    ds = [d1 * ratio ** j for j in range(k)]
    # u=0 and v=1, so even Walsh masks have equal endpoint values.
    qs = [mp.matrix([(-1) ** ((x & (2 * j)).bit_count()) / mp.sqrt(n)
                     for x in range(n)]) for j in range(1, k + 1)]
    e0 = mp.matrix(n, 1)
    e0[0], e0[1] = 1 / mp.sqrt(2), -1 / mp.sqrt(2)
    b = mp.sqrt(2) * e0
    beta_j = [mp.sqrt(c * d / 2) for d in ds]
    beta = mp.sqrt(sum(x * x for x in beta_j))
    z = sum((beta_j[j] * qs[j] / beta for j in range(k)), mp.matrix(n, 1))
    gamma = mp.sqrt(1 - beta ** 2)
    v0 = gamma * e0 - beta * z
    vs = [qs[j] + (gamma - 1) * beta_j[j] / beta * z + beta_j[j] * e0
          for j in range(k)]
    vertices = [v0] + vs
    gram = mp.matrix([[mp.fdot(x, y) for y in vertices] for x in vertices])
    assert maxabs(gram - mp.eye(k + 1)) < mp.mpf('1e-90')
    P = mp.eye(n) - mp.ones(n) / n
    M = P - 2 * outer(v0, v0)
    for d, v in zip(ds, vs):
        M += (d - 1) * outer(v, v)
    K = 2 * n
    A = K * P + M
    weights = [-A[i, j] for i in range(n) for j in range(i)]
    assert min(weights) >= 1 and max(weights) <= 3
    assert maxabs(A * mp.ones(n, 1)) < mp.mpf('1e-85')
    w_e = -A[0, 1]
    couplings = [mp.fdot(b, v) for v in vertices]
    small_A = mp.diag([K - 1] + [K + d for d in ds])
    b_small = mp.matrix(couplings)
    samples = []
    previous_t = mp.mpf(0)
    f_vectors = []
    for j, dj in enumerate(ds):
        mu = K - dj
        denom = [-1 + dj] + [d + dj for d in ds]
        coeff = [bj / den for bj, den in zip(couplings, denom)]
        m = mp.fdot(couplings, coeff)
        t = -1 / m
        y = sum((a * v for a, v in zip(coeff, vertices)), mp.matrix(n, 1))
        dominant = mp.sqrt(c) / (2 * mp.sqrt(dj))
        flat_error = mp.sqrt(n) * maxabs(y / dominant - qs[j])
        f = y / mp.norm(y)
        residual = mp.norm((A + t * outer(b, b)) * f - mu * f)
        # Independent diagonalization of the active (k+1)-dimensional block.
        eig = mp.eigsy(small_A + t * outer(b_small, b_small), eigvals_only=True)
        eig_error = abs(eig[0] - mu)
        gap = eig[1] - eig[0]
        assert previous_t < t < w_e
        assert m < -1
        assert flat_error < eta
        assert all(mp.sign(x) == mp.sign(q) for x, q in zip(f, qs[j]))
        assert mp.norm(f - qs[j]) < 2 * eta
        assert residual < mp.mpf('1e-65')
        assert eig_error < mp.mpf('1e-65')
        assert gap > 0
        previous_t = t
        f_vectors.append(f)
        samples.append({
            'j': j + 1, 't': float(t),
            'sqrt_n_scaled_flat_error': float(flat_error),
            'unit_vector_distance_to_cut': float(mp.norm(f - qs[j])),
            'sqrt_n_min_coordinate': float(mp.sqrt(n) * min(abs(x) for x in f)),
            'eigen_residual': mp.nstr(residual, 6),
            'smallest_eigenvalue_gap': mp.nstr(gap, 8),
        })
    sign_gram = mp.matrix([[mp.fdot(x, y) for y in qs] for x in qs])
    assert maxabs(sign_gram - mp.eye(k)) < mp.mpf('1e-90')
    tau = w_e * sum(bj * bj / aa for bj, aa in
                    zip(couplings, [K - 1] + [K + d for d in ds]))
    assert tau <= mp.mpf(6) / (2 * n - 1)
    return {
        'k': k, 'n': n, 'eta': float(eta), 'precision_digits': mp.mp.dps,
        'minimum_weight': float(min(weights)), 'maximum_weight': float(max(weights)),
        'edited_edge_baseline_weight': float(w_e),
        'exact_relative_norm_at_full_doubling': float(tau),
        'uniform_relative_bound': float(mp.mpf(6) / (2 * n - 1)),
        'orthogonal_sign_cuts': True, 'samples': samples, 'status': 'PASS',
    }


if __name__ == '__main__':
    rows = [check(k, n, '.05') for k, n in [(1, 4), (3, 8), (7, 16), (15, 32)]]
    result = {'purpose': 'Numerical corroboration only; see written theorem.',
              'status': 'PASS', 'cases': rows}
    dest = Path(__file__).with_name('one-edge-trajectory-checks.json')
    dest.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'cases': len(rows),
                      'selected_fiedler_cuts': sum(row['k'] for row in rows)}))
