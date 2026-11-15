"""Finite checks of phase conversion; proofs are in phase-rounding.tex.

Run with Python 3 and numpy. Only writes phase-rounding-checks.json beside
this script. Random search checks matrix identities, not the existence proof.
"""
from functools import lru_cache
import json
import math
from pathlib import Path
import numpy as np


def matching_polynomial(n, edges):
    neighbors = [0] * n
    for u, v in edges:
        neighbors[u] |= 1 << v
        neighbors[v] |= 1 << u

    @lru_cache(None)
    def counts(mask):
        if not mask:
            return (1,)
        bit = mask & -mask
        u = bit.bit_length() - 1
        rest = mask ^ bit
        ans = list(counts(rest))
        available = neighbors[u] & rest
        while available:
            vbit = available & -available
            available ^= vbit
            sub = counts(rest ^ vbit)
            while len(ans) < len(sub) + 1:
                ans.append(0)
            for k, value in enumerate(sub):
                ans[k + 1] += value
        return tuple(ans)

    coeff = [0] * (n + 1)
    for k, value in enumerate(counts((1 << n) - 1)):
        coeff[2 * k] = (-1) ** k * value
    return coeff


def matrix_check(L, copies, rng, samples):
    # Complete bipartite connections between consecutive cycle fibers.
    n = L * copies
    color = np.repeat(np.arange(L), copies)
    edges = sorted({tuple(sorted((i * copies + u,
                                ((i + 1) % L) * copies + v)))
                    for i in range(L)
                    for u in range(copies) for v in range(copies)})
    mu = matching_polynomial(n, edges)
    roots = np.roots(mu)
    assert np.max(np.abs(roots.imag)) < 1e-6
    r_mu = float(np.max(roots.real))
    c = math.cos(math.pi / (2 * L))
    gauge = np.exp(1j * math.pi * (L - 1) / (2 * L) * color)
    best = None
    max_identity_error = 0.0
    for sample in range(samples):
        signs = (rng.integers(0, 2, len(edges)) * 2 - 1)
        H = np.zeros((n, n), dtype=complex)
        for (u, v), s in zip(edges, signs):
            H[u, v], H[v, u] = 1j * s, -1j * s
        K = gauge.conj()[:, None] * H * gauge[None, :]
        rounded = K.real / c
        assert np.max(np.abs(rounded - np.rint(rounded))) < 1e-12
        assert np.max(np.abs(rounded - rounded.T)) < 1e-12
        err = float(np.max(np.abs(c * np.rint(rounded) - K.real)))
        max_identity_error = max(max_identity_error, err)
        hnorm = float(np.max(np.abs(np.linalg.eigvalsh(H))))
        anorm = float(np.max(np.abs(np.linalg.eigvalsh(rounded))))
        assert anorm * c <= hnorm + 1e-10
        if best is None or hnorm < best[0]:
            best = (hnorm, anorm)
    assert best[0] <= r_mu + 1e-7
    return dict(L=L, copies=copies, vertices=n, edges=len(edges),
                matching_polynomial=mu, matching_root=r_mu,
                conversion_factor=1/c, best_orientation_norm=best[0],
                converted_signing_norm=best[1], theorem_bound=r_mu/c,
                samples=samples, max_identity_error=max_identity_error)


def main():
    rng = np.random.default_rng(20261115)
    results = [matrix_check(L, 1, rng, 250) for L in (3, 5, 7, 9)]
    results += [matrix_check(L, 2, rng, 2000) for L in (3, 5, 7)]
    for result in results[:4]:
        assert abs(result["theorem_bound"] - 2) < 1e-8
        assert abs(result["converted_signing_norm"] - 2) < 1e-8
    output = dict(status="passed", seed=20261115, results=results,
                  scope="Numerical matrix identity checks; not a proof of general existence.")
    Path(__file__).with_name("phase-rounding-checks.json").write_text(
        json.dumps(output, indent=2) + "\n")
    print(json.dumps(dict(status="passed", graphs=len(results),
                          total_samples=sum(r["samples"] for r in results))))


if __name__ == "__main__":
    main()
