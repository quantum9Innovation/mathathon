"""Search finite cores completed by independent infinite d-regular branches.

Every missing degree slot receives one edge into a (d-1)-ary tree.  Its
conductance to infinity is (d-2)/(d-1).  Free resistance equals core
resistance.  Wired resistance is computed by eliminating the tree branches.
Numerical searches are diagnostics, not proofs.
"""
import argparse
import json
import random

import numpy as np


def examine(n, edges, d):
    L = np.zeros((n, n))
    for u, v in edges:
        L[u, u] += 1
        L[v, v] += 1
        L[u, v] -= 1
        L[v, u] -= 1
    deg = L.diagonal().copy()
    if np.any(deg > d) or np.all(deg == d):
        return None
    vals, vecs = np.linalg.eigh(L)
    if vals[1] < 1e-8:
        return None
    Linv = (vecs[:, 1:] / vals[1:]) @ vecs[:, 1:].T
    M = L + np.diag((d - deg) * (d - 2) / (d - 1))
    Minv = np.linalg.inv(M)
    best = None
    for u, v in edges:
        rf = Linv[u, u] + Linv[v, v] - 2 * Linv[u, v]
        rw = Minv[u, u] + Minv[v, v] - 2 * Minv[u, v]
        item = dict(d=d, n=n, edges=edges, edge=[u, v], rf=float(rf),
                    rw=float(rw), strong_margin=float(rw - 2 * rf / d),
                    envelope_margin=float(rw-rf/(1+(d-2)*rf/2)),
                    ratio=float((1 + rf) / (1 + rw)))
        if best is None or item['envelope_margin'] < best['envelope_margin']:
            best = item
    return best


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--samples', type=int, default=10000)
    parser.add_argument('--seed', type=int, default=230611)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    records = []
    for d in [3, 4, 5, 6]:
        best = None
        for trial in range(args.samples):
            n = rng.randrange(2, 31)
            # A random tree, rejecting degree overflow; then add core cycles.
            edges = []
            deg = [0] * n
            for v in range(1, n):
                available = [u for u in range(v) if deg[u] < d]
                u = rng.choice(available)
                edges.append((u, v))
                deg[u] += 1
                deg[v] += 1
            candidates = [(u, v) for u in range(n) for v in range(u+1, n)
                          if (u, v) not in edges]
            rng.shuffle(candidates)
            prob = rng.random()
            for u, v in candidates:
                if deg[u] < d and deg[v] < d and rng.random() < prob:
                    edges.append((u, v))
                    deg[u] += 1
                    deg[v] += 1
            item = examine(n, edges, d)
            if item is None:
                continue
            if best is None or item['envelope_margin'] < best['envelope_margin']:
                best = item
            if item['envelope_margin'] < -1e-8:
                print(json.dumps({'counterexample': item}), flush=True)
                return
        records.append(best)
        print(json.dumps({'degree_result': best}), flush=True)
    print(json.dumps({'seed': args.seed, 'samples_per_degree': args.samples,
                      'results': records}))


if __name__ == '__main__':
    main()
