import json
from pathlib import Path

import numpy as np

beta = 3**.5 - 2**.5
rng = np.random.default_rng(20261114)
records = []
for n in (3, 4, 8, 16, 32, 64):
    total = 200 if n <= 8 else 40
    inside = 0
    minimum = float('inf')
    records_local = []
    for rep in range(total):
        a = np.zeros((4*n, 3*n), dtype=float)
        block_permutations = []
        for left in range(4):
            for right in range(3):
                p = rng.permutation(n)
                block_permutations.append(p.tolist())
                a[left*n + np.arange(n), right*n + p] = 1
        adj = np.zeros((7*n, 7*n), dtype=float)
        adj[:4*n, 4*n:] = a
        adj[4*n:, :4*n] = a.T
        values = np.linalg.eigvalsh(adj)
        abs_values = np.abs(values)
        positive = abs_values[abs_values > 1e-7]
        positive_inner = positive[positive < beta - 1e-6]
        hit = len(positive_inner) > 0
        inside += int(hit)
        minimum = min(minimum, float(np.min(positive)))
        if hit and not records_local:
            records_local.append({
                'repetition': rep,
                'inner_eigenvalues': positive_inner.tolist(),
                'block_permutations': block_permutations,
                'biadjacency': a.astype(int).tolist(),
                'all_adjacency_eigenvalues': values.tolist(),
            })
    records.append({'N': n, 'samples': total, 'inner_hits': inside,
                    'min_abs_nonzero_eigenvalue': minimum,
                    'max_abs_eigenvalue': float(np.max(np.abs(values))),
                    'inner_edge': beta})
    Path(f'.scratch/spectral-research/two-band/hits-{n}.json').write_text(
        json.dumps(records_local, indent=2) + '\n')
    print(records[-1], flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(records, indent=2) + '\n')
