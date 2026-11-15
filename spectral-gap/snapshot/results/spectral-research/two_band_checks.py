import json
from pathlib import Path

import numpy as np


def lift(n, signs):
    size = 7 * n
    a = np.zeros((size, size), dtype=np.int8)
    within = np.arange(n)
    for left in range(4):
        for right in range(4, 7):
            u = left * n + within
            v = right * n + within
            if signs & (1 << (4 * left + right - 4)):
                v = v[::-1]
            a[u, v] = 1
            a[v, u] = 1
    return a


def main():
    beta = 3**.5 - 2**.5
    base_left = np.ones((4, 3), dtype=int)
    singular_values = np.linalg.svd(base_left, compute_uv=False)
    adjacency = np.zeros((7, 7))
    adjacency[:4, 4:] = base_left
    adjacency[4:, :4] = base_left.T
    out = {
        'model': 'K_4,3 with four degree-3 and three degree-4 vertices',
        'base': {
            'degree_sequence': sorted(adjacency.sum(axis=1).tolist()),
            'adjacency_eigenvalues': sorted(np.linalg.eigvalsh(adjacency).tolist()),
            'singular_values_squared': sorted((singular_values**2).tolist()),
        },
        'band_formula': {
            'a': 2,
            'b': 3,
            'sqrt_ab': 6**.5,
            'inner_edge': beta,
            'outer_edge': 3**.5 + 2**.5,
        },
        'two_lifts': [],
    }
    assert np.allclose(adjacency.sum(axis=1), [3, 3, 3, 3, 4, 4, 4])
    assert np.allclose(sorted(singular_values**2), [0, 0, 12])
    assert np.linalg.matrix_rank(base_left) == 1
    expected_base = sorted([12**.5, -12**.5] + [0] * 5)
    assert np.allclose(sorted(np.linalg.eigvalsh(adjacency)), expected_base)

    for mask in range(1 << 12):
        values = np.linalg.eigvalsh(lift(2, mask))
        inner = values[(values > 1e-7) & (values < beta - 1e-7)]
        if len(inner):
            out['two_lifts'].append({
                'mask': mask,
                'inner_eigenvalues': inner.tolist(),
                'all_eigenvalues': values.tolist(),
            })
    print(json.dumps({k: v for k, v in out.items() if k != 'two_lifts'}, indent=2))
    print('Two-lifts with a positive eigenvalue strictly below the inner edge:',
          len(out['two_lifts']), 'of 4096 signed covers')
    if out['two_lifts']:
        print('First mask:', out['two_lifts'][0]['mask'])
        print('First inner eigenvalues:', out['two_lifts'][0]['inner_eigenvalues'])
    Path(__file__).with_suffix('.json').write_text(json.dumps(out, indent=2) + '\n')


if __name__ == '__main__':
    main()
