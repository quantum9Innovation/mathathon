"""Evaluate the two proved resonance laws, without simulating graphs."""
from pathlib import Path
from hashlib import sha256
import json
import math
import os
import tempfile

os.environ.setdefault('MPLCONFIGDIR', tempfile.mkdtemp(prefix='spectral-resonance-plot-'))
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / 'root/graph-resonance-v2.md'
EXPECTED = '907d90af7ea1af8a59ec49c100869046e01e3ffd251e81a55239a054bb59f289'
assert sha256(PROOF.read_bytes()).hexdigest() == EXPECTED
KAPPA = 3 / math.sqrt(8)


def positive(tau, pairs=1):
    gap = math.sqrt(tau * tau + 4 * KAPPA * KAPPA * pairs)
    return (tau + gap) / 2, (tau - gap) / 2


def negative(a):
    return -KAPPA * KAPPA / 2, -(a + KAPPA * KAPPA)


checks = 0
for pairs in (1, 2, 5):
    for tau in np.linspace(-5 * KAPPA, 5 * KAPPA, 101):
        high, low = positive(float(tau), pairs)
        assert math.isclose(high + low, tau, abs_tol=1e-12)
        assert math.isclose(high * low, -KAPPA * KAPPA * pairs, abs_tol=1e-11)
        direct = np.linalg.eigvalsh([[0, KAPPA * math.sqrt(pairs)],
                                    [KAPPA * math.sqrt(pairs), tau]])
        assert np.allclose(direct, [low, high], rtol=1e-12, atol=1e-12)
        checks += 1
assert math.isclose(negative(-KAPPA * KAPPA / 2)[0],
                    negative(-KAPPA * KAPPA / 2)[1])
assert negative(0)[0] > negative(0)[1]
assert negative(-KAPPA * KAPPA)[0] < negative(-KAPPA * KAPPA)[1]

plt.rcParams.update({'font.size': 11, 'axes.titlesize': 13,
                     'axes.spines.top': False, 'axes.spines.right': False})
fig, axes = plt.subplots(1, 2, figsize=(12, 4.8), layout='constrained')
blue, orange, grey = '#1864ab', '#d46b08', '#58616b'
x = np.linspace(-3.5, 3.5, 401)
values = np.array([positive(float(t * KAPPA)) for t in x]) / KAPPA
axes[0].plot(x, values[:, 0], color=blue, lw=2.5, label='Upper mixed mode')
axes[0].plot(x, values[:, 1], color=orange, lw=2.5, label='Lower mixed mode')
axes[0].axvline(0, color=grey, lw=1, ls=':')
axes[0].scatter([0, 0], [1, -1], color=[blue, orange], zorder=4)
axes[0].annotate('Exact leading resonance\nConstant host direction: mass 1/4 each',
                 xy=(0, 1), xytext=(-3.2, 2.9), fontsize=10,
                 arrowprops={'arrowstyle': '->', 'color': grey})
axes[0].set_title('Positive side: avoided crossing, one pair')
axes[0].set_xlabel(r'Detuning $\tau/\kappa$, with $\tau=\sqrt{m}(w-\kappa)$')
axes[0].set_ylabel(r'Shift $\sqrt{n}(\mu-3-\kappa s)/\kappa$')
axes[0].legend(loc='lower right', frameon=False, fontsize=10)
axes[0].grid(alpha=.15)

z = np.linspace(-1.5, .8, 301)
axes[1].plot(z, np.full_like(z, -.5), color=blue, lw=2.5, label='Collective mode')
axes[1].plot(z, -z - 1, color=orange, lw=2.5, label='Pair subspace')
axes[1].axvline(0, color=grey, lw=1, ls=':')
axes[1].scatter([0, 0], [-.5, -1], color=[blue, orange], zorder=4)
axes[1].scatter([-.5], [-.5], facecolors='white', edgecolors=grey,
                s=70, linewidths=1.5, zorder=5)
axes[1].annotate('Retuned crossing\nFiner basis remains open',
                 xy=(-.5, -.5), xytext=(-1.4, -1.5), fontsize=10,
                 arrowprops={'arrowstyle': '->', 'color': grey})
axes[1].annotate('Exact phase\nseparates the modes',
                 xy=(0, -.75), xytext=(.15, .2), fontsize=10,
                 arrowprops={'arrowstyle': '->', 'color': grey})
axes[1].set_title('Negative side: logarithmic splitting')
axes[1].set_xlabel(r'Detuning $a/\kappa^2$, with $a=(w-\kappa)/(sr)$')
axes[1].set_ylabel(r'Shift $(\mu-3+\kappa s)/(\kappa^2s^2r)$')
axes[1].legend(loc='lower right', frameon=True, facecolor='white',
               edgecolor='white', framealpha=.95, fontsize=10)
axes[1].grid(alpha=.15)
fig.suptitle('Two distinct scales at collective-pair resonance', fontsize=16)
out = ROOT / 'figures'
out.mkdir(exist_ok=True)
fig.savefig(out / 'two-resonance-scales.png', dpi=180)
fig.savefig(out / 'two-resonance-scales.svg')
plt.close(fig)
(out / 'two-resonance-scales-data.json').write_text(json.dumps({
    'proof_sha256': EXPECTED,
    'scope': 'Evaluation of limiting formulas, not finite-graph simulation.',
    'positive_pairs': 1,
    'positive_formula_checks': checks,
    'negative_crossing_and_order_checks': 3,
    'positive_parameter': 'tau = sqrt(m) * (w-kappa)',
    'negative_parameter': 'a = (w-kappa)/(s*r)',
    'positive_physical_scale': 'n^(-1/2)',
    'negative_physical_scale': 's^2*r',
    'retuned_negative_basis': 'unresolved at a=-kappa^2/2'
}, indent=2) + '\n')
print(f'{checks} positive formula checks and 3 negative checks passed')
