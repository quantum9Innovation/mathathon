"""Plot the explicit limiting cubic law, without sampling finite graphs."""
from pathlib import Path
import hashlib
import json
import math
import os

os.environ.setdefault('MPLCONFIGDIR', '/tmp/spectral-critical-matplotlib')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'figures'
OUT.mkdir(exist_ok=True)
KAPPA = 3 / math.sqrt(8)
H = 3 / 4
C = 1.0
PHASES = [0.0, 0.25, 0.5, 0.75]


def cdf(x, phase):
    if x < KAPPA:
        return 0.0
    threshold = phase + math.log2(H / x)
    nearest = round(threshold)
    if abs(threshold - nearest) < 1e-12:
        threshold = nearest
    largest = math.ceil(threshold) - 1
    intensity = 1.5 * C ** 1.5 * 2 ** (largest - phase)
    return math.exp(-intensity)


fig, ax = plt.subplots(figsize=(10, 5.8), constrained_layout=True)
colors = ['#1768AC', '#DA7C30', '#3A9278', '#8B5FBF']
rows = []
for phase, color in zip(PHASES, colors):
    levels = [H * 2 ** (phase-k) for k in range(-8, 12)]
    nodes = sorted(set([0.6, KAPPA, 8.5] + [x for x in levels if KAPPA < x < 8.5]))
    values = [cdf(x, phase) for x in nodes]
    ax.step(nodes, values, where='post', color=color, linewidth=2.2,
            label=rf'$\phi={phase:g}$')
    for idx in range(1, len(nodes)-1):
        if values[idx] > values[idx-1]:
            ax.plot(nodes[idx], values[idx], 'o', color=color, markersize=4)
    for x, value in zip(nodes, values):
        rows.append({'phase':phase,'x':x,'cdf_right':value})
    for x in [KAPPA, *[z for z in levels if z >= KAPPA], 1.37, 2.41, 5.93]:
        independent_sum = sum(0.75 * C ** 1.5 * 2 ** (k-phase)
                              for k in range(-150, 151)
                              if H * 2 ** (phase-k) > x * (1+1e-13))
        assert abs(cdf(x, phase)-math.exp(-independent_sum)) < 1e-11
        assert abs(cdf(2*x, phase)-cdf(x, phase)**0.5) < 1e-11
    assert all(a <= b for a, b in zip(values, values[1:]))
ax.axvline(KAPPA, color='#555555', linestyle=':', linewidth=1.3, zorder=0)
ax.text(KAPPA+0.12, 0.08, r'Collective floor $3/\sqrt{8}$', color='#444444', fontsize=11)
ax.set_xlim(0.6, 8.5)
ax.set_ylim(-0.015, 1.015)
ax.set_xlabel(r'Normalized top displacement $x$', fontsize=12)
ax.set_ylabel(r'Limiting probability $\mathbb{P}(X_\phi\leq x)$', fontsize=12)
ax.set_title('Different distance phases give different critical laws\n' +
             r'Cubic host, $m/n^{1/3}\ \longrightarrow\ 1$', fontsize=15, pad=14)
ax.grid(axis='y', alpha=0.2)
ax.legend(title='Distance phase', loc='lower right', frameon=False)
ax.spines[['top','right']].set_visible(False)
fig.savefig(OUT/'critical-cdf.png', dpi=180)
fig.savefig(OUT/'critical-cdf.svg')
plt.close(fig)
proof = ROOT/'root/critical-law-v1.md'
record={'model':'cubic, critical coefficient c=1, explicit subsequential limiting CDF',
        'source_proof_sha256':hashlib.sha256(proof.read_bytes()).hexdigest(),
        'phases':PHASES,'collective_floor':KAPPA,'pair_coefficient':H,
        'finite_graph_simulation':False,
        'numerical_checks':'Right-endpoint geometric sum agreement, monotonicity and discrete scaling passed',
        'rows':rows}
(OUT/'critical-cdf-data.json').write_text(json.dumps(record,indent=2)+'\n')
print('Saved two figure formats and the exact-formula plotting data')
