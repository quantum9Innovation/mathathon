"""Draw the proved relative-rank dichotomy; this is a schematic, not data."""
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "spectral-gap" / "figures"
DEST.mkdir(exist_ok=True)
fig, axes = plt.subplots(2, 1, figsize=(10, 7), gridspec_kw={"height_ratios": [1, 2.1]})
ink, accent, quiet = "#18354b", "#cf582d", "#667983"
for ax in axes:
    ax.set_aspect("equal")
    ax.axis("off")


def edge(ax, p, q, edited=False):
    ax.plot([p[0], q[0]], [p[1], q[1]], color=accent if edited else ink,
            lw=3.4 if edited else 1.6, zorder=1)


def vertex(ax, p):
    ax.plot(*p, "o", color="white", mec=ink, mew=1.4, ms=6, zorder=3)


ax = axes[0]
points = [(x, 0) for x in range(9)]
for i in range(8):
    edge(ax, points[i], points[i + 1], edited=i == 3)
for p in points:
    vertex(ax, p)
ax.text(3.5, 0.28, "one edge doubled", ha="center", color=accent, fontsize=11)
ax.text(0, 0.85, "Paths and cycles: maximum degree 2", fontsize=13, weight="bold", color=ink)
ax.text(8, -0.62, r"Worst relative rank: $\Theta_\alpha(\log^2(1/\varepsilon))$",
        ha="right", fontsize=13, color=ink)
ax.set_xlim(-0.6, 8.5)
ax.set_ylim(-0.8, 1.2)

ax = axes[1]
root, left, right = (2.5, 0), (4, 0.85), (4, -0.85)
leaves = [(5.3, 1.3), (5.3, 0.42), (5.3, -0.42), (5.3, -1.3)]
anchor_center, anchor_port = (0.6, 0), (1.02, 0)
edge(ax, anchor_port, root, edited=True)
edge(ax, root, left)
edge(ax, root, right)
for parent, pair in ((left, leaves[:2]), (right, leaves[2:])):
    for leaf in pair:
        edge(ax, parent, leaf)
for i, leaf in enumerate(leaves):
    port = (7.55, leaf[1])
    edge(ax, leaf, (6.14, leaf[1]))
    edge(ax, (6.65, leaf[1]), port)
    ax.text(6.39, leaf[1], "⋯", va="center", ha="center", color=ink, fontsize=17)
    ax.add_patch(Circle((7.97, leaf[1]), 0.42, ec=ink, fc="#edf3f5", lw=1.6))
    vertex(ax, port)
    ax.text(7.97, leaf[1], rf"$M_{i+1}$", ha="center", va="center", fontsize=12, color=ink)
ax.add_patch(Circle(anchor_center, 0.42, ec=ink, fc="#edf3f5", lw=1.6))
ax.text(*anchor_center, r"$M_0$", ha="center", va="center", fontsize=12, color=ink)
for p in [root, left, right, *leaves, anchor_port]:
    vertex(ax, p)
ax.text(1.7, 0.28, "doubled bridge", ha="center", fontsize=10, color=accent)
ax.text(6.4, 1.95, "long unit-edge necks", ha="center", fontsize=10, color=quiet)
ax.text(0, 2.55, "Branching and expander reservoirs: maximum degree 3",
        fontsize=13, weight="bold", color=ink)
ax.text(8.5, -2, r"Worst relative rank: $\Theta_\alpha(1/\varepsilon)$",
        ha="right", fontsize=13, color=ink)
ax.text(0, -2.65, "Circles stand for bipartite expander reservoirs of maximum degree 3, each with one port.\n"
        r"Choose sizes $M_0\gg M_1\gg\cdots\gg M_4$; the drawing suppresses internal vertices.",
        fontsize=10, color=quiet, linespacing=1.6)
ax.set_xlim(-0.6, 8.7)
ax.set_ylim(-2.95, 2.9)
fig.suptitle("A single edge edit has different spectral complexity at degrees 2 and 3",
             fontsize=14, color=ink, y=0.98)
fig.text(0.5, 0.02, r"Fixed $0<\alpha<1$; error is measured relative to $L^\alpha$. "
         "These are worst-case orders over all finite host sizes.",
         ha="center", fontsize=10, color=quiet)
fig.subplots_adjust(top=0.90, bottom=0.08, hspace=0.05)
for extension in ("pdf", "png"):
    path = DEST / f"relative-rank-degree-transition.{extension}"
    fig.savefig(path, dpi=180, bbox_inches="tight", facecolor="white")
    print(path)
