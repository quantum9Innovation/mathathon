"""Vector diagrams for the elementary matching and random-lift slides.

Run with Python, NumPy, and Matplotlib. This script creates only teaching-*
assets; the earlier illustrations are left unchanged.
"""
from pathlib import Path
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, Rectangle, FancyArrowPatch

OUT = Path(__file__).resolve().parent / "assets"
PREVIEW = Path("/tmp/mathathon-teaching-figures")
OUT.mkdir(exist_ok=True)
PREVIEW.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.family": "serif", "font.size": 13,
    "mathtext.fontset": "cm", "pdf.fonttype": 42,
})
BLUE = "#24558a"
PALE = "#e4edf6"
RED = "#a63b32"
GRAY = "#b3b3b3"


def save(fig, name):
    fig.savefig(OUT / (name + ".pdf"), bbox_inches="tight", pad_inches=.10,
                metadata={"CreationDate": None, "ModDate": None})
    fig.savefig(PREVIEW / (name + ".png"), bbox_inches="tight", pad_inches=.10,
                dpi=150)
    plt.close(fig)


def matching_panel(ax, chosen, title, caption, invalid=False):
    pos = {i: (math.cos(math.pi/2-i*math.pi/3),
               math.sin(math.pi/2-i*math.pi/3)) for i in range(6)}
    all_edges = [(i, (i+1) % 6) for i in range(6)]
    degrees = {i: sum(i in e for e in chosen) for i in range(6)}
    color = RED if invalid else BLUE
    for u, v in all_edges:
        ax.plot([pos[u][0], pos[v][0]], [pos[u][1], pos[v][1]],
                color=GRAY, ls="--", lw=1, zorder=1)
    for u, v in chosen:
        ax.plot([pos[u][0], pos[v][0]], [pos[u][1], pos[v][1]],
                color=color, lw=3.5, zorder=2)
    for i, (x, y) in pos.items():
        face = "#f8dfdb" if degrees[i] > 1 else PALE if degrees[i] else "white"
        ax.add_patch(Circle((x, y), .16, fc=face,
                            ec=RED if degrees[i] > 1 else "black", lw=1.4,
                            zorder=3))
        ax.text(x, y, str(i+1), ha="center", va="center", fontsize=13, zorder=4)
    ax.set_title(title, fontsize=16, pad=14)
    ax.text(0, -1.52, caption, ha="center", va="top", fontsize=12,
            linespacing=1.3)
    ax.set(xlim=(-1.45, 1.45), ylim=(-1.95, 1.35), aspect="equal")
    ax.axis("off")
    return degrees


cases = [
    ([(0, 1), (3, 4)], "A matching", "No shared endpoints.\nVertices 3 and 6 are unmatched.", False,
     "teaching-matching"),
    ([(0, 1), (1, 2)], "Not a matching", "Vertex 2 is used twice.", True,
     "teaching-nonmatching"),
    ([(0, 1), (2, 3), (4, 5)], "A perfect matching", "Every vertex is used exactly once.", False,
     "teaching-perfect"),
]
fig, axes = plt.subplots(1, 3, figsize=(11.8, 3.8))
for ax, (edges, title, caption, invalid, name) in zip(axes, cases):
    deg = matching_panel(ax, edges, title, caption, invalid)
    assert max(deg.values()) == (2 if invalid else 1)
    if name == "teaching-perfect":
        assert all(d == 1 for d in deg.values())
fig.subplots_adjust(wspace=.20)
save(fig, "teaching-matching-examples")
for edges, title, caption, invalid, name in cases:
    fig, ax = plt.subplots(figsize=(3.8, 3.8))
    matching_panel(ax, edges, title, caption, invalid)
    save(fig, name)


# A bipartite perfect matching and its exact permutation matrix.
perm = [1, 2, 0]
assert sorted(perm) == [0, 1, 2]
fig, axes = plt.subplots(1, 3, figsize=(10.4, 3.5),
                         gridspec_kw={"width_ratios": [1.1, .25, 1.0]})
ax = axes[0]
for i, j in enumerate(perm):
    ax.plot([0, 2], [2-i, 2-j], color=BLUE, lw=2.2, zorder=1)
for i in range(3):
    for x in [0, 2]:
        ax.add_patch(Circle((x, 2-i), .09, fc="white", ec="black", lw=1.3, zorder=3))
    ax.text(-.25, 2-i, rf"$a_{i+1}$", ha="right", va="center", fontsize=17)
    ax.text(2.25, 2-i, rf"$b_{i+1}$", ha="left", va="center", fontsize=17)
ax.text(1, 2.65, "One partner for each vertex", ha="center", fontsize=14)
ax.set(xlim=(-.8, 2.8), ylim=(-.45, 2.9), aspect="equal"); ax.axis("off")
axes[1].annotate("", xy=(.85, .52), xytext=(.05, .52),
                 xycoords="axes fraction", arrowprops={"arrowstyle": "->", "lw": 1.6})
axes[1].axis("off")
ax = axes[2]
for i in range(3):
    for j in range(3):
        if perm[i] == j:
            ax.add_patch(Rectangle((j-.34, 2-i-.34), .68, .68,
                                   facecolor=PALE, edgecolor="none"))
        ax.text(j, 2-i, str(int(perm[i] == j)), ha="center", va="center",
                fontsize=21, color=BLUE if perm[i] == j else "black")
    ax.text(-.78, 2-i, rf"$a_{i+1}$", ha="center", va="center", fontsize=16)
    ax.text(i, 2.65, rf"$b_{i+1}$", ha="center", va="center", fontsize=16)
for x, direction in [(-.5, 1), (2.5, -1)]:
    ax.plot([x+.15*direction, x, x, x+.15*direction],
            [2.45, 2.45, -.45, -.45], color="black", lw=1.2)
ax.text(1, -.94, "One 1 in every row and column", ha="center", fontsize=13)
ax.set(xlim=(-1.2, 2.9), ylim=(-1.2, 2.95), aspect="equal"); ax.axis("off")
fig.subplots_adjust(wspace=.12)
save(fig, "teaching-bipartite-perfect")


# The smallest possible lift picture: copy the endpoints of one base edge.
fig, axes = plt.subplots(1, 3, figsize=(10.4, 3.7),
                         gridspec_kw={"width_ratios": [.9, .25, 1.7]})
ax = axes[0]
ax.plot([0, 1.8], [0, 0], color="black", lw=1.8)
for x, label in [(0, "$u$"), (1.8, "$v$")]:
    ax.add_patch(Circle((x, 0), .1, fc="white", ec="black", lw=1.4))
    ax.text(x, -.36, label, ha="center", fontsize=19)
ax.text(.9, .7, "One base edge", ha="center", fontsize=15)
ax.set(xlim=(-.5, 2.3), ylim=(-1.25, 1.6), aspect="equal"); ax.axis("off")
axes[1].annotate("", xy=(.95, .52), xytext=(.05, .52),
                 xycoords="axes fraction", arrowprops={"arrowstyle": "->", "lw": 1.7})
axes[1].axis("off")
ax = axes[2]
for x in [-.64, 2.36]:
    ax.add_patch(Rectangle((x, -.35), 1.05, 2.7, fc="#f8f9fb", ec="#777777", lw=.9))
for i, j in enumerate(perm):
    ax.plot([0, 3], [2-i, 2-j], color=BLUE, lw=2, zorder=2)
for i in range(3):
    for x, label, align in [(0, rf"$u_{i+1}$", "right"),
                             (3, rf"$v_{i+1}$", "left")]:
        ax.add_patch(Circle((x, 2-i), .07, fc="white", ec="black", zorder=3))
        ax.text(x+(-.17 if x == 0 else .17), 2-i, label,
                ha=align, va="center", fontsize=16)
ax.text(-.12, 2.62, "Copies of $u$", ha="center", fontsize=14)
ax.text(2.88, 2.62, "Copies of $v$", ha="center", fontsize=14)
ax.text(1.5, -.76, "Replace the edge by a perfect matching", ha="center", fontsize=13)
ax.set(xlim=(-.92, 3.65), ylim=(-1, 2.95), aspect="equal"); ax.axis("off")
fig.subplots_adjust(wspace=.1)
save(fig, "teaching-elementary-lift")


# A half-edge is a stub attached to a vertex; matching stubs makes full edges.
fig, axes = plt.subplots(1, 3, figsize=(12.0, 3.8),
                         gridspec_kw={"width_ratios": [2.3, .25, 1.2]})
ax = axes[0]
left_nodes = [4.4, 1.1]
right_nodes = [4.95, 2.75, .55]
stub_y = [5.5-i*1.1 for i in range(6)]
stub_perm = [0, 2, 4, 1, 3, 5]
for i, y in enumerate(stub_y):
    ax.plot([0, 1.1], [left_nodes[i//3], y], color="#888888", lw=1.1)
    ax.plot([4.1, 5.2], [y, right_nodes[i//2]], color="#888888", lw=1.1)
for i, j in enumerate(stub_perm):
    ax.plot([1.1, 4.1], [stub_y[i], stub_y[j]], color=BLUE, lw=1.35)
for x in [1.1, 4.1]:
    ax.scatter([x]*6, stub_y, s=32, facecolors="white", edgecolors=BLUE, zorder=4)
for x, ys in [(0, left_nodes), (5.2, right_nodes)]:
    ax.scatter([x]*len(ys), ys, s=130, facecolors=PALE, edgecolors="black", zorder=4)
    for i, y in enumerate(ys):
        ax.text(x+(-.35 if x == 0 else .35), y,
                rf"$u_{i+1}$" if x == 0 else rf"$v_{i+1}$",
                ha="right" if x == 0 else "left", va="center", fontsize=15)
ax.text(2.6, 6.2, "Vertices with attached stubs", ha="center", fontsize=13)
ax.text(2.6, -.7, "Pair the six left stubs with the six right stubs", ha="center", fontsize=12)
ax.set(xlim=(-.9, 6.0), ylim=(-1, 6.6), aspect="equal"); ax.axis("off")
axes[1].annotate("", xy=(.95, .52), xytext=(.05, .52),
                 xycoords="axes fraction", arrowprops={"arrowstyle": "->", "lw": 1.7})
axes[1].axis("off")
ax = axes[2]
left = {0: (0, 1.5), 1: (0, -.5)}
right = {j: (2.4, 2-j*1.5) for j in range(3)}
collapsed = {(i//3, stub_perm[i]//2) for i in range(6)}
assert collapsed == {(i, j) for i in range(2) for j in range(3)}
for i, j in sorted(collapsed):
    ax.plot([left[i][0], right[j][0]], [left[i][1], right[j][1]], color=BLUE, lw=1.5)
for nodes, prefix, offset, align in [(left, "u", -.3, "right"), (right, "v", .3, "left")]:
    for i, (x, y) in nodes.items():
        ax.scatter([x], [y], s=130, facecolors=PALE, edgecolors="black", zorder=3)
        ax.text(x+offset, y, rf"${prefix}_{i+1}$", ha=align, va="center", fontsize=15)
ax.text(1.2, 3.1, "Join the original vertices", ha="center", fontsize=14)
ax.text(1.2, -2, "Left degrees 3; right degrees 2", ha="center", fontsize=12)
ax.set(xlim=(-.9, 3.3), ylim=(-2.5, 3.5), aspect="equal"); ax.axis("off")
fig.subplots_adjust(wspace=.1)
save(fig, "teaching-halfedges")

print("Created seven teaching vector figures; exact matching checks passed.")
