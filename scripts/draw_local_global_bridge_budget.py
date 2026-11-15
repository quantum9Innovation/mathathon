"""Plot the exact analytic degree-dependent budget split; no sampled data."""

from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


root = Path(__file__).resolve().parents[1]
destination = root / "spectral-gap/figures"
destination.mkdir(exist_ok=True)
degree = np.arange(3, 17)
local = np.log1p(2 / degree)
global_budget = np.log(2 * degree / (degree + 2))
assert np.max(np.abs(local + global_budget - np.log(2))) < 1e-14

ink, blue, orange = "#18354b", "#5788a6", "#d46c36"
fig, (ax, detail) = plt.subplots(1, 2, figsize=(11, 4.6),
                                gridspec_kw={"width_ratios": [1.55, 1]})
ax.stackplot(degree, local, global_budget, colors=[blue, orange], alpha=0.86,
             labels=[r"Minimum local cost: $\log(1+2/d)$",
                     r"Sharp limiting global budget: $\log(2d/(d+2))$"])
ax.plot(degree, local, "o-", color=ink, ms=3, lw=1)
ax.axhline(np.log(2), color=ink, ls="--", lw=1)
ax.text(16.15, np.log(2), r"$\log 2$", va="center", color=ink)
ax.set_xlim(3, 17.3)
ax.set_ylim(0, 0.77)
ax.set_xticks([3, 4, 6, 8, 10, 12, 14, 16])
ax.set_xlabel("Maximum combinatorial degree $d$")
ax.set_ylabel(r"Logarithmic budget divided by $\alpha$")
ax.spines[["top", "right"]].set_visible(False)
ax.legend(loc="lower right", bbox_to_anchor=(1.02, -0.42), frameon=False,
          fontsize=10)

detail.axis("off")
detail.text(0, 0.94, "Cubic hosts: the exact split", color=ink,
            fontsize=13, weight="bold", transform=detail.transAxes)
detail.barh([0.69], [np.log(5 / 3)], height=0.12, color=blue)
detail.barh([0.69], [np.log(6 / 5)], left=[np.log(5 / 3)], height=0.12,
            color=orange)
detail.set_xlim(0, 0.74)
detail.set_ylim(0, 1)
detail.text(np.log(5 / 3) / 2, 0.69, r"$\log(5/3)$", ha="center",
            va="center", color="white", fontsize=12)
detail.text(np.log(5 / 3) + np.log(6 / 5) / 2, 0.69, r"$\log(6/5)$",
            ha="center", va="center", color="white", fontsize=10)
detail.text(0, 0.50,
            r"$W_{3,\alpha}(\varepsilon)\sim"
            r"\dfrac{\alpha\log(6/5)}{\varepsilon}$",
            fontsize=16, color=ink)
detail.text(0, 0.08,
            "The local tree response consumes the blue part.\n"
            "Shared reservoirs approach the orange budget\n"
            "using arbitrarily many nearly equal modes.",
            fontsize=10, color=ink, linespacing=1.5)

fig.suptitle("One doubled bridge: local response limits global compression rank",
             fontsize=14, color=ink, y=0.99)
fig.text(0.5, 0.015,
         r"Fixed $0<\alpha<1$. Curves show exact formulas, not numerical experiments. "
         "Matching lower examples may be simple and bipartite.",
         ha="center", fontsize=9, color=ink)
fig.subplots_adjust(left=0.075, right=0.98, top=0.86, bottom=0.31, wspace=0.23)
for extension in ("pdf", "png"):
    path = destination / f"local-global-bridge-budget.{extension}"
    fig.savefig(path, dpi=180, bbox_inches="tight", facecolor="white")
    print(path)
