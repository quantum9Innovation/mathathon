#!/usr/bin/env python3
"""Plot the proved asymptotic coefficient, not sampled singular values."""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def normalized_coefficient(alpha, tau):
    tau = np.asarray(tau)
    return np.where(
        tau <= 1,
        1 - alpha * tau**2,
        np.maximum(1 - alpha * tau, 0) ** 2 / (1 - alpha),
    )


def main():
    destination = Path(__file__).resolve().parents[1] / "matmul"
    plt.rcParams.update({"font.size": 12, "axes.spines.top": False,
                         "axes.spines.right": False})
    fig, ax = plt.subplots(figsize=(9, 5.8))
    tau = np.linspace(0, 4.2, 1600)
    for alpha, color in [(0.25, "#3569a8"), (0.5, "#d17a22"),
                         (0.75, "#31836b")]:
        values = normalized_coefficient(alpha, tau)
        ax.plot(tau, values, color=color, linewidth=2.5,
                label=rf"$\alpha={alpha:g}$, cutoff $\tau={1/alpha:g}$")
        ax.scatter([1, 1/alpha], [1-alpha, 0], color=color, s=28, zorder=4)
        assert np.isclose(normalized_coefficient(alpha, 0), 1)
        assert np.isclose(normalized_coefficient(alpha, 1), 1-alpha)
        assert normalized_coefficient(alpha, 1/alpha) == 0
        assert np.all(values >= 0)
    ax.axvline(1, color="#888888", linestyle="--", linewidth=1)
    ax.text(1.05, 0.92, r"First transition: $\tau=1$", color="#555555")
    ax.set(xlim=(0, 4.2), ylim=(-0.035, 1.035),
           xlabel=r"Boundary rate $\tau$ in $h=\varepsilon^\tau$",
           ylabel=r"Sharp coefficient $C_\alpha(\tau)/C_\alpha(0)$",
           title="The joint boundary law for fractional compression")
    ax.grid(axis="y", color="#dddddd", linewidth=0.7)
    ax.legend(loc="upper right", frameon=False)
    fig.subplots_adjust(left=0.12, bottom=0.25, right=0.97, top=0.90)
    fig.text(0.12, 0.105,
             r"Worst-case strict count: $C_\alpha(\tau)\log^2(1/\varepsilon)"
             r"+o(\log^2(1/\varepsilon))$.", fontsize=11)
    fig.text(0.12, 0.055,
             r"For $\tau\geq1/\alpha$, the supremal strict count is exactly one.",
             fontsize=11)
    fig.savefig(destination / "fractional-boundary-crossover.png", dpi=180)
    fig.savefig(destination / "fractional-boundary-crossover.pdf")
    plt.close(fig)


if __name__ == "__main__":
    main()
