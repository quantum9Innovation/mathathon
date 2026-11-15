"""Build manuscript figures from the positive normalized recurrence."""

import json
import os
from pathlib import Path

os.environ.setdefault("MPLCONFIGDIR", "/tmp/spectral-manuscript-mpl")
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parent
mp.mp.dps = 60
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                     "axes.spines.top": False, "axes.spines.right": False})
BLUE = "#176b8a"
ORANGE = "#bb5b28"
INK = "#26394b"


def ratios(n, maximum):
    even = mp.mpf(1)
    odd = mp.mpf(1)
    values = {}
    for m in range(1, maximum // 2 + 1):
        even = (n * even + mp.mpf(4) * (2*m-1) * (2*m-2) * odd / 3) / (n-2*m+1)
        odd = (3*n*even + (2*m-2)*n*odd) / ((n-2*m)*(2*m+1))
        values[2*m] = even
        values[2*m+1] = odd
    return values


def hyperbolic(n, k):
    k_even = 2 * (k // 2)
    lam = mp.mpf(2)/3 * mp.sqrt(mp.mpf(k_even)**3/n)
    return mp.cosh(lam) if k % 2 == 0 else mp.sinh(lam)/lam


data = {"arithmetic": "60-digit recurrence evaluation, not a formal certificate"}
fig, axes = plt.subplots(1, 2, figsize=(10.2, 3.65))
c = np.linspace(0, 9, 200)
z = (2/3)*np.sqrt(c)
axes[0].plot(c, np.cosh(z), color=BLUE, label="Even limit")
odd_limit = np.ones_like(z)
odd_limit[1:] = np.sinh(z[1:])/z[1:]
axes[0].plot(c, odd_limit, color=ORANGE, label="Odd limit")
rv = ratios(10000, 46)
critical = []
for parity, marker, color in [(0, "o", BLUE), (1, "s", ORANGE)]:
    orders = [k for k in sorted(rv) if k % 2 == parity and k**3/10000 <= 9]
    xx = [k**3/10000 for k in orders]
    yy = [float(rv[k]) for k in orders]
    axes[0].scatter(xx, yy, s=17, facecolors="none", edgecolors=color, marker=marker)
    critical.extend({"N":10000,"k":k,"c":x,"ratio":y} for k,x,y in zip(orders,xx,yy))
axes[0].set(xlabel=r"Cubic parameter $k^3/N$", ylabel=r"Normalized moment $R_k$",
            title="A. The parity split", xlim=(0,9))
axes[0].legend(frameon=False, fontsize=9, loc="upper left")
axes[0].text(.98, .04, r"Markers: recurrence at $N=10^4$", transform=axes[0].transAxes,
             ha="right", fontsize=8.5)
data["critical"] = critical
t = np.linspace(0, 2, 200)
axes[1].plot(t, np.exp(t*t/4), color=INK, linewidth=2, label=r"Limit $e^{t^2/4}$")
boundary = []
for n, color, style in [(10000, ORANGE, "--"), (1000000, BLUE, ":")]:
    values = ratios(n, int(2*np.sqrt(n)))
    stride = 2 if n == 10000 else 20
    orders = list(range(2, int(2*np.sqrt(n))+1, stride))
    xx = [k/np.sqrt(n) for k in orders]
    yy = [float(values[k]/hyperbolic(n,k)) for k in orders]
    axes[1].plot(xx, yy, color=color, linestyle=style, label=rf"Even, $N=10^{{{int(np.log10(n))}}}$")
    boundary.extend({"N":n,"k":k,"t":x,"ratio_to_H":y} for k,x,y in zip(orders,xx,yy))
axes[1].set(xlabel=r"Square-root parameter $t=k/\sqrt{N}$", ylabel=r"Ratio $R_k/H_k$",
            title="B. The next correction", xlim=(0,2), ylim=(.94,2.85))
axes[1].legend(frameon=False, fontsize=9, loc="upper left")
for ax in axes:
    ax.grid(alpha=.15)
fig.tight_layout(pad=1.5)
fig.savefig(ROOT/"moment-regimes.pdf", bbox_inches="tight")
fig.savefig(ROOT/"moment-regimes.png", dpi=180, bbox_inches="tight")
plt.close(fig)
data["boundary"] = boundary
(ROOT/"moment-regimes-data.json").write_text(json.dumps(data,indent=2)+"\n")

fig, axes = plt.subplots(1, 2, figsize=(8.4, 3.6))
for ax, cells, title, color, formula in [
    (axes[0], [(0,0),(1,1)], "Separate rows and columns", BLUE, r"$1/[N^2(N-1)]$"),
    (axes[1], [(0,0),(0,1)], "A shared row", ORANGE, r"$-1/N^2$")]:
    for i in range(5):
        ax.plot([0,4],[i,i],color="#c6d1d9",linewidth=1)
        ax.plot([i,i],[0,4],color="#c6d1d9",linewidth=1)
    for row,col in cells:
        ax.add_patch(plt.Rectangle((col,3-row),1,1,facecolor=color,alpha=.16))
        ax.scatter([col+.5],[3-row+.5],s=80,color=color)
    ax.set(xlim=(-.15,4.15),ylim=(-.8,4.1),aspect="equal",title=title)
    ax.text(2,-.45,formula,ha="center",fontsize=13,color=color)
    ax.axis("off")
fig.tight_layout(pad=1.1)
fig.savefig(ROOT/"cell-patterns.pdf",bbox_inches="tight")
fig.savefig(ROOT/"cell-patterns.png",dpi=180,bbox_inches="tight")

fig, axes = plt.subplots(1, 2, figsize=(10.2, 3.8))
scales = np.linspace(0, 2, 250)
signed_data = []
for parity, color, name in [(0, BLUE, "Even"), (1, ORANGE, "Odd")]:
    limit = (2*parity-1)*np.sqrt(scales)/2 + 2*scales**2.5/15
    axes[0].plot(scales, limit, color=color, linewidth=1.8, label=name + " limit")
for n, marker in [(10000, "o"), (1000000, "s")]:
    values = ratios(n, int(2*np.sqrt(n)) + 2)
    for parity, color in [(0, BLUE), (1, ORANGE)]:
        orders = []
        for scale in np.linspace(.15, 1.95, 10):
            order = int(scale*np.sqrt(n))
            order -= (order-parity) % 2
            orders.append(max(2+parity, order))
        errors = []
        for order in orders:
            corrected = values[order]/hyperbolic(n, order)/mp.exp(mp.mpf(order)**2/(4*n))
            errors.append(float(mp.root(n,4)*(corrected-1)))
            signed_data.append({"N":n,"k":order,"scale":order/np.sqrt(n),
                                "scaled_error":errors[-1]})
        axes[0].scatter([order/np.sqrt(n) for order in orders], errors,
                        s=18, facecolors="none", edgecolors=color, marker=marker)
axes[0].axhline(0, color=INK, linewidth=.6, alpha=.4)
axes[0].set(xlabel=r"Square-root scale $c=k/\sqrt{N}$",
            ylabel=r"Scaled error $N^{1/4}(W_{N,k}-1)$",
            title="A. The signed first error", xlim=(0,2))
axes[0].legend(frameon=False, fontsize=8.5, loc="upper left")
axes[0].text(.04,.73,"Circles: $N=10^4$\nSquares: $N=10^6$",
             transform=axes[0].transAxes,va="top",fontsize=8)
axes[1].plot(scales,2*scales**2.5/15,color=INK,linewidth=1.8,
             label=r"Limit $2c^{5/2}/15$")
hierarchy_data = []
for n, color, style in [(10000, ORANGE, "--"),(1000000, BLUE, ":")]:
    scale_size = n**.6
    values = ratios(n, int(2*scale_size)+2)
    orders = sorted({max(2, 2*int(scale*scale_size/2)) for scale in np.linspace(.05,2,100)})
    errors = []
    for order in orders:
        value = mp.log(values[order]/hyperbolic(n,order))-mp.mpf(order)**2/(4*n)
        errors.append(float(value))
        hierarchy_data.append({"N":n,"k":order,"scale":order/scale_size,
                               "log_ratio_after_quartic":errors[-1]})
    axes[1].plot([order/scale_size for order in orders],errors,color=color,
                 linestyle=style,label=rf"Even, $N=10^{{{int(np.log10(n))}}}$")
axes[1].set(xlabel=r"Next scale $c=k/N^{3/5}$",
            ylabel=r"Logarithmic error $\log W_{N,k}$",
            title="B. The first omitted exponent",xlim=(0,2))
axes[1].legend(frameon=False,fontsize=8.5,loc="upper left")
for ax in axes:
    ax.grid(alpha=.15)
fig.tight_layout(pad=1.5)
fig.savefig(ROOT/"rate-and-hierarchy.pdf",bbox_inches="tight")
fig.savefig(ROOT/"rate-and-hierarchy.png",dpi=180,bbox_inches="tight")
plt.close(fig)
(ROOT/"rate-and-hierarchy-data.json").write_text(json.dumps({
    "arithmetic":"60-digit recurrence evaluation, not a formal certificate",
    "signed_error":signed_data,"hierarchy":hierarchy_data},indent=2)+"\n")
print("Saved three figures and their numerical data.")
