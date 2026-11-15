"""Independent diagnostic of the exact gadgets in the unweighted source.

Builds K_{m,m} cells, a 2/3 even-chain rational gadget, and the three
length-three insertion connector. Checks simplicity, bipartiteness,
exact-resistance numerics, compressed powers, Ritz inequalities, and extras.
Numerical checks support, but do not replace, the proof audit.
"""
import numpy as np
from scipy.linalg import eigh, solve, null_space


class Graph:
    def __init__(self):
        self.colors = []
        self.edges = set()

    def vertex(self, color):
        self.colors.append(color)
        return len(self.colors) - 1

    def edge(self, u, v):
        assert u != v
        assert self.colors[u] != self.colors[v]
        key = tuple(sorted((u, v)))
        assert key not in self.edges
        self.edges.add(key)

    def chain(self, u, v, length):
        assert self.colors[v] == self.colors[u] ^ (length % 2)
        previous = u
        for step in range(1, length):
            current = self.vertex(self.colors[u] ^ (step % 2))
            self.edge(previous, current)
            previous = current
        self.edge(previous, v)

    def laplacian(self):
        answer = np.zeros((len(self.colors), len(self.colors)))
        for u, v in self.edges:
            answer[u, u] += 1
            answer[v, v] += 1
            answer[u, v] -= 1
            answer[v, u] -= 1
        return answer


def build(s):
    graph = Graph()
    masses = [1, 2, 3]
    portcolors = [0, 0, 1]
    cells, ports = [], []
    for mass, portcolor in zip(masses, portcolors):
        m = int(s * mass / 2)
        left = [graph.vertex(portcolor) for _ in range(m)]
        right = [graph.vertex(1-portcolor) for _ in range(m)]
        for u in left:
            for v in right:
                graph.edge(u, v)
        cells.append(left + right)
        ports.append(left[0])
    # Conductance 2/3: 2p=4 chains of length 2q=6.
    for _ in range(4):
        graph.chain(ports[0], ports[1], 6)
    # Distinguished conductance 1 without a direct edge.
    for _ in range(3):
        graph.chain(ports[1], ports[2], 3)
    n = len(graph.colors)
    j = np.zeros((n, 3))
    for i, cell in enumerate(cells):
        j[cell, i] = 1 / np.sqrt(len(cell))
    base = graph.laplacian()
    b = np.zeros(n)
    b[ports[1]], b[ports[2]] = 1, -1
    assert tuple(sorted((ports[1], ports[2]))) not in graph.edges
    graph.edge(ports[1], ports[2])
    updated = graph.laplacian()
    assert np.array_equal(updated-base, np.outer(b, b))
    return base, updated, j, b


def positive_eigendecomposition(laplacian):
    values, vectors = eigh(laplacian)
    assert abs(values[0]) < 1e-8
    assert values[1] > 1e-8
    return values[1:], vectors[:, 1:]


def matrix_power_psd(a, alpha):
    values, vectors = eigh(a)
    values = np.maximum(values, 0)
    return (vectors * values**alpha) @ vectors.T


def run():
    alpha, t = 0.6, 0.7
    masses = np.array([1., 2., 3.])
    incidence = np.array([[1, 0], [-1, 1], [0, -1]], dtype=float)
    scale = np.diag(masses**-0.5)
    h = scale @ (incidence * [2/3, 1]) @ incidence.T @ scale
    hp = scale @ (incidence * [2/3, 2]) @ incidence.T @ scale
    ha, hpa = matrix_power_psd(h, alpha), matrix_power_psd(hp, alpha)
    vmacro = null_space(np.sqrt(masses)[None, :])
    qmacro = eigh(vmacro.T @ hpa @ vmacro, vmacro.T @ ha @ vmacro, eigvals_only=True)[::-1]
    print("alpha=0.6; macro masses=(1,2,3); conductances=(2/3,1)->(2/3,2)")
    print("macro relative spectrum:", qmacro)
    print("columns: s N R residual_resolvent residual_power top_spectrum_error max_extra_log budget_slack_Ritz")
    for s in [4, 8, 16, 32, 64, 128, 256]:
        l, lp, j, b = build(s)
        a, ap = s*l, s*lp
        va, ua = positive_eigendecomposition(a)
        vb, ub = positive_eigendecomposition(ap)
        resistance = s * np.sum((ua.T @ b)**2/va)
        assert abs(resistance-1) < 1e-8
        compresolvent = j.T @ solve(a+t*np.eye(len(a)), j, assume_a="pos")
        resolvent_error = np.linalg.norm(compresolvent-np.linalg.inv(h+t*np.eye(3)), 2)
        uaj, ubj = ua.T @ j, ub.T @ j
        compa = (uaj.T * va**alpha) @ uaj
        compb = (ubj.T * vb**alpha) @ ubj
        power_error = np.linalg.norm(compa-ha, 2)
        g = j.T @ np.ones(len(a))
        v = null_space(g[None, :])
        ritz = eigh(v.T @ compb @ v, v.T @ compa @ v, eigvals_only=True)[::-1]
        cross = (va**(-alpha/2))[:, None] * (ua.T @ ub) * vb**(alpha/2)
        full = eigh(cross @ cross.T, eigvals_only=True)[::-1]
        assert full[-1] >= 1-1e-8
        assert np.min(full[:2]-ritz) >= -1e-8
        assert abs(sum(np.log(full))-alpha*np.log(2)) < 1e-6
        residualbudget = alpha*np.log(2)-sum(np.log(ritz))
        assert residualbudget >= -1e-8
        assert np.log(full[2]) <= residualbudget+1e-8
        print(f"{s:3d} {len(a):4d} {resistance:.12f} {resolvent_error:.7g} {power_error:.7g} "
              f"{max(abs(full[:2]-qmacro)):.7g} {np.log(full[2]):.7g} {residualbudget:.7g}")


if __name__ == "__main__":
    run()
