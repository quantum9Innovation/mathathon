"""Exact finite checks for squared-average-obstruction.txt; requires SymPy."""

from itertools import product
from pathlib import Path
import sympy as sp

x, t = sp.symbols("x t")


def matrix(n, edges, signs):
    a = sp.zeros(n)
    for (u, v), s in zip(edges, signs):
        a[u, v] = a[v, u] = s
    return a


def gauge_edges(n, edges):
    """Fix a spanning forest to +1; enumerate every switching class once."""
    parent = list(range(n))

    def root(v):
        while v != parent[v]:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    free = []
    for j, (u, v) in enumerate(edges):
        ru, rv = root(u), root(v)
        if ru == rv:
            free.append(j)
        else:
            parent[ru] = rv
    return free


def check_graph(name, n, edges, left):
    right = [v for v in range(n) if v not in left]
    if len(left) < len(right):
        left, right = right, left
    free = gauge_edges(n, edges)
    compressed = []
    full = []
    for bits in product((-1, 1), repeat=len(free)):
        signs = [1] * len(edges)
        for j, sign in zip(free, bits):
            signs[j] = sign
        a = matrix(n, edges, signs)
        b = a.extract(left, right)
        p = sp.Poly((b.T * b).charpoly(x).as_expr(), x)
        f = sp.Poly((a * a).charpoly(x).as_expr(), x)
        assert f == sp.Poly(x ** (len(left) - len(right)) * p.as_expr() ** 2, x)
        assert sp.Poly(a.charpoly(t).as_expr(), t) == sp.Poly(
            t ** (len(left) - len(right)) * p.as_expr().subs(x, t * t), t
        )
        compressed.append(p)
        full.append(f)
    average = sp.Poly(sum(p.as_expr() for p in full) / len(full), x)
    real_count = sum(multiplicity for _, multiplicity in average.intervals())
    is_forest = len(free) == 0
    assert (real_count == n) == is_forest
    assert (len(set(p.as_expr() for p in compressed)) == 1) == is_forest
    return f"{name}: switching_classes={len(full)}, degree={n}, real_root_multiplicity={real_count}, forest={is_forest}"


def cycle_edges(n):
    return [(j, (j + 1) % n) for j in range(n)]


lines = []
examples = [
    ("path5", 5, [(j, j + 1) for j in range(4)], [0, 2, 4]),
    ("star5", 5, [(0, j) for j in range(1, 5)], [0]),
    ("C4_with_leaf", 5, cycle_edges(4) + [(0, 4)], [0, 2]),
    ("K3,3", 6, [(i, j) for i in range(3) for j in range(3, 6)], [0, 1, 2]),
    ("cube", 8, [(i, i ^ (1 << k)) for i in range(8) for k in range(3) if i < (i ^ (1 << k))], [i for i in range(8) if i.bit_count() % 2 == 0]),
]
for example in examples:
    lines.append(check_graph(*example))

for n in range(4, 22, 2):
    edges = cycle_edges(n)
    a_plus = matrix(n, edges, [1] * n)
    a_minus = matrix(n, edges, [-1] + [1] * (n - 1))
    expected = sp.expand(((a_plus * a_plus).charpoly(x).as_expr() + (a_minus * a_minus).charpoly(x).as_expr()) / 2)
    cheb = sp.Poly(2 * sp.chebyshevt(n, t / 2), t)
    h = sum(coef * x ** (power[0] // 2) for power, coef in cheb.terms())
    assert sp.expand(expected - h * h - 4) == 0
    assert not sp.Poly(expected, x).intervals()
    lines.append(f"C{n}: exact Chebyshev identity and zero real roots")

for polynomial in [t*t, t**4 - 3*t*t + 1, 2*t**6 + t*t - 4]:
    poly = sp.Poly(polynomial, t)
    r, c = poly.degree(), poly.LC()
    for m in (2, 3, 4):
        n = r * m
        edges = cycle_edges(n)
        plus = matrix(n, edges, [1] * n)
        minus = matrix(n, edges, [-1] + [1] * (n - 1))

        def evaluate(a):
            ans = sp.zeros(n)
            for (power,), coefficient in poly.terms():
                ans += coefficient * (a ** power)
            return ans

        difference = sp.trace(evaluate(plus) ** m) - sp.trace(evaluate(minus) ** m)
        assert difference == 4 * n * c**m
        lines.append(f"p={polynomial}, C{n}, m={m}: trace difference={difference}")

f = sp.Poly(x**5 - 15*x**4 + 78*x**3 - 168*x**2 + 156*x - 48, x)
q_k33 = sum(
    ((sp.Matrix([[1, 1, 1], [1, a, b], [1, c, d]]).T *
      sp.Matrix([[1, 1, 1], [1, a, b], [1, c, d]])).charpoly(x).as_expr())**2
    for a, b, c, d in product((-1, 1), repeat=4)
) / 16
assert sp.Poly(q_k33, x).diff() == f.mul_ground(6)
assert sum(m for _, m in f.intervals()) == 1
sturm = [
    f.as_expr(), f.diff().as_expr(),
    sp.Rational(6, 5)*(4*x**3 - 33*x**2 + 64*x - 38),
    (11*x*x - 184*x + 354)/16,
    -sp.Rational(384, 121)*(190*x - 427),
    sp.Rational(142901, 577600),
]
assert all(sp.expand(a-b) == 0 for a, b in zip(sturm, sp.sturm(f.as_expr(), x)))
lines.append("K3,3: exact derivative quintic and Sturm chain; one real root out of five")

output = "\n".join(lines) + "\nAll exact checks passed.\n"
print(output, end="")
Path(__file__).with_name("verification-output.txt").write_text(output)
