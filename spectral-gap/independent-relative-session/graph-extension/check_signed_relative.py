"""Numerical diagnostics for signed closure and weak path concatenation.

These computations illustrate the proved limits; they are not proof substitutes.
Run with a Python environment containing numpy and scipy.
"""
import numpy as np
from scipy.linalg import eigh, null_space


def power(a, exponent):
    values, vectors = eigh(a)
    if values[0] <= 0:
        raise ValueError("Expected SPD matrix")
    return (vectors * values**exponent) @ vectors.T


def relative(a, b, alpha):
    invhalf = power(a, -alpha / 2)
    answer = invhalf @ power(b, alpha) @ invhalf
    return (answer + answer.T) / 2


def reverse_ldl(a):
    n = len(a)
    residual = a.copy()
    upper = np.eye(n)
    pivots = np.empty(n)
    for i in reversed(range(n)):
        pivots[i] = residual[i, i]
        upper[:i, i] = residual[:i, i] / pivots[i]
        residual[:i, :i] -= pivots[i] * np.outer(upper[:i, i], upper[:i, i])
    assert np.linalg.norm(a - (upper * pivots) @ upper.T) < 1e-12
    return upper, pivots


def signed_closure():
    alpha = 0.6
    logr = np.array([0.5, 0.2, -0.3, -0.1])
    logdplus, logdminus = 0.9, 0.6
    r = np.exp(logr)
    h = np.maximum(1, r)
    h[0] *= np.exp(logdplus) / np.prod(h)
    x = np.sqrt([(h[i] - 1) * np.prod(h[i + 1 :]) for i in range(len(r))])
    hzero = np.eye(len(r)) + np.outer(x, x)
    upper, pivots = reverse_ldl(hzero)
    assert np.max(np.abs(pivots - h)) < 1e-12
    ell = r / h
    z = np.sqrt([(1 - ell[i]) * np.prod(ell[i + 1 :]) for i in range(len(r))])
    y = upper @ (np.sqrt(h) * z)
    m = hzero - np.outer(y, y)
    assert np.max(np.abs(reverse_ldl(m)[1] - r)) < 1e-12
    assert abs(np.linalg.slogdet(hzero)[1] - logdplus) < 1e-12
    assert abs(np.linalg.slogdet(hzero)[1] - np.linalg.slogdet(m)[1] - logdminus) < 1e-12
    assert abs(x @ x - np.expm1(logdplus)) < 1e-12
    assert abs(y @ np.linalg.solve(m, y) - np.expm1(logdminus)) < 1e-12
    print("Signed closure: cancellation slack =", logdplus - sum(logr[logr > 0]))
    target = np.diag(r**alpha)
    for delta in [0.2, 0.05, 0.01, 0.002, 0.0005]:
        av = delta ** np.arange(len(r) - 1, -1, -1, dtype=float)
        a = np.diag(av)
        b = np.sqrt(av)[:, None] * m * np.sqrt(av)[None, :]
        q = relative(a, b, alpha)
        print(f"  delta={delta:g}, matrix-limit error={np.linalg.norm(q-target, 2):.8g}")


def path(weights):
    incidence = np.zeros((len(weights) + 1, len(weights)))
    for j in range(len(weights)):
        incidence[j, j] = 1
        incidence[j + 1, j] = -1
    return (incidence * weights) @ incidence.T


def path_relative(a, b, alpha):
    basis = null_space(np.ones((1, len(a))))
    correction = relative(basis.T @ a @ basis, basis.T @ b @ basis, alpha) - np.eye(len(a)-1)
    return basis @ correction @ basis.T


def weak_concatenation():
    alpha = 0.6
    first = [0.3, 2, 0.5]
    firstprime = [0.3, 6, 0.5]
    second = [0.4, 1.2]
    secondprime = [0.4, 0.3]
    c1 = path_relative(path(first), path(firstprime), alpha)
    c2 = path_relative(path(second), path(secondprime), alpha)
    n1, n2 = len(first)+1, len(second)+1
    target = np.zeros((n1+n2, n1+n2))
    target[:n1, :n1] = c1
    target[n1:, n1:] = c2
    print("Weak concatenation: exact positive/negative determinant budgets = log(3), log(4)")
    for coupling in [0.1, 0.01, 0.001, 0.0001, 0.00001]:
        a = path(first + [coupling] + second)
        b = path(firstprime + [coupling] + secondprime)
        cover = path(firstprime + [coupling] + second)
        basis = null_space(np.ones((1, n1+n2)))
        ldeta = np.linalg.slogdet(basis.T @ a @ basis)[1]
        ldetb = np.linalg.slogdet(basis.T @ b @ basis)[1]
        ldeth = np.linalg.slogdet(basis.T @ cover @ basis)[1]
        assert abs(ldeth - ldeta - np.log(3)) < 1e-8
        assert abs(ldeth - ldetb - np.log(4)) < 1e-8
        c = path_relative(a, b, alpha)
        print(f"  coupling={coupling:g}, relative-limit error={np.linalg.norm(c-target, 2):.8g}")


if __name__ == "__main__":
    signed_closure()
    weak_concatenation()
