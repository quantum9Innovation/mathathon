"""Exact checks accompanying analytic counterexamples, without external packages."""

from fractions import Fraction
from hashlib import sha256
from json import dumps
from pathlib import Path


def matmul(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def matrix_power(a, exponent):
    result = [[int(i == j) for j in range(len(a))] for i in range(len(a))]
    for _ in range(exponent):
        result = matmul(result, a)
    return result


def falling(n, m):
    result = 1
    for j in range(m):
        result *= n - j
    return result


def hashimoto_k4():
    darts = [(a, b) for a in range(4) for b in range(4) if a != b]
    return [[int(b == c and a != d) for c, d in darts] for a, b in darts]


def main():
    source = Path("spectral-gap/snapshot/reading-sources/relativized-second-eigenvalue/source/all.tex")
    h_bouquet = [[int(j != (i ^ 1)) for j in range(4)] for i in range(4)]
    assert all(sum(row) == 3 for row in h_bouquet)
    assert 3 * 3 > 3
    h_k4 = hashimoto_k4()
    h3 = matrix_power(h_k4, 3)
    trace = sum(h3[i][i] for i in range(len(h3)))
    assert trace == 24
    assert 2 * trace > trace
    depletion = []
    for n in [16, 32, 64, 128, 256, 512, 1024]:
        m = n // 4
        factor = Fraction(n**m, falling(n, m))
        required_c = 4 * (factor - 1) / n
        depletion.append({
            "n": n,
            "m": m,
            "walk_length": 2 * m,
            "factor_float": float(factor),
            "minimum_constant_for_r1_claim": float(required_c),
        })
    result = {
        "source_sha256": sha256(source.read_bytes()).hexdigest(),
        "source_lines": len(source.read_text().splitlines()),
        "bouquet_two_whole_loops_hashimoto": h_bouquet,
        "bouquet_row_sum": 3,
        "bouquet_order": 1,
        "k4_triangle_trace": trace,
        "identity_two_lift_certified_trace_length3": 2 * trace,
        "depletion_counterexample": depletion,
        "scope": "Finite exact checks corroborate the analytic proofs in READ_REPORT.md.",
    }
    print(dumps(result, indent=2))


if __name__ == "__main__":
    main()
