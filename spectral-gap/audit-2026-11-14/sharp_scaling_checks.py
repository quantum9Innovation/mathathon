"""Exact finite checks of the cubic-scale lower bounds."""

from fractions import Fraction
from math import prod
from pathlib import Path
import json


def even_coefficient(m):
    return Fraction(m * (16 * m * m - 3 * m - 4), 9)


def odd_coefficient(m):
    return Fraction(80 * m**3 + 195 * m * m + 124 * m + 6, 135)


def leading(n, k):
    m = k // 2
    if k % 2 == 0:
        return Fraction(prod(range(1, 2 * m, 2)), n ** (3 * m))
    return Fraction(4 * m * prod(range(1, 2 * m + 2, 2)), 3 * n ** (3 * m + 2))


def run():
    polynomial_checks = 0
    for m in range(2, 1001):
        target = (
            3 * even_coefficient(m) + (2 * m - 2) * odd_coefficient(m - 1)
        ) / (2 * m + 1) + 2 * m
        assert odd_coefficient(m) == target, m
        polynomial_checks += 1

    lower_checks = 0
    recurrence_checks = 0
    for n in range(2, 121):
        moments = [Fraction(1), Fraction(0)]
        ratios = {}
        for k in range(2, n + 1):
            value = (
                Fraction(2 * (k - 1), n * (n - k + 1)) * moments[-1]
                + Fraction(k - 1, n * n * (n - k + 1)) * moments[-2]
            )
            moments.append(value)
            ratio = value / leading(n, k)
            ratios[k] = ratio
            m = k // 2
            coefficient = even_coefficient(m) if k % 2 == 0 else odd_coefficient(m)
            assert ratio - 1 >= coefficient / n, (n, k)
            assert ratio - 1 >= Fraction(2 * k**3, 27 * n), (n, k)
            lower_checks += 1
            if k >= 4 and k % 2 == 0:
                predicted = (
                    Fraction(n, n - 2 * m + 1) * (ratios[k - 2] - 1)
                    + Fraction(4 * (2 * m - 1) * (2 * m - 2), 3 * (n - 2 * m + 1))
                    * (ratios[k - 1] - 1)
                    + Fraction((2 * m - 1) * (8 * m - 5), 3 * (n - 2 * m + 1))
                )
                assert ratio - 1 == predicted, (n, k)
                recurrence_checks += 1
            if k >= 3 and k % 2 == 1:
                predicted = (
                    Fraction(3 * n, (n - 2 * m) * (2 * m + 1)) * (ratios[k - 1] - 1)
                    + Fraction(2 * m, n - 2 * m)
                )
                if m >= 2:
                    predicted += Fraction((2 * m - 2) * n, (n - 2 * m) * (2 * m + 1)) * (
                        ratios[k - 2] - 1
                    )
                assert ratio - 1 == predicted, (n, k)
                recurrence_checks += 1
        product_upper = Fraction(1)
        for k in range(2, n // 2 + 1):
            product_upper *= 1 + Fraction(3 * k * k, n)
            assert ratios[k] <= product_upper, (n, k)

    result = {
        "status": "passed",
        "polynomial_identity_checks": polynomial_checks,
        "exact_lower_bound_checks": lower_checks,
        "exact_normalized_recurrence_checks": recurrence_checks,
        "scope": "Finite rational checks. General statements are proved in sharp-scaling-v1.md.",
    }
    output = Path(__file__).with_name("sharp-scaling-checks-v1.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    run()
