from fractions import Fraction
from math import comb, factorial, log, log1p, exp, sqrt
from pathlib import Path
from itertools import permutations
import hashlib
import json


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent / "frozen-manuscript-v1"


def falling(n, k):
    out = 1
    for j in range(k):
        out *= n - j
    return out


def partitions(k, j=2):
    if k == 0:
        yield {}
        return
    if j > k:
        return
    for count in range(k // j + 1):
        for tail in partitions(k - count * j, j + 1):
            yield ({j: count} | tail) if count else tail


def leading_q(k, n):
    m = k // 2
    if k % 2 == 0:
        return Fraction(factorial(k) * n**m, 2**m * factorial(m))
    return Fraction(4 * m * factorial(k) * n**m, 3 * 2**m * factorial(m))


checks = {}
checks["manifest_sha256"] = hashlib.sha256((ROOT / "MANIFEST.json").read_bytes()).hexdigest()
for entry in json.loads((ROOT / "MANIFEST.json").read_text()):
    assert hashlib.sha256((ROOT / entry["path"]).read_bytes()).hexdigest() == entry["sha256"]
checks["manifest_entries_verified"] = 16

depleted_cases = 0
for n in range(1, 21):
    for r in range(n + 1):
        remain = n - r
        direct = []
        for h in range(remain + 1):
            value = sum((Fraction(comb(h, j) * n**j * (-1)**(h - j), falling(remain, j)) for j in range(h + 1)), Fraction())
            direct.append(value)
            assert value >= 0
            if h:
                rhs = (r + 2*h - 2) * direct[h-1]
                if h >= 2:
                    rhs += (h - 1) * direct[h-2]
                assert (remain - h + 1) * value == rhs
            depleted_cases += 1
checks["exact_depleted_moment_cases"] = depleted_cases

partition_cases = 0
availability_cases = 0
for n in range(2, 25):
    for k in range(2, min(n, 14) + 1):
        moment = sum((Fraction(comb(k, j) * (-1)**(k-j), n**(k-j) * falling(n, j)) for j in range(k + 1)), Fraction())
        q_direct = falling(n, k) * n**k * moment
        q_partition = Fraction()
        m = k // 2
        big_k = 2*m
        for counts in partitions(k):
            contribution = Fraction(factorial(k))
            for j, count in counts.items():
                contribution *= Fraction(n * (j-1), j)**count / factorial(count)
            q_partition += contribution
            nonpair = {j: c for j, c in counts.items() if j >= 3}
            total = sum(j*c for j, c in nonpair.items())
            bare = Fraction(1)
            for j, count in nonpair.items():
                bare *= Fraction(n * (j-1), j)**count / factorial(count)
            if k % 2 == 0:
                s = total // 2
                availability_value = Fraction(falling(m, s), m**s) * Fraction(big_k, n)**s * bare
            else:
                s = (total - 3) // 2
                availability_value = Fraction(falling(m-1, s), m**s) * Fraction(big_k, n)**s * Fraction(3, 2*n) * bare
            assert contribution / leading_q(k, n) == availability_value
            availability_cases += 1
        assert q_direct == q_partition
        partition_cases += 1
checks["exact_partition_total_cases"] = partition_cases
checks["exact_individual_availability_cases"] = availability_cases

threshold_cases = 0
upper_cases = 0
for n in range(2, 101):
    moments = [Fraction(1), Fraction(0)]
    for k in range(2, n + 1):
        value = Fraction(2*(k-1), n*(n-k+1))*moments[-1] + Fraction(k-1, n*n*(n-k+1))*moments[-2]
        moments.append(value)
        ratio = value * n**(2*k) / leading_q(k, n)
        assert ratio - 1 >= Fraction(2*k**3, 27*n)
        threshold_cases += 1
        if 2*k <= n:
            assert log(ratio.numerator) - log(ratio.denominator) <= 3*k**3/n + 1e-12
            upper_cases += 1
checks["exact_lower_bound_cases"] = threshold_cases
checks["numerical_upper_bound_cases"] = upper_cases

perms = list(permutations(range(1, 5)))
first = [p for p in perms if p[0] == 1]
second = [p for p in perms if p[1] == 3 and p[3] == 2]
assert len(first) == 6 and all(p[0] == 1 for p in first)
assert len(second) == 2 and sum(p[0] == 1 for p in second) == 1
checks["conditioning_atoms"] = {
    "shared_row_event_probability": str(Fraction(len(first), len(perms))),
    "shared_row_true_probability": "1",
    "two_arrows_atom_probability": str(Fraction(len(second), len(perms))),
    "two_arrows_true_probability": "1/2",
}


def logadd(a, b):
    c = max(a, b)
    return c + log1p(exp(min(a, b) - c))


def ratios_at(n, k):
    e = o = 0.0
    for m in range(1, k//2 + 1):
        a = n / (n - 2*m + 1)
        b = 4 * (2*m - 1) * (2*m - 2) / (3 * (n - 2*m + 1))
        c = 3*n / ((n - 2*m)*(2*m + 1))
        d = (2*m - 2)*n / ((n - 2*m)*(2*m + 1))
        e = log(a) + e if b == 0 else logadd(log(a) + e, log(b) + o)
        o = log(c) + e if d == 0 else logadd(log(c) + e, log(d) + o)
    big_k = 2*(k//2)
    lam = (2/3)*sqrt(big_k**3/n)
    even_h = lam - log(2) + log1p(exp(-2*lam))
    odd_h = lam - log(2) + log1p(-exp(-2*lam)) - log(lam)
    return {
        "even_k": big_k,
        "odd_k": big_k + 1,
        "even_corrected_ratio": exp(e - even_h - big_k**2/(4*n)),
        "odd_corrected_ratio": exp(o - odd_h - (big_k+1)**2/(4*n)),
    }


checks["square_root_numeric_samples"] = [dict(n=n, target_d=d, **ratios_at(n, 2*int(sqrt(d*n)/2))) for n in (10_000, 1_000_000, 100_000_000) for d in (1, 4)]
out = HERE / "manuscript-referee-checks.json"
out.write_text(json.dumps(checks, indent=2) + "\n")
print(json.dumps(checks, indent=2))
