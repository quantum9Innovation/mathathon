"""Independent exact cycle-cover checks on small labeled lift graphs."""
from fractions import Fraction
from itertools import permutations, product
from math import prod
from pathlib import Path
import json


def lift(k, n, pi):
    adj = [set() for _ in range(k*n)]
    for i in range(k):
        for a in range(n):
            j = (i+1) % k
            b = pi[a] if i == k-1 else a
            u, v = i*n+a, j*n+b
            adj[u].add(v)
            adj[v].add(u)
    return adj


def components(adj):
    unseen = set(range(len(adj)))
    out = 0
    while unseen:
        stack = [unseen.pop()]
        out += 1
        while stack:
            for v in adj[stack.pop()]:
                if v in unseen:
                    unseen.remove(v)
                    stack.append(v)
    return out


def partition_count(adj, k, n):
    # Independent balanced named-map enumeration and local cover verification.
    answers = set()
    for labels in product(range(k), repeat=k*n):
        if any(labels.count(c) != n for c in range(k)):
            continue
        if any({labels[w] for w in adj[v]} !=
               {(labels[v]-1) % k, (labels[v]+1) % k}
               for v in range(k*n)):
            continue
        blocks = tuple(sorted(tuple(v for v, c in enumerate(labels) if c == i)
                              for i in range(k)))
        answers.add(blocks)
    return len(answers)


def main():
    cases = []
    for k, n in [(3, 2), (4, 2), (3, 3)]:
        sums = Fraction(0)
        for pi in permutations(range(n)):
            adj = lift(k, n, pi)
            count = partition_count(adj, k, n)
            predicted = (2*k)**(components(adj)-1)
            assert count == predicted, (k, n, pi, count, predicted)
            sums += Fraction(1, count)
        import math
        exact = sums / math.factorial(n)
        # Independent rising-factorial expression, evaluated rationally.
        t = Fraction(1, 2*k)
        formula = 2*k*prod(t+j for j in range(n))/math.factorial(n)
        assert exact == formula
        cases.append({"k": k, "N": n, "permutations": math.factorial(n),
                      "optimal_success": str(exact), "status": "PASS"})
    # Separate exact algebra checks of the two-class leading coefficient.
    constants = []
    import math
    f = math.factorial
    for a, b, expected in [(2, 1, 4), (3, 1, 64), (3, 2, 1296)]:
        t = a-b+1
        constant = Fraction(f(b*t)**2*f(a)**(2*t),
                            f(t)**2*f(b)**(2*t)*a**(t*(a-b)))
        assert constant == expected
        v, e = 2*t+2*b*t, t*(a-b)+4*b*t
        assert e-v == (a+b-2)*t
        constants.append({"a": a, "b": b, "constant": str(constant),
                          "excess": e-v, "status": "PASS"})
    report = {"status": "PASS", "cycle_cases": cases,
              "ambiguity_constant_cases": constants}
    dest = Path(__file__).with_name("boundary-checks.json")
    dest.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

