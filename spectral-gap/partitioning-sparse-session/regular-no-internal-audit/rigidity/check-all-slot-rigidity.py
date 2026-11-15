"""Finite corroboration of the written all-slot rigidity proof.

Uses only the Python standard library. Exhausts all set partitions of
five explicit small graphs and checks an odd-fiber family of cover laws.
These diagnostics are not premises of the asymptotic proof.
"""
from collections import Counter, defaultdict
from itertools import permutations, product
from math import log, sqrt
from pathlib import Path
import json


def partitions(n):
    labels = [0] * n

    def rec(t, largest):
        if t == n:
            yield tuple(labels)
            return
        for x in range(largest + 2):
            labels[t] = x
            yield from rec(t + 1, max(largest, x))

    yield from rec(1, 0)


def normalized_labels(values):
    rename = {}
    return tuple(rename.setdefault(x, len(rename)) for x in values)


def graph(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        assert u != v and v not in adj[u]
        adj[u].append(v)
        adj[v].append(u)
    assert len(set(map(len, adj))) == 1
    return [sorted(x) for x in adj]


def quotient(adj, labels):
    r = max(labels) + 1
    rows = [None] * r
    for v, neighbors in enumerate(adj):
        row = [0] * r
        for u in neighbors:
            row[labels[u]] += 1
        row = tuple(row)
        x = labels[v]
        if rows[x] is not None and rows[x] != row:
            return None
        rows[x] = row
    return tuple(rows)


def entropy(probs):
    return -sum(p * log(p) for p in probs if p > 0)


def marginal(law, coords):
    result = defaultdict(float)
    for values, probability in law.items():
        result[tuple(values[s] for s in coords)] += probability
    return dict(result)


def h(law):
    return entropy(law.values())


def check_laws(adj, old, labels, R, metrics, boundary=False, count=True):
    n, k, r, d = len(adj), len(old), len(R), len(adj[0])
    old_type = {v: i for i, block in enumerate(old) for v in block}
    alpha = [len(block) / n for block in old]
    stars, types = [], []
    for i, block in enumerate(old):
        law = defaultdict(float)
        slot_types = None
        for v in block:
            grouped = [tuple(labels[u] for u in adj[v] if old_type[u] == j)
                       for j in range(k)]
            now_types = tuple(j for j, group in enumerate(grouped) for _ in group)
            assert slot_types is None or slot_types == now_types
            slot_types = now_types
            choices = [tuple(permutations(group)) for group in grouped]
            denominator = len(block)
            for choice in choices:
                denominator *= len(choice)
            for ordered_groups in product(*choices):
                neighbors = tuple(x for group in ordered_groups for x in group)
                law[(labels[v],) + neighbors] += 1 / denominator
        assert abs(sum(law.values()) - 1) < 1e-10
        stars.append(dict(law))
        types.append(slot_types)
    roots = [marginal(P, [0]) for P in stars]
    root_vectors = [[law.get((x,), 0) for x in range(r)] for law in roots]
    V = [1 - sum(p * p for p in rho) for rho in root_vectors]
    defect = sum(a * (1 - max(rho)) for a, rho in zip(alpha, root_vectors))
    phi = sum(a * h(P) for a, P in zip(alpha, stars))
    edge_I = 0.0
    pair_laws = {}
    for i in range(k):
        for j in set(types[i]):
            slot = types[i].index(j)
            pair = marginal(stars[i], [0, slot + 1])
            pair_laws[i, j] = pair
            for s, neighbor_type in enumerate(types[i]):
                if neighbor_type == j:
                    other = marginal(stars[i], [0, s + 1])
                    assert all(abs(pair.get(x, 0) - other.get(x, 0)) < 1e-10
                               for x in set(pair) | set(other))
            neighbor = marginal(pair, [1])
            assert all(abs(neighbor.get((x,), 0) - root_vectors[j][x]) < 1e-10
                       for x in range(r))
    for (i, j), pair in pair_laws.items():
        reverse = pair_laws[j, i]
        assert all(abs(prob - reverse.get((y, x), 0)) < 1e-10
                   for (x, y), prob in pair.items())
        if i <= j:
            degree = types[i].count(j)
            w = alpha[i] * degree / (2 if i == j else 1)
            phi -= w * h(pair)
            edge_I += w * (h(roots[i]) + h(roots[j]) - h(pair))
    J_total = 0.0
    for i, P in enumerate(stars):
        pairs = [marginal(P, [0, s + 1]) for s in range(d)]
        slot_I = [h(roots[i]) + h(roots[types[i][s]]) - h(pairs[s])
                  for s in range(d)]
        local_J, local_K, differences = [], [], []
        M = [sum(root_vectors[types[i][s]][x] for s in range(d))
             for x in range(r)]
        B = sum(p * sum((R[x[0]][z] - M[z]) ** 2 for z in range(r))
                for x, p in roots[i].items())
        for t in range(d):
            retained = [s for s in range(d) if s != t]
            Pminus = marginal(P, [0] + [s + 1 for s in retained])
            J = sum(h(pairs[s]) - h(roots[i]) for s in retained)
            J -= h(Pminus) - h(roots[i])
            kappa_direct = 0.0
            for tup, prob in Pminus.items():
                aux_prob = root_vectors[i][tup[0]]
                for z, s in zip(tup[1:], retained):
                    aux_prob *= root_vectors[types[i][s]][z]
                kappa_direct += prob * log(prob / aux_prob)
            kappa = J + sum(slot_I[s] for s in retained)
            metrics['maxKLIdentityError'] = max(metrics['maxKLIdentityError'],
                                                abs(kappa - kappa_direct))
            mu = root_vectors[types[i][t]]

            def f(tup):
                difference = [R[tup[0]][x] - mu[x] for x in range(r)]
                for label in tup[1:]:
                    difference[label] -= 1
                answer = sum(x * x for x in difference)
                assert -1e-10 <= answer <= 2 * d * d + 1e-10
                return answer

            EP = sum(prob * f(tup) for tup, prob in Pminus.items())
            root_support = [(x[0], p) for x, p in roots[i].items() if p > 0]
            supports = [[(x, p) for x, p in enumerate(root_vectors[types[i][s]]) if p > 0]
                        for s in retained]
            EQ = 0.0
            for x, px in root_support:
                for choices in product(*supports):
                    prob = px
                    for _, p in choices:
                        prob *= p
                    EQ += prob * f((x,) + tuple(z for z, _ in choices))
            Vt = V[types[i][t]]
            expected_Q = sum(V[types[i][s]] for s in retained) + B
            metrics['maxActualVarianceError'] = max(metrics['maxActualVarianceError'], abs(EP - Vt))
            metrics['maxProductVarianceError'] = max(metrics['maxProductVarianceError'], abs(EQ - expected_Q))
            assert abs(EP - Vt) < 1e-8 and abs(EQ - expected_Q) < 1e-8
            assert abs(EQ - EP) <= 2 * d * d * sqrt(max(0, kappa_direct) / 2) + 1e-6
            local_J.append(J)
            local_K.append(kappa_direct)
            differences.append(EQ - EP)
        J_total += alpha[i] * sum(local_J)
        Vsum = sum(V[j] for j in types[i])
        metrics['maxSummedVarianceError'] = max(metrics['maxSummedVarianceError'],
            abs(sum(differences) - ((d - 2) * Vsum + d * B)))
        if not boundary:
            L = -phi
            assert alpha[i] * sum(local_K) <= 2 * d * (d - 1) / (d - 2) * L + 1e-8
            local_bound = alpha[i] * (d - 2) ** 3 / (4 * d ** 6 * (d - 1)) * Vsum ** 2
            assert L + 1e-8 >= local_bound
    cancellation = -(d - 2) / d * edge_I - J_total / d
    metrics['maxCancellationError'] = max(metrics['maxCancellationError'], abs(phi - cancellation))
    assert abs(phi - cancellation) < 1e-8
    if boundary:
        assert abs(phi) < 1e-8 and defect > 0
        return
    gap = min(alpha) * (d - 2) ** 3 / (4 * d ** 6 * (d - 1)) * defect ** 2
    metrics['minGapSlack'] = min(metrics['minGapSlack'], -phi - gap)
    assert phi <= -gap + 1e-8
    assert (abs(phi) < 1e-8) == (defect < 1e-8)
    if count:
        if defect > 1e-8:
            metrics['positiveDefect'] += 1
        else:
            metrics['zeroDefect'] += 1
        if len(set(R)) < r:
            metrics['repeatedQuotientRows'] += 1


def examples():
    lift_edges = []
    edge_index = 0
    for i in range(4):
        for j in range(i + 1, 4):
            flip = int(edge_index == 0)
            lift_edges.extend((2 * i + u, 2 * j + (u ^ flip)) for u in range(2))
            edge_index += 1
    yield 'K4-two-lift-zero-internal', graph(8, lift_edges), [list(range(2*i, 2*i+2)) for i in range(4)], None
    matching_edges = [(0,1),(2,3),(4,5),(6,7)]
    matching_edges += [(u, 4+u) for u in range(4)] + [(u, 4+(u+1)%4) for u in range(4)]
    yield 'cubic-internal-matchings', graph(8, matching_edges), [list(range(4)),list(range(4,8))], None
    unequal_edges = [(0, v) for v in [2,3,4]] + [(1, v) for v in [5,6,7]]
    unequal_edges += [(v, 2+(v-1)%6) for v in range(2,8)]
    yield 'unequal-proportions-zero-internal', graph(8, unequal_edges), [[0,1],list(range(2,8))], None
    yield 'one-class-cubic-K4', graph(4, [(u,v) for u in range(4) for v in range(u+1,4)]), [list(range(4))], None
    yield 'degree-four-allcross-K44', graph(8, [(u,v) for u in range(4) for v in range(4,8)]), [list(range(4)),list(range(4,8))], None
    odd_edges = [(3*i+u,3*j+u) for i in range(4) for j in range(i+1,4) for u in range(3)]
    odd_labels = set()
    for base in partitions(4):
        for component in partitions(3):
            odd_labels.add(normalized_labels((base[i],component[u]) for i in range(4) for u in range(3)))
    yield 'odd-three-fold-K4-cover-selected-product-partitions', graph(12,odd_edges), [list(range(3*i,3*i+3)) for i in range(4)], sorted(odd_labels)


def main():
    reports = []
    for name, adj, old, selected in examples():
        metrics = dict(name=name, vertices=len(adj), oldSizes=list(map(len,old)), degree=len(adj[0]),
                       testedPartitions=0, equitable=0, positiveDefect=0, zeroDefect=0,
                       repeatedQuotientRows=0, maxCancellationError=0.0, maxKLIdentityError=0.0,
                       maxActualVarianceError=0.0, maxProductVarianceError=0.0,
                       maxSummedVarianceError=0.0, minGapSlack=float('inf'), unusedLabelChecks=0)
        iterator = partitions(len(adj)) if selected is None else iter(selected)
        padded_done = False
        for labels in iterator:
            metrics['testedPartitions'] += 1
            R = quotient(adj, labels)
            if R is None:
                continue
            metrics['equitable'] += 1
            check_laws(adj, old, labels, R, metrics)
            if not padded_done:
                padded = tuple(tuple(row) + (0,) for row in R) + ((0,) * (len(R)+1),)
                check_laws(adj, old, labels, padded, metrics, count=False)
                metrics['unusedLabelChecks'] += 1
                padded_done = True
        metrics['partitionScope'] = 'all set partitions' if selected is None else 'all 75 base/component product partitions'
        reports.append(metrics)
    boundary_metrics = dict(maxCancellationError=0.0, maxKLIdentityError=0.0,
                            maxActualVarianceError=0.0, maxProductVarianceError=0.0,
                            maxSummedVarianceError=0.0)
    cycle = graph(4, [(0,1),(1,2),(2,3),(3,0)])
    check_laws(cycle, [[0,1,2,3]], (0,1,0,1), ((0,2),(2,0)), boundary_metrics, boundary=True)
    result = {'status':'PASS: finite corroboration of the complete written local proof',
              'examples':reports,
              'excludedDegreeTwoAlternatingCycle':{'status':'zero entropy with positive defect confirmed', **boundary_metrics}}
    target = Path(__file__).with_name('all-slot-rigidity-checks.json')
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
