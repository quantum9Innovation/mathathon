#!/usr/bin/env python3
"""One NEW end-to-end K4-lift verification; frozen code is imported only.

This tests the known quotient R=A_K4. It does not run the enormous general
unknown-frame family or rerun earlier regression suites. Hidden labels
are used only in the independent validation after recovery.
"""
from pathlib import Path
import hashlib
import importlib.util
import itertools
import json
import random
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


audit = load(HERE/"fresh_run_check.py", "frame_independent_reference")
fk = audit.load_prototype()


def sample_fixture(N=3, seed=2):
    """Six independently sampled edge matchings, then hidden vertex labels."""
    rng = random.Random(seed)
    t, n = 4, 4*N
    old_adj = [set() for _ in range(n)]
    matchings = {}
    for a in range(t):
        for b in range(a+1, t):
            perm = list(range(N))
            rng.shuffle(perm)
            matchings[f"{a}-{b}"] = perm
            for i, j in enumerate(perm):
                old_adj[a*N+i].add(b*N+j)
                old_adj[b*N+j].add(a*N+i)
    relabel = list(range(n))
    rng.shuffle(relabel)
    adj = [set() for _ in range(n)]
    labels = [-1]*n
    for i in range(n):
        labels[relabel[i]] = i//N
        for j in old_adj[i]:
            adj[relabel[i]].add(relabel[j])
    adj = [sorted(row) for row in adj]
    assert all(len(row) == 3 and i not in row for i, row in enumerate(adj))
    assert all(i in adj[j] for i, row in enumerate(adj) for j in row)
    reached, todo = {0}, [0]
    while todo:
        i = todo.pop()
        for j in adj[i]:
            if j not in reached:
                reached.add(j)
                todo.append(j)
    assert len(reached) == n
    return adj, labels, matchings, relabel


def quotient_rows(adj, R, p):
    """Sparse column-vectorization of I_t tensor A - R^T tensor I_n."""
    n, t = len(adj), len(R)
    rows = []
    for a in range(t):
        for i in range(n):
            row = {a*n+j: 1 for j in adj[i]}
            for b in range(t):
                j = b*n+i
                row[j] = (row.get(j, 0)-R[b][a]) % p
            rows.append(sorted((j, x) for j, x in row.items() if x))
    return rows


def dense(rows):
    M = [[0]*len(rows) for _ in rows]
    for i, row in enumerate(rows):
        for j, x in row:
            M[i][j] = x
    return M


def canonical_partition(labels, t):
    return tuple(sorted(tuple(i for i, value in enumerate(labels) if value == a)
                        for a in range(t)))


def enumerate_one_hot(adj, R, columns, p, fiber_size):
    """Recovery path: A,R and full kernel only; no hidden labels/rank oracle."""
    n, t = len(adj), len(R)
    images = 0
    maps = []
    for image in fk.enumerate_kernel(columns, n*t, p):
        images += 1
        if any(x not in (0, 1) for x in image):
            continue
        labels = []
        for i in range(n):
            row = [image[a*n+i] for a in range(t)]
            if sum(row) != 1:
                break
            labels.append(row.index(1))
        if len(labels) != n:
            continue
        if [labels.count(a) for a in range(t)] != [fiber_size]*t:
            continue
        if not all([sum(labels[j] == a for j in row) for a in range(t)]
                   == R[labels[i]] for i, row in enumerate(adj)):
            continue
        maps.append(labels)
    return maps, images


def main():
    protected_before = audit.hashes()
    adj, planted, matchings, relabel = sample_fixture()
    n, t, p, N = len(adj), 4, 3, 3
    R = [[int(i != j) for j in range(t)] for i in range(t)]
    rows = quotient_rows(adj, R, p)
    fk.check_input(rows, p)  # R is symmetric, so K itself is symmetric.
    # This is the ONLY kernel recovery call in this new verification.
    columns, cert, stats = fk.kernel_basis(rows, p, seed=71251)
    assert fk.verify(rows, cert, p)
    recovered, enumerated = enumerate_one_hot(adj, R, columns, p, N)
    assert len(columns) == 10 and enumerated == 3**10
    assert len(recovered) == 24 and planted in recovered
    partition_set = {canonical_partition(labels, t) for labels in recovered}
    assert partition_set == {canonical_partition(planted, t)}
    # Independent dense reference is validation ONLY, never used by recovery.
    reference, rank = audit.gauss_kernel(dense(rows), p)
    assert rank == n*t-10
    assert audit.span_signature(columns, n*t, p) == audit.span_signature(reference, n*t, p)
    # Explain this fixture's full kernel: it is exactly the old commutant.
    R_rows = quotient_rows([[j for j in range(t) if j != i] for i in range(t)], R, p)
    commutant, _ = audit.gauss_kernel(dense(R_rows), p)
    lifted_old = []
    for z in commutant:
        lifted_old.append([z[a*t+planted[i]] for a in range(t) for i in range(n)])
    assert len(commutant) == 10
    assert audit.span_signature(columns, n*t, p) == audit.span_signature(lifted_old, n*t, p)
    assert {tuple(labels) for labels in recovered} == {
        tuple(perm[a] for a in planted) for perm in itertools.permutations(range(t))}
    protected_after = audit.hashes()
    assert protected_before == protected_after
    output = {
        "test": "known K4 quotient, random 3-lift deterministic fixture",
        "fixture_selection": "N=3, graph seed2 chosen for a manageable minimal kernel; not a statistical sample study",
        "base_vertices": 4, "base_degree": 3, "lift_size": N,
        "graph_vertices": n, "quotient_R": R,
        "simple_connected_regular_graph_checked": True,
        "matching_permutations": matchings, "hidden_vertex_relabeling": relabel,
        "field_prime": p, "field_divides_degree": True,
        "intertwiner_dimension": n*t,
        "intertwiner_nonzeros": sum(len(row) for row in rows),
        "certified_kernel_dimension": len(columns),
        "independent_gaussian_kernel_span_matches": True,
        "kernel_equals_lifted_old_commutant": True,
        "kernel_vectors_enumerated": enumerated,
        "integer_one_hot_maps": len(recovered),
        "unlabeled_equal_fiber_partitions": len(partition_set),
        "all_maps_are_base_automorphism_relabelings": True,
        "planted_fibers_recovered": True,
        "integer_local_neighbor_counts_checked": True,
        "unknown_frame_matrix_enumeration_executed": False,
        "stats": stats,
        "protected_artifacts_unchanged": True,
        "protected_hashes_before": protected_before,
        "protected_hashes_after": protected_after,
    }
    (HERE/"regular-lift-k4-checks.json").write_text(json.dumps(output, indent=2)+"\n")
    (HERE/"regular-lift-k4-certificate.json").write_text(json.dumps({
        "adjacency_lists": adj, "R": R, "prime": p,
        "kernel_certificate": cert, "integer_one_hot_maps": recovered,
        "planted_labels_used_only_in_validation": planted,
    }, indent=2)+"\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
