#!/usr/bin/env python3
"""New intertwiner fixtures; frozen solver/manuscript are only imported/read."""
from pathlib import Path
import copy
import importlib.util
import itertools
import json
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("fresh_kernel_audit", HERE/"fresh_run_check.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
fk = audit.load_prototype()


def multiply(A, B):
    return [[sum(a*b for a, b in zip(row, col)) for col in zip(*B)] for row in A]


def vec(X):
    return [X[i][j] for j in range(len(X[0])) for i in range(len(X))]


def intertwiner(A, R):
    n, t = len(A), len(R)
    return [[int(a == b)*A[i][j]-int(i == j)*R[b][a]
             for b in range(t) for j in range(n)]
            for a in range(t) for i in range(n)]


def apply_dense(A, x, p):
    return [sum(a*b for a, b in zip(row, x)) % p for row in A]


def compute_right(K, p, seed):
    n = len(K)
    S = audit.symmetrize(K)
    rows = fk.rows_from_dense(S, p)
    full_basis, full_cert, stats = fk.kernel_basis(rows, p, seed=seed)
    assert fk.verify(rows, full_cert, p)
    projected = [v[n:] for v in full_basis]
    columns, pivots = audit.rref(projected, p, n)
    cert = {key: copy.deepcopy(full_cert[key])
            for key in ["p", "h", "D", "u", "v", "ell"]}
    cert["columns"], cert["pivots"] = columns, pivots
    assert audit.verify_right(fk, K, cert, p)
    reference, rank = audit.gauss_kernel(K, p)
    assert audit.span_signature(columns, n, p) == audit.span_signature(reference, n, p)
    assert len(full_basis) == 2*len(columns)
    bad = copy.deepcopy(cert)
    bad["ell"] += 1
    assert not audit.verify_right(fk, K, bad, p)
    images = list(fk.enumerate_kernel(columns, n, p))
    assert len(images) == p**len(columns)
    assert len({tuple(x) for x in images}) == p**len(columns)
    assert all(not any(apply_dense(K, x, p)) for x in images)
    return columns, cert, images, stats


def compatible(R, sizes):
    return all(sizes[i]*R[i][j] == sizes[j]*R[j][i]
               for i in range(len(R)) for j in range(len(R)))


def main():
    before = audit.hashes()
    cases = [("zero", [[0, 0], [0, 0]], 3),
             ("identity", [[1, 0], [0, 1]], 3),
             ("nonsymmetric_nilpotent", [[0, 1], [0, 0]], 3),
             ("isotropic_plain_gram", [[1, 0], [2, 0]], 5)]
    results = []
    for index, (name, K, p) in enumerate(cases):
        C, cert, images, stats = compute_right(K, p, seed=781+index)
        results.append({"name": name, "dimension": len(K), "prime": p,
                        "right_corank": len(C), "certified": True,
                        "right_vectors_enumerated": len(images),
                        "full_block_vectors_not_enumerated": p**(2*len(C)),
                        "stats": stats})
        if name == "nonsymmetric_nilpotent":
            for diagonals in itertools.product([1, 2], repeat=4):
                a, b, c, d = diagonals
                scaled = [[a*K[0][0]*c % 3, a*K[0][1]*d % 3],
                          [b*K[1][0]*c % 3, b*K[1][1]*d % 3]]
                assert scaled[0][1] != 0
                assert multiply(scaled, scaled) == [[0, 0], [0, 0]]
        if name == "isotropic_plain_gram":
            gram = multiply([list(row) for row in zip(*K)], K)
            assert all(a % 5 == 0 for row in gram for a in row)
            assert len(C) == 1
    A = [[0, 1, 1], [1, 0, 1], [1, 1, 0]]
    R = [[0, 2], [1, 1]]
    planted = [[1, 0], [0, 1], [0, 1]]
    assert multiply(A, planted) == multiply(planted, R)
    K = intertwiner(A, R)
    assert not any(apply_dense(K, vec(planted), 5))
    # Wrongly transposing the quotient switches the actual equation.
    wrong = intertwiner(A, [list(row) for row in zip(*R)])
    assert any(apply_dense(wrong, vec(planted), 5))
    X = [[2, 3], [4, 1], [1, 0]]
    AX, XR = multiply(A, X), multiply(X, R)
    residual = [[a-b for a, b in zip(arow, rrow)] for arow, rrow in zip(AX, XR)]
    assert apply_dense(K, vec(X), 5) == [x % 5 for x in vec(residual)]
    C, cert, images, stats = compute_right(K, 5, seed=28371)
    n, t = len(A), len(R)
    accepted = []
    for image in images:
        if any(x not in (0, 1) for x in image):
            continue
        X = [[image[j*n+i] for j in range(t)] for i in range(n)]
        if any(sum(row) != 1 for row in X):
            continue
        if [sum(row[j] for row in X) for j in range(t)] != [1, 2]:
            continue
        if multiply(A, X) == multiply(X, R):
            accepted.append(tuple(row.index(1) for row in X))
    brute = []
    for labels in itertools.product(range(t), repeat=n):
        X = [[int(j == labels[i]) for j in range(t)] for i in range(n)]
        if [sum(row[j] for row in X) for j in range(t)] == [1, 2]:
            if multiply(A, X) == multiply(X, R):
                brute.append(labels)
    assert set(accepted) == set(brute) and len(accepted) == 3
    assert compatible(R, [1, 2]) and not compatible(R, [2, 2])
    after = audit.hashes()
    assert before == after
    output = {"protected_hashes_before": before, "protected_hashes_after": after,
              "protected_artifacts_unchanged": True,
              "matrix_boundary_and_counterexample_cases": results,
              "vectorization_and_unequal_fiber_triangle": {
                  "n": n, "quotient_order": t, "R": R,
                  "K_dimension": len(K), "right_corank": len(C),
                  "right_vectors_enumerated": len(images),
                  "full_block_vectors_not_enumerated": 5**(2*len(C)),
                  "exact_one_hot_intertwiners": accepted,
                  "matches_brute_assignment_search": True,
                  "equal_size_quotient_rejected_by_integer_balance": True,
                  "column_vectorization_and_transpose_checked": True,
                  "stats": stats}}
    (HERE/"intertwiner-checks.json").write_text(json.dumps(output, indent=2)+"\n")
    (HERE/"intertwiner-example-certificate.json").write_text(
        json.dumps({"A": A, "R": R, "K": K, "certificate": cert}, indent=2)+"\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
