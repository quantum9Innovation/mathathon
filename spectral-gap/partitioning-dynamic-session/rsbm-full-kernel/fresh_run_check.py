#!/usr/bin/env python3
"""Fresh independent audit. Does not modify the prototype or manuscript."""
from pathlib import Path
import contextlib
import copy
import hashlib
import importlib.util
import io
import itertools
import json
import random
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "full_kernel.py"
PROTECTED = [SOURCE, ROOT / "certified-full-kernel.tex",
             ROOT / "full-kernel-checks.json",
             ROOT / "full-kernel-example-certificate.json",
             ROOT / "unique-degenerate-example-certificate.json"]


def hashes():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in PROTECTED}


def load_prototype():
    spec = importlib.util.spec_from_file_location("independently_audited_full_kernel", SOURCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rref(rows, p, width=None):
    """Independent dense base-field reference; not used by recovery."""
    A = [[a % p for a in row] for row in rows]
    width = len(A[0]) if A else (0 if width is None else width)
    assert all(len(row) == width for row in A)
    pivots = []
    for j in range(width):
        at = len(pivots)
        found = next((i for i in range(at, len(A)) if A[i][j]), None)
        if found is None:
            continue
        A[at], A[found] = A[found], A[at]
        inv = pow(A[at][j], -1, p)
        A[at] = [a * inv % p for a in A[at]]
        for i in range(len(A)):
            if i != at and A[i][j]:
                factor = A[i][j]
                A[i] = [(a - factor * b) % p for a, b in zip(A[i], A[at])]
        pivots.append(j)
        if len(pivots) == len(A):
            break
    return A[:len(pivots)], pivots


def gauss_kernel(M, p):
    reduced, pivots = rref(M, p)
    n = len(M[0])
    free = [i for i in range(n) if i not in pivots]
    columns = []
    for j in free:
        v = [0] * n
        v[j] = 1
        for row, pivot in zip(reduced, pivots):
            v[pivot] = -row[j] % p
        columns.append(v)
    return columns, len(pivots)


def span_signature(columns, n, p):
    return tuple(tuple(row) for row in rref(columns, p, n)[0])


def invertible(n, p, rng):
    while True:
        U = [[rng.randrange(p) for _ in range(n)] for _ in range(n)]
        if len(rref(U, p)[1]) == n:
            return U


def symmetric_rank(n, k, p, rng):
    U = invertible(n, p, rng)
    d = [rng.randrange(1, p) for _ in range(k)]
    return [[sum(d[a] * U[a][i] * U[a][j] for a in range(k)) % p
             for j in range(n)] for i in range(n)]


def nonsymmetric_rank(n, k, p, rng):
    U, V = invertible(n, p, rng), invertible(n, p, rng)
    return [[sum(U[i][a] * V[a][j] for a in range(k)) % p
             for j in range(n)] for i in range(n)]


def symmetrize(K):
    n = len(K)
    return [[0] * n + row[:] for row in K] + [
        [K[i][j] for i in range(n)] + [0] * n for j in range(n)]


def run_original(fk):
    """Run the unchanged original test function, redirecting only outputs."""
    target = ROOT / "fresh-original-run"
    target.mkdir(exist_ok=True)
    filenames = {"full-kernel-checks.json", "full-kernel-example-certificate.json",
                 "unique-degenerate-example-certificate.json"}
    original_write = Path.write_text
    redirected = []
    def audit_write(path, *args, **kwargs):
        if path.parent.resolve() != ROOT or path.name not in filenames:
            raise RuntimeError(f"Unexpected original-test write: {path}")
        dest = target / path.name
        redirected.append(str(dest.relative_to(ROOT)))
        return original_write(dest, *args, **kwargs)
    stdout = io.StringIO()
    Path.write_text = audit_write
    try:
        with contextlib.redirect_stdout(stdout):
            fk.run_checks()
    finally:
        Path.write_text = original_write
    (target / "stdout.json").write_text(stdout.getvalue())
    output = json.loads(stdout.getvalue())
    return {"passed": True, "redirected_outputs": redirected,
            "rank_lower_bound_checks": output["rank_lower_bound_checks"],
            "symmetric_cases": len(output["full_kernel_cases"]),
            "unique_degenerate_partition_count": output[
                "unique_partition_despite_real_nullity_two"][
                    "exact_admissible_partitions_up_to_exchange"]}


def tampered_certificates(cert, n):
    bad = copy.deepcopy(cert)
    bad["ell"] = (bad["ell"] + 1) % (n + 1)
    yield "rank", bad
    bad = copy.deepcopy(cert)
    bad["D"][0] = 0
    yield "zero_diagonal", bad
    bad = copy.deepcopy(cert)
    bad["D"][0] = cert["p"] ** (len(cert["h"]) - 1)
    yield "oversize_field_element", bad
    bad = copy.deepcopy(cert)
    bad["u"][0] = cert["p"] ** (len(cert["h"]) - 1)
    yield "oversize_probe", bad
    bad = copy.deepcopy(cert)
    bad["h"] = [0] * (len(cert["h"]) - 1) + [1]
    yield "reducible_polynomial", bad
    bad = copy.deepcopy(cert)
    bad["h"] = cert["h"][:-1]
    yield "wrong_field_degree", bad
    bad = copy.deepcopy(cert)
    bad["p"] = 9
    yield "wrong_prime", bad
    if cert["ell"]:
        bad = copy.deepcopy(cert)
        bad["u"] = [0] * n
        yield "zero_probe_nonzero_rank", bad
    if cert["columns"]:
        bad = copy.deepcopy(cert)
        bad["columns"][0][cert["pivots"][0]] = 0
        yield "identity_pivot_corruption", bad
        bad = copy.deepcopy(cert)
        bad["pivots"][0] = n
        yield "out_of_range_pivot", bad
        # This stays a correctly normalized *partial* kernel basis.
        # Only the shifted lower-rank certificate detects incompleteness.
        bad = copy.deepcopy(cert)
        bad["columns"].pop()
        bad["pivots"].pop()
        bad["ell"] += 1
        yield "incomplete_basis_with_consistent_dimensions", bad
        nonpivots = [j for j in range(n) if j not in cert["pivots"]]
        if nonpivots:
            bad = copy.deepcopy(cert)
            j = nonpivots[0]
            bad["columns"][0][j] = (bad["columns"][0][j] + 1) % cert["p"]
            yield "residual_corruption_preserving_pivots", bad
    if len(cert["pivots"]) >= 2:
        bad = copy.deepcopy(cert)
        bad["pivots"][1] = bad["pivots"][0]
        yield "duplicate_pivots", bad


def verify_right(fk, K, cert, p):
    """Deterministic right-kernel verifier using only a symmetric rank lower bound."""
    try:
        n = len(K)
        if not n or any(len(row) != n for row in K) or cert["p"] != p:
            return False
        S = symmetrize(K)
        rows = fk.rows_from_dense(S, p)
        fk.check_input(rows, p)
        s, q = fk.extension_degree(p, 2 * n)
        if len(cert["h"]) != s + 1 or not fk.irreducible(cert["h"], p):
            return False
        F = fk.Field(p, cert["h"])
        D, u, v = cert["D"], cert["u"], cert["v"]
        if not (len(D) == len(u) == len(v) == 2 * n):
            return False
        if not all(0 < x < q for x in D) or not all(0 <= x < q for x in u + v):
            return False
        columns, pivots, ell = cert["columns"], cert["pivots"], cert["ell"]
        h = len(columns)
        if not (0 <= h <= n and ell == 2 * (n - h) and len(pivots) == h):
            return False
        if len(set(pivots)) != h or not all(0 <= i < n for i in pivots):
            return False
        for j, col in enumerate(columns):
            if len(col) != n or not all(0 <= x < p for x in col):
                return False
            if any(col[pivot] != int(i == j) for i, pivot in enumerate(pivots)):
                return False
            if any(sum(a * x for a, x in zip(row, col)) % p for row in K):
                return False
        seq, _ = fk.sequence(rows, D, u, v, F)
        ell_actual, _ = fk.bm(seq, F)
        return ell_actual == ell
    except (AssertionError, KeyError, IndexError, ValueError, TypeError, ZeroDivisionError):
        return False


def main():
    before = hashes()
    fk = load_prototype()
    start = time.perf_counter()
    original = run_original(fk)
    rng = random.Random(779301183)
    cases, tamper_counts = [], {}
    seed = 829001
    for p, max_n, repeats in [(3, 8, 2), (5, 6, 1)]:
        for n in range(1, max_n + 1):
            for k in range(n + 1):
                for rep in range(repeats):
                    M = symmetric_rank(n, k, p, rng)
                    reference, rank = gauss_kernel(M, p)
                    assert rank == k
                    rows = fk.rows_from_dense(M, p)
                    columns, cert, stats = fk.kernel_basis(rows, p, seed=seed)
                    seed += 1
                    assert fk.verify(rows, cert, p)
                    assert span_signature(columns, n, p) == span_signature(reference, n, p)
                    assert len(columns) == n - rank
                    for category, bad in tampered_certificates(cert, n):
                        assert not fk.verify(rows, bad, p), (category, p, n, k)
                        tamper_counts[category] = tamper_counts.get(category, 0) + 1
                    cases.append({"p": p, "n": n, "rank": k, "corank": n-k,
                                  "basis_equals_independent_gauss": True,
                                  "trials": stats["trials"]})
    nilpotent = []
    for p, n in [(3, 3), (3, 6), (3, 9), (5, 5)]:
        M = [[1] * n for _ in range(n)]
        assert all(sum(M[i][a] * M[a][j] for a in range(n)) % p == 0
                   for i in range(n) for j in range(n))
        rows = fk.rows_from_dense(M, p)
        columns, cert, stats = fk.kernel_basis(rows, p, seed=seed)
        seed += 1
        reference, rank = gauss_kernel(M, p)
        assert rank == 1 and len(columns) == n-1 and fk.verify(rows, cert, p)
        assert span_signature(columns, n, p) == span_signature(reference, n, p)
        nilpotent.append({"p": p, "n": n, "corank": n-1, "certified": True})
    fixtures = []
    for name in ["full-kernel-example-certificate.json", "unique-degenerate-example-certificate.json"]:
        saved = json.loads((ROOT / name).read_text())
        cert = saved["certificate"]
        p = cert["p"]
        rows = fk.rows_from_dense(saved["integer_matrix"], p)
        assert fk.verify(rows, cert, p)
        reference, rank = gauss_kernel(saved["integer_matrix"], p)
        assert span_signature(cert["columns"], len(rows), p) == span_signature(reference, len(rows), p)
        fixtures.append({"name": name, "certified": True, "rank": rank,
                         "corank": len(rows)-rank})
    nonsym, right_tampers = [], 0
    for n in range(1, 7):
        for k in range(n + 1):
            K = nonsymmetric_rank(n, k, 3, rng)
            reference, rank = gauss_kernel(K, 3)
            assert rank == k
            S = symmetrize(K)
            assert len(rref(S, 3)[1]) == 2 * k
            rows = fk.rows_from_dense(S, 3)
            full_columns, full_cert, stats = fk.kernel_basis(rows, 3, seed=seed)
            seed += 1
            assert fk.verify(rows, full_cert, 3)
            assert len(full_columns) == 2 * (n-k)
            # RREF of projected columns gives a canonical column basis.
            projected = [col[n:] for col in full_columns]
            right_columns, pivots = rref(projected, 3, n)
            h = len(right_columns)
            assert h == n-k
            assert span_signature(right_columns, n, 3) == span_signature(reference, n, 3)
            cert = {key: copy.deepcopy(full_cert[key]) for key in ["p", "h", "D", "u", "v", "ell"]}
            cert["columns"], cert["pivots"] = right_columns, pivots
            assert verify_right(fk, K, cert, 3)
            bad = copy.deepcopy(cert)
            bad["ell"] += 1
            assert not verify_right(fk, K, bad, 3)
            right_tampers += 1
            bad = copy.deepcopy(cert)
            bad["D"][0] = 0
            assert not verify_right(fk, K, bad, 3)
            right_tampers += 1
            if h:
                bad = copy.deepcopy(cert)
                bad["columns"].pop()
                bad["pivots"].pop()
                bad["ell"] += 2
                assert not verify_right(fk, K, bad, 3)
                right_tampers += 1
                bad = copy.deepcopy(cert)
                bad["columns"][0][pivots[0]] = 0
                assert not verify_right(fk, K, bad, 3)
                right_tampers += 1
            images = list(fk.enumerate_kernel(right_columns, n, 3))
            assert len(images) == 3**h and len({tuple(x) for x in images}) == 3**h
            assert all(all(sum(a*b for a,b in zip(row, x)) % 3 == 0 for row in K)
                       for x in images)
            if n <= 4:
                brute = {v for v in itertools.product(range(3), repeat=n)
                         if all(sum(a*b for a,b in zip(row, v)) % 3 == 0 for row in K)}
                assert {tuple(x) for x in images} == brute
            nonsym.append({"n": n, "rank_K": k, "corank_K": h,
                           "rank_symmetric_dilation": 2*k,
                           "symmetric_corank": 2*h,
                           "right_basis_equals_gauss": True,
                           "right_certificate_valid": True,
                           "enumerated_only_right_kernel_vectors": 3**h,
                           "avoided_full_dilation_enumeration": 3**(2*h)})
    after = hashes()
    assert before == after, "Protected existing files changed"
    result = {"status": "PASS", "protected_hashes_before": before,
              "protected_hashes_after": after, "protected_files_unchanged": True,
              "original_tests_fresh_run": original,
              "additional_symmetric_cases": cases,
              "additional_nilpotent_cases": nilpotent,
              "saved_certificates_reverified": fixtures,
              "tampered_symmetric_certificates_rejected_by_category": tamper_counts,
              "symmetric_tamper_rejection_total": sum(tamper_counts.values()),
              "nonsymmetric_square_dilation_cases": nonsym,
              "right_kernel_tamper_rejections": right_tampers,
              "elapsed_seconds_including_original_tests": time.perf_counter()-start}
    (ROOT / "fresh-independent-checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "protected_files_unchanged": True,
                      "symmetric_cases": len(cases), "nilpotent_cases": len(nilpotent),
                      "symmetric_tamper_rejections": sum(tamper_counts.values()),
                      "nonsymmetric_dilation_cases": len(nonsym),
                      "right_kernel_tamper_rejections": right_tampers,
                      "elapsed_seconds": result["elapsed_seconds_including_original_tests"]}, indent=2))


if __name__ == "__main__":
    main()
