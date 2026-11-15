"""Independent kernel/span/certificate checks; no rank oracle in the solver."""
from pathlib import Path
import copy
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("packet_full_kernel", HERE/"full_kernel.py")
fk = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fk)


def rref(rows, width, p):
    rows = [[x % p for x in row] for row in rows]
    pivots = []
    for j in range(width):
        at = len(pivots)
        found = next((i for i in range(at, len(rows)) if rows[i][j]), None)
        if found is None:
            continue
        rows[at], rows[found] = rows[found], rows[at]
        inverse = pow(rows[at][j], -1, p)
        rows[at] = [inverse*x % p for x in rows[at]]
        for i in range(len(rows)):
            if i != at:
                coefficient = rows[i][j]
                rows[i] = [(x-coefficient*y) % p
                           for x, y in zip(rows[i], rows[at])]
        pivots.append(j)
        if len(pivots) == len(rows):
            break
    return rows[:len(pivots)], pivots


def reference_kernel(matrix, p):
    reduced, pivots = rref(matrix, len(matrix), p)
    columns = []
    for j in range(len(matrix)):
        if j not in pivots:
            column = [int(i == j) for i in range(len(matrix))]
            for row, at in zip(reduced, pivots):
                column[at] = -row[j] % p
            columns.append(column)
    return columns


def same_span(a, b, n, p):
    return rref(a, n, p)[0] == rref(b, n, p)[0]


def double(matrix):
    n = len(matrix)
    return [[0]*n+row[:] for row in matrix]+[
        [matrix[i][j] for i in range(n)]+[0]*n for j in range(n)]


def right_verify(matrix, cert, p):
    n = len(matrix)
    try:
        srows = fk.rows_from_dense(double(matrix), p)
        s, q = fk.extension_degree(p, 2*n)
        if cert["p"] != p or len(cert["h"]) != s+1:
            return False
        if not fk.irreducible(cert["h"], p):
            return False
        field = fk.Field(p, cert["h"])
        if any(len(cert[key]) != 2*n for key in ["D", "u", "v"]):
            return False
        if not all(0 < x < q for x in cert["D"]):
            return False
        if not all(0 <= x < q for x in cert["u"]+cert["v"]):
            return False
        columns, pivots = cert["columns"], cert["pivots"]
        h = len(columns)
        if len(pivots) != h or len(set(pivots)) != h:
            return False
        if any(not 0 <= j < n for j in pivots):
            return False
        if cert["ell"] != 2*(n-h):
            return False
        for j, column in enumerate(columns):
            if len(column) != n or any(not 0 <= x < p for x in column):
                return False
            if any(column[at] != int(i == j) for i, at in enumerate(pivots)):
                return False
            if any(sum(x*y for x, y in zip(row, column)) % p for row in matrix):
                return False
        sequence, _ = fk.sequence(srows, cert["D"], cert["u"], cert["v"], field)
        return fk.bm(sequence, field)[0] == cert["ell"]
    except (KeyError, TypeError, IndexError, ValueError, ZeroDivisionError):
        return False


def main():
    p = 3
    symmetric = [
        ("zero", [[0]*3 for _ in range(3)]),
        ("identity", [[int(i == j) for j in range(3)] for i in range(3)]),
        ("nilpotent", [[1]*3 for _ in range(3)]),
        ("corank_two", [[1, 0, 0], [0, 0, 0], [0, 0, 0]]),
    ]
    report = []
    for seed, (name, matrix) in enumerate(symmetric, 921):
        rows = fk.rows_from_dense(matrix, p)
        columns, cert, _ = fk.kernel_basis(rows, p, seed=seed)
        assert fk.verify(rows, cert, p)
        assert same_span(columns, reference_kernel(matrix, p), len(matrix), p)
        wrong = copy.deepcopy(cert)
        wrong["ell"] = (wrong["ell"]+1) % (len(matrix)+1)
        assert not fk.verify(rows, wrong, p)
        images = list(fk.enumerate_kernel(columns, len(matrix), p))
        assert len({tuple(x) for x in images}) == p**len(columns)
        report.append({"kind": "symmetric", "case": name,
                       "nullity": len(columns), "status": "PASS"})
    nonsymmetric = [
        ("nilpotent_jordan", [[0, 1, 0], [0, 0, 1], [0, 0, 0]]),
        ("different_left_right", [[0, 1], [0, 0]]),
        ("zero", [[0]*3 for _ in range(3)]),
        ("invertible", [[1, 1], [0, 1]]),
        ("isotropic_gram", [[1, 0, 0], [1, 0, 0], [1, 0, 0]]),
    ]
    for seed, (name, matrix) in enumerate(nonsymmetric, 1741):
        n = len(matrix)
        full, full_cert, _ = fk.kernel_basis(fk.rows_from_dense(double(matrix), p),
                                           p, seed=seed)
        projected = [column[n:] for column in full]
        # Independently reduce the projected spanning vectors.
        columns, _ = rref(projected, n, p)
        reference = reference_kernel(matrix, p)
        assert len(full) == 2*len(columns)
        assert same_span(columns, reference, n, p)
        # Choose coordinate pivots and normalize columns to identity there.
        field = fk.Field(p, [0, 1])
        normalized, pivots = [], []
        for column in columns:
            fk.insert_canonical(column, normalized, pivots, field)
        cert = {key: copy.deepcopy(full_cert[key])
                for key in ["p", "h", "D", "u", "v", "ell"]}
        cert["columns"], cert["pivots"] = normalized, pivots
        assert right_verify(matrix, cert, p)
        if normalized:
            bad = copy.deepcopy(cert)
            bad["columns"].pop()
            bad["pivots"].pop()
            bad["ell"] += 2
            assert not right_verify(matrix, bad, p)
        images = list(fk.enumerate_kernel(normalized, n, p))
        assert len({tuple(x) for x in images}) == p**len(normalized)
        assert all(not any(sum(a*b for a, b in zip(row, x)) % p
                           for row in matrix) for x in images)
        report.append({"kind": "right_projection", "case": name,
                       "right_nullity": len(normalized),
                       "enumerated": len(images), "status": "PASS"})
    output = {"status": "PASS", "cases": report,
              "tests_compare_to_independent_elimination": True,
              "incomplete_certificate_forgeries_rejected": True}
    (HERE/"linear-algebra-checks.json").write_text(json.dumps(output, indent=2)+"\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()

