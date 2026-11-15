from pathlib import Path
import hashlib
import json
import resource
import time

import numpy as np
import scipy
from scipy import sparse
from scipy.sparse.linalg import eigsh, splu
from scipy.sparse.csgraph import connected_components


def regular_graph(n, seed):
    rng = np.random.default_rng(seed)
    stubs = np.repeat(np.arange(n), 3)
    for attempt in range(500):
        pairs = rng.permutation(stubs).reshape(-1, 2)
        if np.any(pairs[:, 0] == pairs[:, 1]):
            continue
        pairs.sort(axis=1)
        if len(np.unique(pairs, axis=0)) != len(pairs):
            continue
        rows = np.concatenate((pairs[:, 0], pairs[:, 1]))
        cols = np.concatenate((pairs[:, 1], pairs[:, 0]))
        adjacency = sparse.csr_matrix((np.ones(len(rows)), (rows, cols)),
                                      shape=(n, n))
        if connected_components(adjacency, directed=False)[0] != 1:
            raise RuntimeError("A sampled simple graph was disconnected")
        return adjacency, attempt + 1
    raise RuntimeError("Bounded simple-configuration rejection limit reached")


def motif(name):
    if name == "duplication":
        return np.zeros((1, 1)), np.ones(1), 8.0, 1.0 / 8
    if name == "triangle":
        return np.ones((3, 3)) - np.eye(3), np.array([1., 1., 0.]), 31.0 / 18, 11.0 / 31
    center = np.zeros((8, 8))
    center[0, 1:] = 1
    center[1:, 0] = 1
    port = np.zeros(8)
    port[0] = 1
    return center, port, 26.0 / 9, 8.0 / 13


def check_case(n, seed):
    adjacency, attempts = regular_graph(n, seed)
    m = round(n ** (1.0 / 3))
    scale = np.sqrt(m / n)
    inclusion = sparse.csr_matrix((np.ones(m), (np.arange(m), np.arange(m))),
                                  shape=(n, m))
    unit = np.ones(n) / np.sqrt(n)
    laplacian = 3 * sparse.eye(n, format="csc") - adjacency
    grounded = splu(laplacian[:-1, :-1].tocsc())
    records = []
    for name in ("duplication", "triangle", "star7"):
        internal, port, metric, eta = motif(name)
        coupling = adjacency @ inclusion if name == "duplication" else inclusion
        dense_coupling = coupling.toarray()
        projected = dense_coupling - np.outer(unit, unit @ dense_coupling)
        response = np.zeros((n, m))
        response[:-1] = grounded.solve(projected[:-1])
        response -= response.mean(axis=0)
        inverse_port = np.linalg.solve(3 * np.eye(len(port)) - internal, port)
        f = float(port @ inverse_port)
        motif_lift = inverse_port / f
        retained_f = np.eye(m) / f - dense_coupling.T @ response
        retained = np.zeros((m + 1, m + 1))
        retained[0, 1:] = (unit @ dense_coupling) / (scale * np.sqrt(metric))
        retained[1:, 0] = retained[0, 1:]
        retained[1:, 1:] = -retained_f / (metric * scale)
        port_copies = sparse.kron(sparse.eye(m), sparse.csr_matrix(port[None, :]))
        physical_coupling = coupling @ port_copies
        augmented = sparse.bmat([
            [adjacency, physical_coupling],
            [physical_coupling.T, sparse.kron(sparse.eye(m), internal)]
        ], format="csr")
        lift = np.zeros((augmented.shape[0], m + 1))
        lift[:n, 0] = unit
        lift[:n, 1:] = response / np.sqrt(metric)
        lift[n:, 1:] = np.kron(np.eye(m), motif_lift[:, None]) / np.sqrt(metric)
        companion = np.zeros_like(lift)
        companion[:n, 0] = unit
        companion[n:, 1:] = np.sqrt(metric) * np.kron(np.eye(m), port[:, None])
        derivative = float(motif_lift @ motif_lift) * np.eye(m) + response.T @ response
        gram_target = np.zeros((m + 1, m + 1))
        gram_target[0, 0] = 1
        gram_target[1:, 1:] = derivative / metric
        residual = augmented @ lift - 3 * lift
        errors = {
            "host_projected_inverse": float(np.linalg.norm(laplacian @ response - projected)),
            "exact_gram": float(np.linalg.norm(lift.T @ lift - gram_target)),
            "exact_graph_action": float(np.linalg.norm(residual - scale * companion @ retained)),
            "exact_compression": float(np.linalg.norm(lift.T @ residual / scale - retained)),
            "exact_duality": float(np.linalg.norm(lift.T @ companion - np.eye(m + 1))),
            "motif_mass": abs(float(motif_lift @ motif_lift) / metric - eta)
        }
        assert max(errors.values()) < 1e-9, (n, seed, name, errors)
        values, vectors = eigsh(augmented, k=m + 2, which="LA", tol=1e-11,
                               maxiter=20000, v0=np.linspace(1., 2., augmented.shape[0]))
        order = np.argsort(values)[::-1]
        values = values[order]
        vectors = vectors[:, order]
        prediction = np.linalg.eigvalsh(retained)[::-1]
        actual = (values[:m + 1] - 3) / scale
        records.append({
            "motif": name,
            "dimension": augmented.shape[0],
            "identity_errors": errors,
            "retained_linearization_max_error": float(np.max(np.abs(actual - prediction))),
            "top_normalized": float(actual[0]),
            "retained_top": float(prediction[0]),
            "cluster_to_next_gap": float(values[m] - values[m + 1]),
            "top_constant_host_mass": float((unit @ vectors[:n, 0]) ** 2),
            "top_motif_mass": float(np.sum(vectors[n:, 0] ** 2))
        })
    independent_marks = (inclusion.T @ adjacency @ inclusion).nnz == 0
    compact = None
    if independent_marks:
        signed_coupling = laplacian @ inclusion
        signed = sparse.bmat([[adjacency, signed_coupling],
                              [signed_coupling.T, sparse.csr_matrix((m, m))]], format="csr")
        compact_modes = np.vstack((inclusion.toarray(), np.eye(m)))
        constant_mode = np.concatenate((unit, np.zeros(m)))[:, None]
        modes = np.hstack((constant_mode, compact_modes))
        compact = {
            "residual": float(np.linalg.norm(signed @ modes - 3 * modes)),
            "rank": int(np.linalg.matrix_rank(modes)),
            "expected_rank": m + 1
        }
        assert compact["residual"] < 1e-10 and compact["rank"] == m + 1
    return {"n": n, "m": m, "seed": seed, "configuration_attempts": attempts,
            "independent_marks": independent_marks, "cases": records,
            "compact_cancellation": compact}


def main():
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024 ** 3, 4 * 1024 ** 3))
    resource.setrlimit(resource.RLIMIT_CPU, (170, 175))
    start = time.monotonic()
    results = [check_case(n, seed) for n in (512, 1024, 2048) for seed in (17, 41)]
    output = {
        "scope": "Finite random-graph diagnostics of exact attachment identities and linearization. These samples do not establish an asymptotic law.",
        "numpy_version": np.__version__,
        "scipy_version": scipy.__version__,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "elapsed_seconds": round(time.monotonic() - start, 3),
        "memory_bound_bytes": 4 * 1024 ** 3,
        "cpu_bound_seconds": 170,
        "results": results
    }
    path = Path(__file__).with_name("graph-diagnostic-v1.json")
    path.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"cases": sum(len(x["cases"]) for x in results),
                      "compact_cases": sum(x["compact_cancellation"] is not None for x in results),
                      "max_identity_error": max(max(y["identity_errors"].values()) for x in results for y in x["cases"]),
                      "elapsed_seconds": output["elapsed_seconds"]}))


if __name__ == "__main__":
    main()
