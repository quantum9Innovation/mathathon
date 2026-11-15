import json
import math
from pathlib import Path

out = {}

# The complete 3-uniform hypergraph on six vertices has A = 4(J-I).
n = 6
off_diagonal = math.comb(n - 2, 3 - 2)
eigenvalues = [off_diagonal * (n - 1)] + [-off_diagonal] * (n - 1)
out["complete_3_uniform_6"] = {
    "vertex_hyperedge_degree": math.comb(n - 1, 2),
    "eigenvalues": eigenvalues,
    "perron_multiplicity": sum(x == max(eigenvalues) for x in eigenvalues),
}

# Exact sequence for a square two-dimensional 4-regular lattice torus.
side = 10
torus = sorted(
    (2 * math.cos(2 * math.pi * a / side) + 2 * math.cos(2 * math.pi * b / side)
     for a in range(side) for b in range(side)),
    reverse=True,
)
out["square_torus_10"] = {
    "vertices": side**2,
    "lambda_1": torus[0],
    "lambda_2": torus[1],
    "adjacency_gap": torus[0] - torus[1],
    "times_side_squared": side**2 * (torus[0] - torus[1]),
}

# Check the exact center secular equation and the regular branch equations.
def defect_value(d, delta):
    q = 1 / math.sqrt(delta - d + 1)
    nu = delta / math.sqrt(delta - d + 1)
    return {
        "degree": delta,
        "nu": nu,
        "center_residual": nu - delta * q,
        "branch_residual": nu - (1 / q + (d - 1) * q),
        "radial_l2_parameter_before_branching": (d - 1) * q**2,
        "bulk": 2 * math.sqrt(d - 1),
    }

out["single_center_degree_defect"] = [defect_value(4, 5), defect_value(3, 5)]
path = Path(__file__).with_suffix(".json")
path.write_text(json.dumps(out, indent=2) + "\n")
print(path)
