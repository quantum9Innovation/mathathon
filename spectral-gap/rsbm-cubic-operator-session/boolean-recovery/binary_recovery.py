"""Exact bounded-runtime recovery of a prescribed-degree regular partition.

No planted labels, matching, cycles, or numerical eigensolver are used.
Both entry points use exponent 27, from the degree-independent polynomial
moment exponent 24 for fixed model degrees. They use exact XOR elimination
and integer crossing-degree verification.
Only the Python standard library is required.
"""

from dataclasses import dataclass
from typing import Iterator, Sequence


def validate_regular_graph(adjacency: Sequence[Sequence[int]], expected_degree: int | None = None) -> int:
    """Validate a simple regular graph of positive even order; return its degree."""
    n = len(adjacency)
    if n % 2 or n < 4:
        raise ValueError("The graph must have a positive even vertex count")
    degree = len(adjacency[0])
    if expected_degree is not None and degree != expected_degree:
        raise ValueError("The graph has the wrong degree")
    for i, neighbors in enumerate(adjacency):
        if len(neighbors) != degree or len(set(neighbors)) != degree:
            raise ValueError("Every vertex must have the same number of distinct neighbors")
        if any(j < 0 or j >= n or j == i for j in neighbors):
            raise ValueError("Invalid vertex index or self-loop")
    if any(i not in adjacency[j] for i, neighbors in enumerate(adjacency) for j in neighbors):
        raise ValueError("The graph must be undirected")
    return degree


def validate_cubic_graph(adjacency: Sequence[Sequence[int]]) -> None:
    """Reject inputs outside the promised simple cubic graph class."""
    validate_regular_graph(adjacency, expected_degree=3)


def binary_affine_space(adjacency: Sequence[Sequence[int]], rhs_parity: int = 1) -> tuple[int, list[int]]:
    """Return z0 and a basis for binary solutions of (A+dI)z=rhs_parity*1.

    Vectors are encoded as arbitrary-precision integers with bit i for vertex
    i. Elimination and back substitution use exact XOR and integer parity.
    The input is assumed to have passed validate_regular_graph. In the
    original cubic use d is odd and rhs_parity=1, giving (A+I)z=1.
    """
    n = len(adjacency)
    rhs_bit = 1 << n
    coefficient_mask = rhs_bit - 1
    rows = []
    for i, neighbors in enumerate(adjacency):
        row = rhs_bit if rhs_parity & 1 else 0
        if len(neighbors) & 1:
            row ^= 1 << i
        for j in neighbors:
            row ^= 1 << j
        rows.append(row)

    pivots = []
    rank = 0
    for column in range(n):
        column_bit = 1 << column
        pivot = next((i for i in range(rank, n) if rows[i] & column_bit), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        pivot_row = rows[rank]
        for i in range(rank + 1, n):
            if rows[i] & column_bit:
                rows[i] ^= pivot_row
        pivots.append(column)
        rank += 1

    if any((row & coefficient_mask) == 0 and row & rhs_bit for row in rows[rank:]):
        raise ValueError("The binary affine system is inconsistent")

    def back_substitute(initial: int, homogeneous: bool) -> int:
        value = initial
        for i in range(rank - 1, -1, -1):
            parity = (rows[i] & value & coefficient_mask).bit_count() & 1
            rhs = 0 if homogeneous else int(bool(rows[i] & rhs_bit))
            if parity != rhs:
                value |= 1 << pivots[i]
        return value

    pivot_set = set(pivots)
    particular = back_substitute(0, False)
    basis = [back_substitute(1 << j, True) for j in range(n) if j not in pivot_set]
    return particular, basis


def affine_labelings(particular: int, basis: Sequence[int]) -> Iterator[int]:
    """Enumerate the affine space in Gray-code order with one XOR per step."""
    current = particular
    yield current
    for i in range(1, 1 << len(basis)):
        changed_coordinate = (i & -i).bit_length() - 1
        current ^= basis[changed_coordinate]
        yield current


def is_prescribed_crossing_degree(adjacency: Sequence[Sequence[int]], labels: int, cross_degree: int) -> bool:
    """Check the integer local degree condition, not merely its binary parity."""
    # Convert once so each bit lookup has constant cost; repeatedly shifting
    # an arbitrary-precision labels integer at every vertex would obscure
    # the linear bit-operation bound for checking one candidate.
    packed = labels.to_bytes((len(adjacency) + 7) // 8, "little")

    def bit_at(i: int) -> int:
        return (packed[i >> 3] >> (i & 7)) & 1

    for i, neighbors in enumerate(adjacency):
        bit = bit_at(i)
        if sum(bit_at(j) != bit for j in neighbors) != cross_degree:
            return False
    return True


def is_perfect_matching_cut(adjacency: Sequence[Sequence[int]], labels: int) -> bool:
    return is_prescribed_crossing_degree(adjacency, labels, 1)


def canonical_partition(labels: int, vertex_count: int) -> int:
    """Identify global complementation of the two labels."""
    return min(labels, labels ^ ((1 << vertex_count) - 1))


@dataclass(frozen=True)
class RecoveryResult:
    status: str
    binary_nullity: int
    affine_candidates: int
    checked_candidates: int
    partition: int | None = None


def recover(adjacency: Sequence[Sequence[int]], cutoff_exponent: int = 27) -> RecoveryResult:
    """Recover the unique perfect matching cut, or return a certified failure.

    Status is one of ok, cutoff, no_partition, or multiple_partitions.
    The deterministic enumeration cutoff is (number_of_vertices/2)^27 by
    default. The cutoff is checked before enumerating any affine vectors.
    """
    validate_cubic_graph(adjacency)
    return _recover_validated(adjacency, 1, cutoff_exponent)


def recover_regular(adjacency: Sequence[Sequence[int]], cross_degree: int,
                    cutoff_exponent: int | None = None) -> RecoveryResult:
    """Recover a unique partition with prescribed positive crossing degree.

    The default enumeration cutoff is N^27, using the aggregate-fiber
    bound E|ker_F2(A+dI)|=O_(a,b)(N^24). The moment bound's constant
    depends on the fixed model degrees, while its exponent does not.
    An arbitrary unpromised input may have an inconsistent affine system.
    """
    degree = validate_regular_graph(adjacency)
    if not isinstance(cross_degree, int) or not 1 <= cross_degree <= degree:
        raise ValueError("The crossing degree must be an integer between 1 and d")
    if cutoff_exponent is None:
        cutoff_exponent = 27
    return _recover_validated(adjacency, cross_degree, cutoff_exponent)


def _recover_validated(adjacency: Sequence[Sequence[int]], cross_degree: int,
                       cutoff_exponent: int) -> RecoveryResult:
    if not isinstance(cutoff_exponent, int) or cutoff_exponent < 0:
        raise ValueError("The cutoff exponent must be a nonnegative integer")
    try:
        particular, basis = binary_affine_space(adjacency, rhs_parity=cross_degree & 1)
    except ValueError:
        return RecoveryResult("inconsistent", -1, 0, 0)
    k = len(basis)
    candidates = 1 << k
    # For N>=2 and cutoff_exponent>=2N, N^cutoff_exponent>=2^(2N)
    # already exceeds the whole binary cube. Avoid constructing an enormous
    # formal cutoff integer when the observed regular degree is large.
    exceeds_cutoff = (
        cutoff_exponent < len(adjacency)
        and candidates > (len(adjacency) // 2) ** cutoff_exponent
    )
    if exceeds_cutoff:
        return RecoveryResult("cutoff", k, candidates, 0)

    found = None
    checked = 0
    for labels in affine_labelings(particular, basis):
        checked += 1
        if not is_prescribed_crossing_degree(adjacency, labels, cross_degree):
            continue
        partition = canonical_partition(labels, len(adjacency))
        if found is not None and found != partition:
            return RecoveryResult("multiple_partitions", k, candidates, checked)
        found = partition

    if found is None:
        return RecoveryResult("no_partition", k, candidates, checked)
    return RecoveryResult("ok", k, candidates, checked, found)
