#!/usr/bin/env python3
"""Pinned finite probe of the same-policy KL defect automaton.

On a strict minimizing-policy cell, the nonlinear KL map is exactly linear.
If ``sigma(u)`` selects the minimum in ternary fiber ``u``, write the active
matrix as ``A_sigma``.  For two vectors in that same open policy cell,

    F(x) - F(y) = A_sigma (x-y).

The directed support graph of ``A_sigma`` is an honest defect automaton:

* every source coordinate has one transport successor;
* a source which is selected in its fiber has two additional branch
  successors, so a defect may split; and
* a branch output also has its transport input, so defects may merge.

This script asks whether that exact graph has a small quotient after retaining
the low 3-adic carry state, source digit, minimizing policy, and sibling order.
It also records recurrence/split/merge data in the zero-charge complement of
the inherited exceptional balls.

All source, indexing, policy, SCC, partition-refinement, and sibling-gap claims
are exact finite computations on the SHA-pinned portable k=12 certificate.
The restricted Perron radii are explicitly floating diagnostics and are not
certificates.  The conclusion is a scoped no-go: the natural deterministic
state refinement recovers essentially the entire coordinate set, and exact
projective sibling-gap data are unique fiber by fiber.  This does not rule out
a different finite conditional cone or a non-deterministic/statistical
compression.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components


HERE = Path(__file__).resolve().parent
LEVEL = 12
MANIFEST = HERE / "cert_k12.json"
EXPECTED_MANIFEST_SHA256 = (
    "a6386bfc8d0410a3dd82a98d765690e53c620259e6b7c4a5359f150ce6d1459f"
)
EXPECTED_POLICY_COUNTS = (20_037, 19_545, 19_467)
EXPECTED_ZERO_CHARGE = {
    3: {
        "kept_nodes": 118_098,
        "kept_edges": 150_903,
        "restricted_sccs": 81_017,
        "largest_scc": 37_082,
        "cyclic_nodes": 37_083,
        "split_nodes_in_largest": 19_223,
        "merge_nodes_in_largest": 12_990,
    },
    4: {
        "kept_nodes": 150_903,
        "kept_edges": 229_635,
        "restricted_sccs": 34_046,
        "largest_scc": 116_858,
        "cyclic_nodes": 116_858,
        "split_nodes_in_largest": 43_979,
        "merge_nodes_in_largest": 64_212,
    },
    5: {
        "kept_nodes": 166_212,
        "kept_edges": 267_543,
        "restricted_sccs": 11_245,
        "largest_scc": 154_968,
        "cyclic_nodes": 154_968,
        "split_nodes_in_largest": 53_200,
        "merge_nodes_in_largest": 97_720,
    },
}
EXPECTED_POLICY_REFINEMENT = (
    81,
    5_276,
    57_306,
    96_549,
    134_040,
    161_680,
    173_871,
    176_464,
)
EXPECTED_ORDER_REFINEMENT = (
    162,
    28_214,
    84_090,
    131_567,
    165_355,
    175_338,
    176_973,
    177_119,
)

BRANCH_2 = 2
NEUTRAL = 5
BRANCH_8 = 8


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(8 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def branch_type(index: int) -> int:
    return (BRANCH_2, NEUTRAL, BRANCH_8)[index % 3]


def transport_source(row: int, size: int) -> int:
    """Source read by the transport term in output ``row``."""

    return (4 * row + 2) % size


def transport_successor(source: int, size: int) -> int:
    """Unique output row receiving the transport defect from ``source``."""

    return (pow(4, -1, size) * (source - 2)) % size


def branch_target(row: int, size: int) -> int:
    """Parent index of the branch-source fiber read by output ``row``."""

    parent_size = size // 3
    kind = branch_type(row)
    if kind == BRANCH_2:
        return (4 * (row // 3)) % parent_size
    if kind == BRANCH_8:
        return (2 * ((row - 2) // 3) + 1) % parent_size
    raise ValueError("neutral rows have no branch target")


def branch_successors(parent: int, size: int) -> tuple[int, int]:
    """The type-2 and type-8 outputs reading the selected child of ``parent``."""

    parent_size = size // 3
    row_2 = 3 * ((pow(4, -1, parent_size) * parent) % parent_size)
    row_8 = (
        3 * ((pow(2, -1, parent_size) * ((parent - 1) % parent_size)) % parent_size)
        + 2
    )
    return row_2, row_8


def slow_transport_source(row: int, level: int) -> int:
    modulus = 3**level
    state = 2 + 3 * row
    source = (4 * state) % modulus
    if source % 3 != 2:
        raise AssertionError("transport left the state class")
    return (source - 2) // 3


def slow_branch_target(row: int, level: int) -> int:
    modulus = 3**level
    coarse_modulus = modulus // 3
    state = 2 + 3 * row
    if state % 9 == BRANCH_2:
        target = ((4 * state - 2) // 3) % coarse_modulus
    elif state % 9 == BRANCH_8:
        target = ((2 * state - 1) // 3) % coarse_modulus
    else:
        raise ValueError("neutral rows have no branch target")
    if target % 3 != 2:
        raise AssertionError("branch target left the state class")
    return (target - 2) // 3


def verify_indexing(first_level: int = 2, last_level: int = 8) -> None:
    for level in range(first_level, last_level + 1):
        size = 3 ** (level - 1)
        for row in range(size):
            source = transport_source(row, size)
            if source != slow_transport_source(row, level):
                raise AssertionError("closed transport formula failed")
            if transport_successor(source, size) != row:
                raise AssertionError("transport inverse formula failed")
            if branch_type(row) != NEUTRAL:
                parent = branch_target(row, size)
                if parent != slow_branch_target(row, level):
                    raise AssertionError("closed branch formula failed")
                row_2, row_8 = branch_successors(parent, size)
                expected = row_2 if branch_type(row) == BRANCH_2 else row_8
                if expected != row:
                    raise AssertionError("branch inverse formula failed")


def load_record() -> tuple[dict[str, object], np.ndarray]:
    actual_hash = sha256(MANIFEST)
    if actual_hash != EXPECTED_MANIFEST_SHA256:
        raise AssertionError(f"k=12 manifest hash mismatch: {actual_hash}")
    manifest = json.loads(MANIFEST.read_text())
    if int(manifest["k"]) != LEVEL:
        raise AssertionError("manifest level changed")
    raw = manifest.get("C")
    if not isinstance(raw, list):
        raise AssertionError("portable k=12 vector is missing")
    vector = np.asarray(raw, dtype=np.int64)
    if vector.shape != (3 ** (LEVEL - 1),) or np.any(vector <= 0):
        raise AssertionError("k=12 vector has the wrong shape or sign")
    return manifest, vector


def exact_policy_retention(
    manifest: dict[str, object], vector: np.ndarray, policy: np.ndarray
) -> None:
    """Check that one rationally tightened KL step stays in the same cell."""

    size = len(vector)
    parent_size = size // 3
    children = vector.reshape(3, parent_size)
    minima = np.minimum(np.minimum(children[0], children[1]), children[2])
    lambda_numerator = int(manifest["A"])
    lambda_scale = int(manifest["SC_L"])
    weight_scale = int(manifest["SC_W"])
    transport_numerator = lambda_scale * lambda_scale * weight_scale
    branch_numerators = {
        BRANCH_2: int(manifest["B2"]) * lambda_numerator * lambda_numerator,
        BRANCH_8: int(manifest["B8"]) * lambda_numerator * lambda_numerator,
    }

    for parent in range(parent_size):
        outputs: list[int] = []
        for digit in range(3):
            row = parent + digit * parent_size
            value = (
                transport_numerator
                * int(vector[transport_source(row, size)])
            )
            kind = branch_type(row)
            if kind != NEUTRAL:
                value += (
                    branch_numerators[kind]
                    * int(minima[branch_target(row, size)])
                )
            outputs.append(value)
        output_policy = min(range(3), key=outputs.__getitem__)
        if output_policy != int(policy[parent]):
            raise AssertionError("rational active step changed a minimizing label")


def exceptional_set(depth: int) -> set[int]:
    modulus = 3**depth
    inverse_four = pow(4, -1, modulus)
    point = (-1) % modulus
    result: set[int] = set()
    for _ in range(depth):
        result.add(point)
        point = (point * inverse_four) % modulus
    return result


def build_active_graph(
    vector: np.ndarray, policy: np.ndarray
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    size = len(vector)
    parent_size = size // 3
    coordinates = np.arange(size, dtype=np.int64)
    parents = np.arange(parent_size, dtype=np.int64)
    selected_sources = parents + policy.astype(np.int64) * parent_size

    transport_targets = np.fromiter(
        (transport_successor(int(source), size) for source in coordinates),
        dtype=np.int64,
        count=size,
    )
    branch_2_targets = np.empty(parent_size, dtype=np.int64)
    branch_8_targets = np.empty(parent_size, dtype=np.int64)
    for parent in range(parent_size):
        branch_2_targets[parent], branch_8_targets[parent] = branch_successors(
            parent, size
        )

    sources = np.concatenate(
        (coordinates, selected_sources, selected_sources)
    )
    targets = np.concatenate(
        (transport_targets, branch_2_targets, branch_8_targets)
    )
    kinds = np.concatenate(
        (
            np.zeros(size, dtype=np.int8),
            np.full(parent_size, BRANCH_2, dtype=np.int8),
            np.full(parent_size, BRANCH_8, dtype=np.int8),
        )
    )
    return sources, targets, kinds


def zero_charge_graph_statistics(
    size: int,
    sources: np.ndarray,
    targets: np.ndarray,
    kinds: np.ndarray,
    depth: int,
) -> tuple[dict[str, int], np.ndarray, np.ndarray]:
    modulus = 3**depth
    excluded = exceptional_set(depth)
    coordinates = np.arange(size, dtype=np.int64)
    balls = (2 + 3 * coordinates) % modulus
    keep = np.fromiter(
        (int(ball) not in excluded for ball in balls),
        dtype=bool,
        count=size,
    )
    keep_edge = keep[sources] & keep[targets]
    graph = coo_matrix(
        (
            np.ones(int(keep_edge.sum()), dtype=np.int8),
            (sources[keep_edge], targets[keep_edge]),
        ),
        shape=(size, size),
    ).tocsr()
    component_count, labels = connected_components(
        graph, directed=True, connection="strong"
    )
    sizes = np.bincount(labels, minlength=component_count)
    largest_component = int(np.argmax(sizes))
    in_largest = labels == largest_component

    cyclic_components = sizes > 1
    self_loop_edges = keep_edge & (sources == targets)
    cyclic_components[labels[sources[self_loop_edges]]] = True

    branch_edges = kinds != 0
    branch_outdegree = np.zeros(size, dtype=np.int8)
    np.add.at(branch_outdegree, sources[keep_edge & branch_edges], 1)
    indegree = np.zeros(size, dtype=np.int8)
    np.add.at(indegree, targets[keep_edge], 1)

    excluded_nodes = size - int(keep.sum())
    result = {
        "kept_nodes": int(keep.sum()),
        "kept_edges": int(keep_edge.sum()),
        "restricted_sccs": int(component_count - excluded_nodes),
        "largest_scc": int(sizes[largest_component]),
        "cyclic_nodes": int(sizes[cyclic_components].sum()),
        "split_nodes_in_largest": int(
            np.count_nonzero(in_largest & (branch_outdegree > 0))
        ),
        "merge_nodes_in_largest": int(
            np.count_nonzero(in_largest & (indegree > 1))
        ),
    }
    return result, keep, keep_edge


def floating_radius(
    manifest: dict[str, object],
    size: int,
    sources: np.ndarray,
    targets: np.ndarray,
    kinds: np.ndarray,
    keep: np.ndarray,
    keep_edge: np.ndarray,
) -> float:
    """Uncertified power-iteration diagnostic on the restricted active matrix."""

    lam = int(manifest["A"]) / int(manifest["SC_L"])
    weight_scale = int(manifest["SC_W"])
    weights = {
        0: lam**-2,
        BRANCH_2: int(manifest["B2"]) / weight_scale,
        BRANCH_8: int(manifest["B8"]) / weight_scale,
    }
    data = np.fromiter(
        (weights[int(kind)] for kind in kinds[keep_edge]),
        dtype=np.float64,
        count=int(keep_edge.sum()),
    )
    matrix = coo_matrix(
        (data, (targets[keep_edge], sources[keep_edge])),
        shape=(size, size),
    ).tocsr()
    vector = keep.astype(np.float64)
    vector /= vector.sum()
    radius = 0.0
    for _ in range(2_000):
        image = matrix @ vector
        total = float(image.sum())
        if total == 0:
            return 0.0
        image /= total
        radius = total
        if np.max(np.abs(image - vector)) < 1e-13:
            break
        vector = image
    return radius


def factor_rows(rows: np.ndarray) -> np.ndarray:
    rows = np.ascontiguousarray(rows, dtype=np.int64)
    structured_type = np.dtype(
        [(f"field_{column}", rows.dtype) for column in range(rows.shape[1])]
    )
    _, inverse = np.unique(rows.view(structured_type).ravel(), return_inverse=True)
    return inverse.astype(np.int64)


def refinement_counts(
    initial_rows: np.ndarray,
    transport_targets: np.ndarray,
    branch_2_targets: np.ndarray,
    branch_8_targets: np.ndarray,
    rounds: int = 7,
) -> tuple[int, ...]:
    colors = factor_rows(initial_rows)
    counts = [int(colors.max()) + 1]
    for _ in range(rounds):
        sink_color = int(colors.max()) + 1
        extended = np.append(colors, sink_color)
        signatures = np.column_stack(
            (
                colors,
                extended[transport_targets],
                extended[branch_2_targets],
                extended[branch_8_targets],
            )
        )
        colors = factor_rows(signatures)
        counts.append(int(colors.max()) + 1)
    return tuple(counts)


def verify_state_refinement(
    vector: np.ndarray, policy: np.ndarray, sources: np.ndarray, targets: np.ndarray
) -> None:
    size = len(vector)
    parent_size = size // 3
    coordinates = np.arange(size, dtype=np.int64)
    parent = coordinates % parent_size
    digit = coordinates // parent_size
    ball = ((2 + 3 * coordinates) % 27 - 2) // 3

    children = vector.reshape(3, parent_size)
    order = np.argsort(children, axis=0)
    permutation_code = order[0] * 9 + order[1] * 3 + order[2]

    # sources/targets are stored as T for every coordinate, followed by the
    # B2 and B8 edge of each selected source.  Missing branch transitions go
    # to one common sink during deterministic partition refinement.
    transport_targets = targets[:size]
    branch_2_targets = np.full(size, size, dtype=np.int64)
    branch_8_targets = np.full(size, size, dtype=np.int64)
    selected_sources = sources[size : size + parent_size]
    branch_2_targets[selected_sources] = targets[size : size + parent_size]
    branch_8_targets[selected_sources] = targets[size + parent_size :]

    policy_rows = np.column_stack((ball, digit, policy[parent]))
    policy_counts = refinement_counts(
        policy_rows, transport_targets, branch_2_targets, branch_8_targets
    )
    if policy_counts != EXPECTED_POLICY_REFINEMENT:
        raise AssertionError("policy/carry state refinement changed")

    order_rows = np.column_stack(
        (ball, digit, policy[parent], permutation_code[parent])
    )
    order_counts = refinement_counts(
        order_rows, transport_targets, branch_2_targets, branch_8_targets
    )
    if order_counts != EXPECTED_ORDER_REFINEMENT:
        raise AssertionError("sibling-order state refinement changed")

    sorted_children = np.sort(children, axis=0)
    small_gap = sorted_children[1] - sorted_children[0]
    large_gap = sorted_children[2] - sorted_children[0]
    common_divisor = np.gcd(small_gap, large_gap)
    if np.any(common_divisor == 0):
        raise AssertionError("strict policy produced a zero projective gap")
    projective_gaps = np.column_stack(
        (small_gap // common_divisor, large_gap // common_divisor)
    )
    distinct_gap_shapes = int(np.unique(projective_gaps, axis=0).shape[0])
    if distinct_gap_shapes != parent_size:
        raise AssertionError("exact projective sibling-gap shapes are not unique")

    print("PASS: deterministic quotient refinement counts")
    print("  policy/carry:", " -> ".join(map(str, policy_counts)))
    print("  +sibling order:", " -> ".join(map(str, order_counts)))
    print(
        "PASS: exact projective sibling-gap shapes are unique on all "
        f"{parent_size} fibers"
    )


def main() -> None:
    verify_indexing()
    print("PASS: exact transport/branch carry formulas and their inverses")

    manifest, vector = load_record()
    size = len(vector)
    parent_size = size // 3
    children = vector.reshape(3, parent_size)
    policy = np.argmin(children, axis=0).astype(np.int8)
    sorted_children = np.sort(children, axis=0)
    if np.any(sorted_children[0] == sorted_children[1]):
        raise AssertionError("pinned policy has a tied minimum")
    policy_counts = tuple(map(int, np.bincount(policy, minlength=3)))
    if policy_counts != EXPECTED_POLICY_COUNTS:
        raise AssertionError("pinned minimizing-policy counts changed")
    print(f"PASS: strict pinned policy, counts={policy_counts}")

    exact_policy_retention(manifest, vector, policy)
    print("PASS: one exact rationally tightened KL step retains every argmin")

    sources, targets, kinds = build_active_graph(vector, policy)
    for depth in (3, 4, 5):
        statistics, keep, keep_edge = zero_charge_graph_statistics(
            size, sources, targets, kinds, depth
        )
        if statistics != EXPECTED_ZERO_CHARGE[depth]:
            raise AssertionError(f"J={depth} active graph reduction changed")
        radius = floating_radius(
            manifest, size, sources, targets, kinds, keep, keep_edge
        )
        print(
            f"PASS J={depth}: exact largest SCC={statistics['largest_scc']} "
            f"of {statistics['kept_nodes']}, "
            f"split/merge={statistics['split_nodes_in_largest']}/"
            f"{statistics['merge_nodes_in_largest']}; "
            f"FLOAT active radius={radius:.12f}"
        )

    verify_state_refinement(vector, policy, sources, targets)
    print(
        "CONCLUSION: the same-policy graph is semantically exact and carries "
        "recurrent split/merge defects, but its natural deterministic quotient "
        "refines to essentially the full coordinate system; no bounded defect "
        "automaton or all-level invariant is claimed"
    )


if __name__ == "__main__":
    main()
