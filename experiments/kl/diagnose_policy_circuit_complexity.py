#!/usr/bin/env python3
"""Bounded circuit-complexity diagnostics for selected KL policies.

This script separates three notions which are easy to conflate.

* The level-k KL operator has a uniform O(3^k) arithmetic/min circuit.
* Composing t operator layers gives a uniform O(t 3^k) global circuit.
* A succinct coordinate circuit, DFA, OBDD, grammar, or tensor train for the
  induced minimizing-policy word is a much stronger assertion.

The exact part of the checker SHA-pins the portable selected feasible records
k=12,...,15.  Those records are subeigenvectors, not exact critical Perron
vectors.  It computes exact residual-function counts for ordered ternary
decision diagrams, arbitrary-digit-order width lower bounds within that model,
finite-field matricization ranks, an F_3 algebraic normal form at k=12, and
dependency cones.  These are lower bounds only for the stated restricted
representations; they are not lower bounds for general arithmetic circuits.

The final comparison freshly iterates the strict and p=-1 operators in
float64.  It is explicitly numerical, although Collatz--Wielandt brackets and
minimum gaps are reported.  No all-level complexity claim is made.
"""

from __future__ import annotations

import argparse
import bz2
import hashlib
import itertools
import json
import math
import zlib
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent
LEVELS = (12, 13, 14, 15)
MANIFEST_SHA256 = {
    12: "a6386bfc8d0410a3dd82a98d765690e53c620259e6b7c4a5359f150ce6d1459f",
    13: "32f22a8bfc6e7962443ce0da0fd28bdb5d2a56748e0ea832a9135a45391fc7b7",
    14: "08ac51b3f259798b9bf979388ec5f7f590c26025cc323ee331867d20d616285f",
    15: "fdf28dbd79aa50334e4f643e51232bebb46d32e6e18d40acd144101613c87ae1",
}
POLICY_COUNTS = {
    12: (20_037, 19_545, 19_467),
    13: (58_821, 58_835, 59_491),
    14: (176_945, 177_415, 177_081),
    15: (531_226, 532_339, 530_758),
}
UNIQUE_VECTOR_COUNTS = {
    12: 177_147,
    13: 531_441,
    14: 1_594_323,
    15: 4_782_968,
}
MSD_RESIDUAL_COUNTS = {
    12: (1, 3, 9, 27, 81, 243, 729, 2_187, 5_568, 27, 3),
    13: (1, 3, 9, 27, 81, 243, 729, 2_187, 6_561, 12_391, 27, 3),
    14: (
        1,
        3,
        9,
        27,
        81,
        243,
        729,
        2_187,
        6_561,
        19_683,
        18_659,
        27,
        3,
    ),
    15: (
        1,
        3,
        9,
        27,
        81,
        243,
        729,
        2_187,
        6_561,
        19_683,
        59_049,
        19_680,
        27,
        3,
    ),
}
LSD_RESIDUAL_COUNTS = {
    12: (1, 3, 9, 27, 81, 243, 729, 2_187, 5_269, 27, 3),
    13: (1, 3, 9, 27, 81, 243, 729, 2_187, 6_560, 11_676, 27, 3),
    14: (
        1,
        3,
        9,
        27,
        81,
        243,
        729,
        2_187,
        6_561,
        19_679,
        18_088,
        27,
        3,
    ),
    15: (
        1,
        3,
        9,
        27,
        81,
        243,
        729,
        2_187,
        6_561,
        19_683,
        59_036,
        19_661,
        27,
        3,
    ),
}
ARBITRARY_ORDER_LAYER = {
    12: (120, 2_187, 2_187),
    13: (165, 6_553, 6_561),
    14: (220, 19_668, 19_683),
    15: (286, 58_945, 59_049),
}
MODULAR_RANKS = {
    12: (243, 243),
    13: (729, 487),
    14: (729, 729),
}
EXPECTED_CROSS_LEVEL_MATCHES = {
    (12, 13): (19_516, 19_709, 19_747),
    (13, 14): (58_816, 58_896, 59_143),
    (14, 15): (177_539, 176_474, 177_615),
}
FINITE_FIELD_PRIME = 65_521
ALPHA = math.log(3.0, 2.0)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(8 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def load_record(level: int) -> tuple[dict[str, object], np.ndarray]:
    manifest_path = HERE / f"cert_k{level}.json"
    actual_hash = sha256(manifest_path)
    if actual_hash != MANIFEST_SHA256[level]:
        raise AssertionError(f"k={level} manifest hash mismatch: {actual_hash}")
    manifest = json.loads(manifest_path.read_text())
    raw = manifest.get("C")
    if isinstance(raw, list):
        vector = np.asarray(raw, dtype=np.int64)
    else:
        sidecar = HERE / str(manifest["C_file"])
        actual_sidecar_hash = sha256(sidecar)
        if actual_sidecar_hash != manifest["C_sha256"]:
            raise AssertionError(
                f"k={level} sidecar hash mismatch: {actual_sidecar_hash}"
            )
        vector = np.load(sidecar, allow_pickle=False)
    if vector.shape != (3 ** (level - 1),) or np.any(vector <= 0):
        raise AssertionError(f"k={level} vector has the wrong shape or sign")
    return manifest, np.asarray(vector, dtype=np.int64)


def selected_policy(vector: np.ndarray) -> np.ndarray:
    children = vector.reshape(3, -1)
    ordered = np.sort(children, axis=0)
    if np.any(ordered[0] == ordered[1]):
        raise AssertionError("selected record has a tied fiber minimum")
    return np.argmin(children, axis=0).astype(np.uint8)


def entropy_bits(counts: np.ndarray) -> float:
    positive = counts[counts > 0].astype(np.float64)
    probabilities = positive / positive.sum()
    return float(-np.sum(probabilities * np.log2(probabilities)))


def pack_four_trits(policy: np.ndarray) -> bytes:
    padding = (-len(policy)) % 4
    values = np.pad(policy, (0, padding)).astype(np.uint8)
    return (
        values[0::4]
        + 3 * values[1::4]
        + 9 * values[2::4]
        + 27 * values[3::4]
    ).astype(np.uint8).tobytes()


def natural_residual_counts(policy: np.ndarray, digits: int) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Numbers of residual functions after MSD- or LSD-first prefixes."""

    msd: list[int] = []
    lsd: list[int] = []
    for prefix_length in range(digits + 1):
        msd_rows = policy.reshape(
            3**prefix_length, 3 ** (digits - prefix_length)
        )
        lsd_rows = policy.reshape(
            3 ** (digits - prefix_length), 3**prefix_length
        ).T
        msd.append(int(np.unique(msd_rows, axis=0).shape[0]))
        lsd.append(int(np.unique(lsd_rows, axis=0).shape[0]))
    return tuple(msd), tuple(lsd)


def arbitrary_order_width_lower_bound(
    policy: np.ndarray, digits: int
) -> tuple[int, int, int]:
    """Inspect every prefix-set leaving three ternary variables unread.

    For a fixed digit order, states after a queried prefix must distinguish
    distinct residual functions on the unread digits.  Every order encounters
    one of these subsets, so the minimum count over all subsets is an exact
    lower bound on the width of every ordered read-once branching program.
    """

    tensor = policy.reshape((3,) * digits)
    powers = 3 ** np.arange(27, dtype=np.uint64)
    counts: list[int] = []
    for complement in itertools.combinations(range(digits), 3):
        prefix = [axis for axis in range(digits) if axis not in complement]
        rows = np.transpose(tensor, prefix + list(complement)).reshape(
            3 ** (digits - 3), 27
        )
        # A residual function has 27 ternary outputs, whose exact base-three
        # code fits in uint64 because 3^27 < 2^64.
        codes = rows.astype(np.uint64) @ powers
        counts.append(int(np.unique(codes).shape[0]))
    return len(counts), min(counts), max(counts)


def exhaustive_ordered_diagram_k12(
    policy: np.ndarray,
) -> tuple[int, int, tuple[int, ...], tuple[int, ...]]:
    """Exact optimum over all ten digit orders for the k=12 policy."""

    digits = 10
    tensor = policy.reshape((3,) * digits)
    residuals = np.empty(1 << digits, dtype=np.int64)
    for mask in range(1 << digits):
        prefix = [axis for axis in range(digits) if mask & (1 << axis)]
        suffix = [axis for axis in range(digits) if not mask & (1 << axis)]
        rows = np.transpose(tensor, prefix + suffix).reshape(
            3 ** len(prefix), 3 ** len(suffix)
        )
        residuals[mask] = np.unique(rows, axis=0).shape[0]

    infinity = np.iinfo(np.int64).max
    total = np.full(1 << digits, infinity, dtype=np.int64)
    peak = np.full(1 << digits, infinity, dtype=np.int64)
    total_parent = np.full(1 << digits, -1, dtype=np.int8)
    peak_parent = np.full(1 << digits, -1, dtype=np.int8)
    total[0] = residuals[0]
    peak[0] = residuals[0]
    for mask in range(1, 1 << digits):
        for axis in range(digits):
            if not mask & (1 << axis):
                continue
            previous = mask ^ (1 << axis)
            total_candidate = int(total[previous]) + int(residuals[mask])
            if total_candidate < total[mask]:
                total[mask] = total_candidate
                total_parent[mask] = axis
            peak_candidate = max(int(peak[previous]), int(residuals[mask]))
            if peak_candidate < peak[mask]:
                peak[mask] = peak_candidate
                peak_parent[mask] = axis

    def recover(parents: np.ndarray) -> tuple[int, ...]:
        mask = (1 << digits) - 1
        reversed_order: list[int] = []
        while mask:
            axis = int(parents[mask])
            reversed_order.append(axis)
            mask ^= 1 << axis
        return tuple(reversed(reversed_order))

    return (
        int(total[-1]),
        int(peak[-1]),
        recover(total_parent),
        recover(peak_parent),
    )


def rank_mod_prime(matrix: np.ndarray, prime: int = FINITE_FIELD_PRIME) -> int:
    """Row rank over F_prime; a lower bound for characteristic-zero rank."""

    reduced = np.asarray(matrix, dtype=np.int64) % prime
    row_count, column_count = reduced.shape
    rank = 0
    for column in range(column_count):
        candidates = np.flatnonzero(reduced[rank:, column])
        if not len(candidates):
            continue
        pivot = rank + int(candidates[0])
        if pivot != rank:
            reduced[[rank, pivot]] = reduced[[pivot, rank]]
        inverse = pow(int(reduced[rank, column]), -1, prime)
        reduced[rank, column:] = (
            reduced[rank, column:] * inverse
        ) % prime
        if rank + 1 < row_count:
            factors = reduced[rank + 1 :, column].copy()
            nonzero = np.flatnonzero(factors)
            if len(nonzero):
                rows = rank + 1 + nonzero
                reduced[rows, column:] = (
                    reduced[rows, column:]
                    - factors[nonzero, None] * reduced[rank, column:]
                ) % prime
        rank += 1
        if rank == row_count:
            break
    return rank


def matricization_ranks(
    level: int, vector: np.ndarray, policy: np.ndarray
) -> tuple[tuple[int, int], int, tuple[int, int], int]:
    coordinate_digits = level - 1
    coordinate_prefix = coordinate_digits // 2
    value_matrix = vector.reshape(
        3**coordinate_prefix, 3 ** (coordinate_digits - coordinate_prefix)
    )

    policy_digits = level - 2
    policy_prefix = (policy_digits + 1) // 2
    one_hot = np.eye(3, dtype=np.int8)[policy].reshape(
        (3,) * policy_digits + (3,)
    )
    policy_matrix = one_hot.reshape(
        3**policy_prefix, 3 ** (policy_digits - policy_prefix) * 3
    )
    return (
        value_matrix.shape,
        rank_mod_prime(value_matrix),
        policy_matrix.shape,
        rank_mod_prime(policy_matrix),
    )


def anf_statistics(policy: np.ndarray) -> tuple[int, int, int, tuple[int, ...]]:
    """Canonical reduced polynomial of sigma:F_3^10 -> F_3."""

    digits = 10
    # Signed arithmetic is essential here: uint8 subtraction would wrap
    # modulo 256 before the intended reduction modulo three.
    coefficients = policy.reshape((3,) * digits).astype(np.int64) % 3
    for axis in range(digits):
        moved = np.moveaxis(coefficients, axis, 0)
        value_zero = moved[0].copy()
        value_one = moved[1].copy()
        value_two = moved[2].copy()
        linear = 2 * (value_one - value_two) % 3
        moved[0] = value_zero
        moved[1] = linear
        moved[2] = (value_one - value_zero - linear) % 3

    indices = np.indices((3,) * digits)
    total_degree = indices.sum(axis=0)
    support_size = (indices > 0).sum(axis=0)
    nonzero = coefficients != 0
    degree_counts = tuple(
        map(int, np.bincount(total_degree[nonzero], minlength=2 * digits + 1))
    )

    reconstructed = coefficients.copy()
    for axis in range(digits):
        moved = np.moveaxis(reconstructed, axis, 0)
        constant = moved[0].copy()
        linear = moved[1].copy()
        quadratic = moved[2].copy()
        moved[0] = constant
        moved[1] = (constant + linear + quadratic) % 3
        moved[2] = (constant + 2 * linear + quadratic) % 3
    if not np.array_equal(reconstructed.reshape(-1), policy):
        raise AssertionError("F_3 algebraic normal form did not reconstruct")
    return (
        int(np.count_nonzero(nonzero)),
        int(total_degree[nonzero].max()),
        int(support_size[nonzero].max()),
        degree_counts,
    )


def branch_parents(rows: np.ndarray, size: int) -> tuple[np.ndarray, np.ndarray]:
    parent_size = size // 3
    branch_rows = rows[rows % 3 != 1]
    residue = branch_rows % 3
    parents = np.empty(len(branch_rows), dtype=np.int64)
    type_two = residue == 0
    type_eight = residue == 2
    parents[type_two] = (4 * (branch_rows[type_two] // 3)) % parent_size
    parents[type_eight] = (
        2 * ((branch_rows[type_eight] - 2) // 3) + 1
    ) % parent_size
    return branch_rows, parents


def expand_dependency_cone(
    rows: np.ndarray, policy: np.ndarray, active: bool
) -> np.ndarray:
    size = 3 * len(policy)
    parent_size = len(policy)
    transport = (4 * rows + 2) % size
    _, parents = branch_parents(rows, size)
    if active:
        branch_sources = parents + policy[parents].astype(np.int64) * parent_size
    else:
        branch_sources = np.concatenate(
            (parents, parents + parent_size, parents + 2 * parent_size)
        )
    return np.unique(np.concatenate((transport, branch_sources)))


def saturation_depth(start: int, policy: np.ndarray, active: bool) -> int:
    size = 3 * len(policy)
    rows = np.asarray([start], dtype=np.int64)
    for depth in range(1, 256):
        rows = expand_dependency_cone(rows, policy, active)
        if len(rows) == size:
            return depth
    raise AssertionError("dependency cone did not saturate in 255 layers")


def operator_indices(level: int) -> tuple[np.ndarray, ...]:
    size = 3 ** (level - 1)
    parent_size = size // 3
    rows = np.arange(size, dtype=np.int64)
    transport = (4 * rows + 2) % size
    rows_two = rows[rows % 3 == 0]
    rows_eight = rows[rows % 3 == 2]
    parent_two = (4 * (rows_two // 3)) % parent_size
    parent_eight = (2 * ((rows_eight - 2) // 3) + 1) % parent_size
    offsets = parent_size * np.arange(3, dtype=np.int64)
    fibers_two = parent_two[:, None] + offsets[None, :]
    fibers_eight = parent_eight[:, None] + offsets[None, :]
    return transport, rows_two, rows_eight, fibers_two, fibers_eight


def power_mean(values: np.ndarray, power: float) -> np.ndarray:
    scaled = power * np.log(values)
    peak = np.max(scaled, axis=1)
    log_mean = peak + np.log(np.mean(np.exp(scaled - peak[:, None]), axis=1))
    return np.exp(log_mean / power)


def apply_operator(
    vector: np.ndarray,
    indices: tuple[np.ndarray, ...],
    lambda_value: float,
    power: float | None,
) -> np.ndarray:
    transport, rows_two, rows_eight, fibers_two, fibers_eight = indices
    image = lambda_value**-2 * vector[transport]
    if power is None:
        mean_two = np.min(vector[fibers_two], axis=1)
        mean_eight = np.min(vector[fibers_eight], axis=1)
    else:
        mean_two = power_mean(vector[fibers_two], power)
        mean_eight = power_mean(vector[fibers_eight], power)
    image[rows_two] += lambda_value ** (ALPHA - 2) * mean_two
    image[rows_eight] += lambda_value ** (ALPHA - 1) * mean_eight
    return image


def floating_perron(
    level: int,
    lambda_value: float,
    power: float | None,
    tolerance: float = 1.0e-12,
) -> tuple[np.ndarray, int, float, float]:
    indices = operator_indices(level)
    vector = np.ones(3 ** (level - 1), dtype=np.float64)
    lower = upper = 0.0
    for iteration in range(1, 1_001):
        image = apply_operator(vector, indices, lambda_value, power)
        ratios = image / vector
        lower = float(ratios.min())
        upper = float(ratios.max())
        vector = image / image.max()
        if iteration > 50 and math.log(upper / lower) <= tolerance:
            return vector, iteration, lower, upper
    raise AssertionError("floating Perron iteration did not converge")


def approximate_tt_ranks(
    vector: np.ndarray, level: int, tolerances: tuple[float, ...]
) -> dict[float, int]:
    normalized = vector.astype(np.float64, copy=True)
    normalized /= np.linalg.norm(normalized)
    digits = level - 1
    maxima = {tolerance: 0 for tolerance in tolerances}
    for prefix in range(1, digits):
        matrix = normalized.reshape(3**prefix, 3 ** (digits - prefix))
        singular_values = np.linalg.svd(matrix, compute_uv=False)
        squares = singular_values * singular_values
        total = float(squares.sum())
        tails = np.concatenate((np.cumsum(squares[::-1])[::-1], [0.0]))
        for tolerance in tolerances:
            rank = next(
                candidate
                for candidate in range(1, len(singular_values) + 1)
                if math.sqrt(float(tails[candidate]) / total) <= tolerance
            )
            maxima[tolerance] = max(maxima[tolerance], rank)
    return maxima


def cross_level_statistics(
    lower: np.ndarray, upper: np.ndarray
) -> tuple[tuple[int, ...], tuple[float, ...]]:
    upper_blocks = upper.reshape(3, -1)
    matches: list[int] = []
    conditional_entropies: list[float] = []
    for digit in range(3):
        confusion = np.zeros((3, 3), dtype=np.int64)
        np.add.at(confusion, (lower, upper_blocks[digit]), 1)
        matches.append(int(np.trace(confusion)))
        entropy = 0.0
        for row in confusion:
            if row.sum():
                entropy += row.sum() / len(lower) * entropy_bits(row)
        conditional_entropies.append(entropy)
    return tuple(matches), tuple(conditional_entropies)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--skip-floating",
        action="store_true",
        help="skip fresh strict/soft Perron and approximate tensor-rank diagnostics",
    )
    args = parser.parse_args()

    records: dict[int, np.ndarray] = {}
    policies: dict[int, np.ndarray] = {}
    print("EXACT SELECTED-RECORD DIAGNOSTICS")
    for level in LEVELS:
        _, vector = load_record(level)
        policy = selected_policy(vector)
        records[level] = vector
        policies[level] = policy
        counts = tuple(map(int, np.bincount(policy, minlength=3)))
        if counts != POLICY_COUNTS[level]:
            raise AssertionError(f"k={level} policy counts changed")
        unique_values = int(np.unique(vector).shape[0])
        if unique_values != UNIQUE_VECTOR_COUNTS[level]:
            raise AssertionError(f"k={level} distinct coordinate count changed")

        msd, lsd = natural_residual_counts(policy, level - 2)
        if msd != MSD_RESIDUAL_COUNTS[level] or lsd != LSD_RESIDUAL_COUNTS[level]:
            raise AssertionError(f"k={level} residual-function counts changed")
        arbitrary = arbitrary_order_width_lower_bound(policy, level - 2)
        if arbitrary != ARBITRARY_ORDER_LAYER[level]:
            raise AssertionError(f"k={level} arbitrary-order lower bound changed")

        packed = pack_four_trits(policy)
        entropy = entropy_bits(np.bincount(policy, minlength=3))
        zlib_bits = 8.0 * len(zlib.compress(packed, 9)) / len(policy)
        bz2_bits = 8.0 * len(bz2.compress(packed, 9)) / len(policy)
        children = np.sort(vector.reshape(3, -1), axis=0).astype(np.float64)
        minimum_log_gap = float(np.min(np.log(children[1] / children[0])))
        print(
            f"k={level}: policy_length={len(policy):,}, counts={counts}, "
            f"H1={entropy:.9f} bits/trit, unique_C={unique_values:,}/{len(vector):,}"
        )
        print(
            f"  strict min_log_gap={minimum_log_gap:.3e}; "
            f"packed zlib/bz2={zlib_bits:.5f}/{bz2_bits:.5f} bits/trit"
        )
        print(
            f"  aligned MSD DAG total/peak={sum(msd):,}/{max(msd):,}; "
            f"LSD={sum(lsd):,}/{max(lsd):,}"
        )
        print(
            f"  every digit order has width >= {arbitrary[1]:,} at its "
            f"{level-5}-digit prefix (range over {arbitrary[0]} subsets: "
            f"{arbitrary[1]:,}..{arbitrary[2]:,})"
        )

    optimum = exhaustive_ordered_diagram_k12(policies[12])
    if optimum[:2] != (8_579, 5_269):
        raise AssertionError("k=12 exhaustive digit-order optimum changed")
    print(
        "PASS k=12 all-order DP: optimal layered total/peak="
        f"{optimum[0]:,}/{optimum[1]:,}; total-order={optimum[2]}, "
        f"peak-order={optimum[3]}"
    )

    anf = anf_statistics(policies[12])
    if anf[:3] != (39_296, 19, 10):
        raise AssertionError("k=12 F_3 ANF statistics changed")
    print(
        "PASS k=12 F_3 ANF: "
        f"nonzero={anf[0]:,}/59,049, max_total_degree={anf[1]}, "
        f"max_variable_support={anf[2]}"
    )

    for level in (12, 13, 14):
        value_shape, value_rank, policy_shape, policy_rank = matricization_ranks(
            level, records[level], policies[level]
        )
        if (value_rank, policy_rank) != MODULAR_RANKS[level]:
            raise AssertionError(f"k={level} modular ranks changed")
        print(
            f"PASS k={level} rank mod {FINITE_FIELD_PRIME}: "
            f"C{value_shape} rank={value_rank}; "
            f"one-hot-policy{policy_shape} rank={policy_rank}"
        )

    for lower_level in (12, 13, 14):
        matches, conditional = cross_level_statistics(
            policies[lower_level], policies[lower_level + 1]
        )
        if matches != EXPECTED_CROSS_LEVEL_MATCHES[(lower_level, lower_level + 1)]:
            raise AssertionError("cross-level policy match counts changed")
        agreements = tuple(match / len(policies[lower_level]) for match in matches)
        print(
            f"PASS k={lower_level}->{lower_level+1} top-digit lifts: "
            f"agreement={tuple(round(value, 6) for value in agreements)}, "
            f"H(new|old)="
            f"{tuple(round(float(value), 6) for value in conditional)}"
        )

    full_depths = tuple(
        saturation_depth(start, policies[12], active=False)
        for start in (0, len(records[12]) - 1)
    )
    active_depths = tuple(
        saturation_depth(start, policies[12], active=True)
        for start in (0, len(records[12]) - 1)
    )
    if full_depths != (11, 11) or active_depths != (84, 82):
        raise AssertionError("k=12 dependency saturation depths changed")
    print(
        "PASS k=12 coordinate dependency cones (starts 0,-1): "
        f"full-min saturation={full_depths}, same-policy saturation={active_depths}"
    )

    if not args.skip_floating:
        print("\nFLOATING PERRON / APPROXIMATE-TENSOR DIAGNOSTICS")
        strict, iterations, lower, upper = floating_perron(
            12, 1.8064236, None
        )
        strict_children = strict.reshape(3, -1)
        strict_policy = np.argmin(strict_children, axis=0).astype(np.uint8)
        strict_gap = float(
            np.min(
                np.log(
                    np.sort(strict_children, axis=0)[1]
                    / np.sort(strict_children, axis=0)[0]
                )
            )
        )
        print(
            f"strict k=12 lambda=1.8064236: iterations={iterations}, "
            f"CW=[{lower:.12f},{upper:.12f}], "
            f"selected-policy agreement={np.mean(strict_policy == policies[12]):.9f}, "
            f"min_log_gap={strict_gap:.3e}"
        )

        soft_vectors: dict[int, np.ndarray] = {}
        for level in (12, 13):
            soft, iterations, lower, upper = floating_perron(level, 1.9, -1.0)
            soft_vectors[level] = soft
            soft_policy = np.argmin(soft.reshape(3, -1), axis=0).astype(np.uint8)
            soft_msd, soft_lsd = natural_residual_counts(soft_policy, level - 2)
            print(
                f"soft p=-1 k={level} lambda=1.9: iterations={iterations}, "
                f"CW=[{lower:.12f},{upper:.12f}], "
                f"selected-policy agreement={np.mean(soft_policy == policies[level]):.9f}, "
                f"MSD/LSD DAG total={sum(soft_msd):,}/{sum(soft_lsd):,}"
            )

        tolerances = (1.0e-3, 1.0e-6)
        for level in (12, 13):
            selected_ranks = approximate_tt_ranks(
                records[level], level, tolerances
            )
            soft_ranks = approximate_tt_ranks(
                soft_vectors[level], level, tolerances
            )
            print(
                f"approx QTT max rank k={level}: selected={selected_ranks}, "
                f"soft_p=-1={soft_ranks} (relative Frobenius tolerances)"
            )

    print()
    print(
        "VERDICT: the operator and its finite iterates have a short uniform "
        "description and output-linear global circuits.  On k=12,...,15, "
        "however, the selected policy defeats the tested ordered read-once, "
        "aligned-grammar, sparse-ANF, and low-rank tensor "
        "models.  This is not a lower bound against general poly(k)-size "
        "circuits, and the selected records are feasible subeigenvectors, not "
        "exact critical eigenvectors."
    )


if __name__ == "__main__":
    main()
