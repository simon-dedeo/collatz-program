#!/usr/bin/env python3
"""Exact finite audit of an argmin-frustration lower bound.

For a selected level-``k`` certificate vector ``c``, split the coordinates
into ternary fibers and write

    g_u = min_a c_(u,a),       g'_v = min_z g_(v,z).

The three fine equations above a coarse branch row ``r`` pair the transport
source fiber of ``c`` with a branch-target fiber of ``g``.  The carry maps
induce a permutation ``pi_r`` of the three digit labels.  After subtracting
the two separate minima, the exact local coarse-minimum mismatch is

    h_r = min_a (tau A_u(a) + w_beta Z_v(pi_r(a))),

where ``A_u(a)=c_(u,a)-g_u`` and ``Z_v(z)=g_(v,z)-g'_v``.

Let ``sigma_A,sigma_Z`` be deterministic argmins and let ``gap_A,gap_Z``
be the second-smallest residuals.  If the two argmins disagree across the
edge signature, then every candidate digit pays at least

    omega_r = min(tau gap_A, w_beta gap_Z).

Ties make the relevant second gap zero, so the same inequality remains true
without a uniqueness assumption.  Thus the actual-section frustration

    Fr(c) = sum_r omega_r 1{sigma_Z != pi_r(sigma_A)}

is an elementary lower bound for ``sum_r h_r``.

This checker uses only integer arithmetic after loading the pinned vectors.
For the rational certificate parameters

    lambda=A/SC_L,  tau=SC_L^2/A^2,  w_beta=B_beta/SC_W,

all edge costs have denominator ``A^2 SC_W``.  It verifies the finite
comparison

    Fr(c) >= ((w_2+w_8) G / 2) epsilon(c)^2,
    G=sum g,  epsilon(c)=(sum c-3G)/sum c,

on the selected records k=12,...,15.  Combined with the exact critical
coarse-slack identity, this is the sufficient inequality that would yield

    epsilon(q) >= epsilon(c) + (3/2) epsilon(c)^2.

The records checked here are rationally tightened feasible certificates, not
exact critical eigenvectors.  This is a bounded post-hoc finite audit and not
an all-level theorem, a proof of the critical coarse-slack identity, or a
magnetic-Cheeger theorem.  In particular, the underlying bipartite graph has
flat label sections; any proof must use the endogenous section and weights
forced by critical selection.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
import hashlib
from itertools import permutations, product
import json
from pathlib import Path
from typing import Iterable

import numpy as np


HERE = Path(__file__).resolve().parent
EXPECTED_LEVELS = (12, 13, 14, 15)
EXPECTED_MANIFEST_SHA256 = {
    12: "a6386bfc8d0410a3dd82a98d765690e53c620259e6b7c4a5359f150ce6d1459f",
    13: "32f22a8bfc6e7962443ce0da0fd28bdb5d2a56748e0ea832a9135a45391fc7b7",
    14: "08ac51b3f259798b9bf979388ec5f7f590c26025cc323ee331867d20d616285f",
    15: "fdf28dbd79aa50334e4f643e51232bebb46d32e6e18d40acd144101613c87ae1",
}
EXPECTED_SIDECAR_SHA256 = {
    15: "fa65959e13cb445e50c92a447a924658b45aae943873e38d774a0b79aa85cda4",
}

# These values pin the complete reduction, rather than only its final sign.
EXPECTED_REDUCTIONS = {
    12: {
        "total": 1_373_960_412_522_506_741,
        "coarse_total": 433_998_324_323_329_751,
        "excess": 71_965_439_552_517_488,
        "edges": 39_366,
        "mismatches": 26_448,
        "frustration_numerator":
            451_432_838_902_254_236_560_662_447_124_726_169_319_752_462,
        "local_cost_numerator":
            772_423_864_681_596_547_189_456_501_972_885_013_539_027_640,
    },
    13: {
        "total": 4_475_321_486_922_343_160,
        "coarse_total": 1_419_895_314_933_859_664,
        "excess": 215_635_542_120_764_168,
        "edges": 118_098,
        "mismatches": 79_282,
        "frustration_numerator":
            1_322_770_043_241_481_770_572_985_258_922_421_483_958_234_368,
        "local_cost_numerator":
            2_234_900_867_728_090_992_035_322_634_418_498_268_573_545_536,
    },
    14: {
        "total": 14_596_152_850_956_151_164,
        "coarse_total": 4_650_020_642_614_134_369,
        "excess": 646_090_923_113_748_057,
        "edges": 354_294,
        "mismatches": 237_189,
        "frustration_numerator":
            3_888_857_370_006_452_701_905_029_173_034_437_030_932_079_664,
        "local_cost_numerator":
            6_531_852_270_199_133_814_291_567_659_656_285_337_188_903_364,
    },
    15: {
        "total": 47_049_100_452_382_107_460,
        "coarse_total": 15_044_745_800_098_690_322,
        "excess": 1_914_863_052_086_036_494,
        "edges": 1_062_882,
        "mismatches": 710_970,
        "frustration_numerator":
            11_307_279_577_756_309_029_491_122_163_980_890_816_531_156_265,
        "local_cost_numerator":
            18_883_819_318_381_755_969_950_287_873_041_798_252_295_246_870,
    },
}

BRANCH_2 = 2
NEUTRAL = 5
BRANCH_8 = 8


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(8 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def parse_levels(specification: str) -> tuple[int, ...]:
    levels: set[int] = set()
    for piece in specification.split(","):
        piece = piece.strip()
        if not piece:
            continue
        if "-" in piece:
            first_text, last_text = piece.split("-", 1)
            levels.update(range(int(first_text), int(last_text) + 1))
        else:
            levels.add(int(piece))
    result = tuple(sorted(levels))
    if not result or any(level not in EXPECTED_LEVELS for level in result):
        raise ValueError("levels must be a nonempty subset of 12,...,15")
    return result


def branch_type(index: int) -> int:
    return (BRANCH_2, NEUTRAL, BRANCH_8)[index % 3]


def transport(index: int, size: int) -> int:
    """Transport-source index at a level with ``size`` states."""

    return (4 * index + 2) % size


def branch_target(index: int, size: int) -> int:
    """Parent index of the branch fiber at a level with ``size`` states."""

    parent_size = size // 3
    kind = branch_type(index)
    if kind == BRANCH_2:
        return (4 * (index // 3)) % parent_size
    if kind == BRANCH_8:
        return (2 * ((index - 2) // 3) + 1) % parent_size
    raise ValueError("neutral rows have no branch target")


def slow_transport(index: int, level: int) -> int:
    modulus = 3**level
    state = 2 + 3 * index
    target = (4 * state) % modulus
    if target % 3 != 2:
        raise AssertionError("transport left the KL state class")
    return (target - 2) // 3


def slow_branch_target(index: int, level: int) -> int:
    modulus = 3**level
    coarse_modulus = modulus // 3
    state = 2 + 3 * index
    kind = state % 9
    if kind == BRANCH_2:
        target = ((4 * state - 2) // 3) % coarse_modulus
    elif kind == BRANCH_8:
        target = ((2 * state - 1) // 3) % coarse_modulus
    else:
        raise ValueError("neutral rows have no branch target")
    if target % 3 != 2:
        raise AssertionError("branch target left the KL state class")
    return (target - 2) // 3


def edge_signature(
    fine_level: int, coarse_row: int
) -> tuple[int, int, tuple[int, int, int]]:
    """Return ``(transport fiber, branch fiber, digit permutation)``."""

    fine_size = 3 ** (fine_level - 1)
    coarse_size = fine_size // 3
    branch_size = coarse_size // 3
    kind = branch_type(coarse_row)
    if kind == NEUTRAL:
        raise ValueError("neutral rows do not define mismatch edges")

    transport_fiber = transport(coarse_row, coarse_size)
    branch_fiber = branch_target(coarse_row, coarse_size)
    signature = [-1, -1, -1]
    for lift_digit in range(3):
        fine_row = coarse_row + lift_digit * coarse_size
        fine_transport = transport(fine_row, fine_size)
        fine_branch = branch_target(fine_row, fine_size)
        if fine_transport % coarse_size != transport_fiber:
            raise AssertionError("fine transport sources do not form the coarse fiber")
        if fine_branch % branch_size != branch_fiber:
            raise AssertionError("fine branch targets do not form the coarse fiber")
        source_digit = fine_transport // coarse_size
        target_digit = fine_branch // branch_size
        if signature[source_digit] != -1:
            raise AssertionError("transport digit map is not injective")
        signature[source_digit] = target_digit
    if sorted(signature) != [0, 1, 2]:
        raise AssertionError("edge signature is not a ternary permutation")
    return transport_fiber, branch_fiber, tuple(signature)


def verify_indexing(first_level: int = 2, last_level: int = 8) -> None:
    for level in range(first_level, last_level + 1):
        size = 3 ** (level - 1)
        for index in range(size):
            if transport(index, size) != slow_transport(index, level):
                raise AssertionError("closed transport index formula failed")
            if branch_type(index) != NEUTRAL:
                if branch_target(index, size) != slow_branch_target(index, level):
                    raise AssertionError("closed branch-target formula failed")

    for fine_level in range(max(4, first_level + 1), last_level + 1):
        coarse_size = 3 ** (fine_level - 2)
        branch_size = coarse_size // 3
        expected = list(range(branch_size))
        for kind in (BRANCH_2, BRANCH_8):
            targets = sorted(
                branch_target(row, coarse_size)
                for row in range(coarse_size)
                if branch_type(row) == kind
            )
            if targets != expected:
                raise AssertionError("coarse branch targets are not bijective")
        for row in range(coarse_size):
            if branch_type(row) != NEUTRAL:
                edge_signature(fine_level, row)


def second_smallest(values: tuple[int, int, int]) -> int:
    return sorted(values)[1]


def first_argmin(values: tuple[int, int, int]) -> int:
    return min(range(3), key=values.__getitem__)


def verify_local_frustration_lemma() -> None:
    triples = tuple(values for values in product(range(4), repeat=3) if min(values) == 0)
    for left in triples:
        for right in triples:
            for signature in permutations(range(3)):
                for tau_coefficient, branch_coefficient in ((1, 1), (2, 3), (5, 2)):
                    left_argmin = first_argmin(left)
                    right_argmin = first_argmin(right)
                    mismatch = signature[left_argmin] != right_argmin
                    edge_cost = 0
                    if mismatch:
                        edge_cost = min(
                            tau_coefficient * second_smallest(left),
                            branch_coefficient * second_smallest(right),
                        )
                    local_cost = min(
                        tau_coefficient * left[digit]
                        + branch_coefficient * right[signature[digit]]
                        for digit in range(3)
                    )
                    if local_cost < edge_cost:
                        raise AssertionError("local frustration lower bound failed")


def exact_sum(values: Iterable[np.integer]) -> int:
    """Avoid fixed-width overflow in the large certificate totals."""

    return sum(map(int, values))


def load_record(level: int) -> tuple[dict[str, object], np.ndarray]:
    manifest_path = HERE / f"cert_k{level}.json"
    actual_manifest_hash = sha256(manifest_path)
    if actual_manifest_hash != EXPECTED_MANIFEST_SHA256[level]:
        raise AssertionError(
            f"k={level} manifest hash mismatch: {actual_manifest_hash}"
        )
    manifest = json.loads(manifest_path.read_text())
    if int(manifest["k"]) != level:
        raise AssertionError("manifest level mismatch")

    if level <= 14:
        raw = manifest.get("C")
        if not isinstance(raw, list):
            raise AssertionError("portable manifest has no inline vector")
        vector = np.asarray(raw, dtype=np.int64)
    else:
        sidecar_name = manifest.get("C_file")
        if not isinstance(sidecar_name, str):
            raise AssertionError("sidecar manifest has no C_file")
        sidecar = HERE / sidecar_name
        actual_sidecar_hash = sha256(sidecar)
        if actual_sidecar_hash != EXPECTED_SIDECAR_SHA256[level]:
            raise AssertionError(
                f"k={level} sidecar hash mismatch: {actual_sidecar_hash}"
            )
        if manifest.get("C_sha256") != actual_sidecar_hash:
            raise AssertionError("manifest-to-sidecar provenance mismatch")
        vector = np.load(sidecar, mmap_mode="r")

    expected_size = 3 ** (level - 1)
    if vector.shape != (expected_size,) or vector.dtype not in (
        np.dtype("int64"),
        np.dtype("uint64"),
    ):
        raise AssertionError("certificate vector has the wrong shape or dtype")
    if np.any(vector == 0):
        raise AssertionError("certificate vector is not strictly positive")
    return manifest, vector


def verify_record(level: int) -> dict[str, int]:
    manifest, vector = load_record(level)
    fine_size = len(vector)
    coarse_size = fine_size // 3
    branch_size = coarse_size // 3

    children = vector.reshape(3, coarse_size)
    coarse = np.minimum(np.minimum(children[0], children[1]), children[2])
    coarse_children = coarse.reshape(3, branch_size)
    twice_coarse = np.minimum(
        np.minimum(coarse_children[0], coarse_children[1]), coarse_children[2]
    )

    total = exact_sum(vector)
    coarse_total = exact_sum(coarse)
    excess = total - 3 * coarse_total
    if not 0 < excess < total:
        raise AssertionError("terminal excess is degenerate")

    lambda_numerator = int(manifest["A"])
    lambda_scale = int(manifest["SC_L"])
    weight_scale = int(manifest["SC_W"])
    branch_numerators = {
        BRANCH_2: int(manifest["B2"]),
        BRANCH_8: int(manifest["B8"]),
    }
    lambda_square = lambda_numerator * lambda_numerator
    transport_numerator = lambda_scale * lambda_scale * weight_scale

    frustration_numerator = 0
    local_cost_numerator = 0
    mismatches = 0
    edge_count = 0

    for row in range(coarse_size):
        kind = branch_type(row)
        if kind == NEUTRAL:
            continue
        edge_count += 1
        transport_fiber, branch_fiber, signature = edge_signature(level, row)
        branch_numerator = branch_numerators[kind] * lambda_square

        left = tuple(
            int(children[digit, transport_fiber]) - int(coarse[transport_fiber])
            for digit in range(3)
        )
        right = tuple(
            int(coarse_children[digit, branch_fiber])
            - int(twice_coarse[branch_fiber])
            for digit in range(3)
        )
        if min(left) != 0 or min(right) != 0:
            raise AssertionError("minimum-subtracted profile has no zero")

        left_argmin = first_argmin(left)
        right_argmin = first_argmin(right)
        mismatch = signature[left_argmin] != right_argmin
        edge_cost = 0
        if mismatch:
            mismatches += 1
            edge_cost = min(
                transport_numerator * second_smallest(left),
                branch_numerator * second_smallest(right),
            )
            frustration_numerator += edge_cost

        local_cost = min(
            transport_numerator * left[digit]
            + branch_numerator * right[signature[digit]]
            for digit in range(3)
        )
        if local_cost < edge_cost:
            raise AssertionError("record violates the local frustration lemma")
        local_cost_numerator += local_cost

    reduction = {
        "total": total,
        "coarse_total": coarse_total,
        "excess": excess,
        "edges": edge_count,
        "mismatches": mismatches,
        "frustration_numerator": frustration_numerator,
        "local_cost_numerator": local_cost_numerator,
    }
    if reduction != EXPECTED_REDUCTIONS[level]:
        raise AssertionError(f"k={level} pinned frustration reduction changed")

    # Fr has denominator A^2 SC_W.  Clearing the common SC_W and the
    # epsilon denominator gives this exact integer comparison.
    target_core = (
        lambda_square
        * (branch_numerators[BRANCH_2] + branch_numerators[BRANCH_8])
        * coarse_total
        * excess
        * excess
    )
    frustration_core = 2 * frustration_numerator * total * total
    local_cost_core = 2 * local_cost_numerator * total * total
    if frustration_core < target_core:
        raise AssertionError(f"k={level} fails the finite frustration comparison")
    if local_cost_core < frustration_core:
        raise AssertionError("summed local cost fell below frustration")

    with localcontext() as context:
        context.prec = 14
        mismatch_fraction = Decimal(mismatches) / Decimal(edge_count)
        frustration_ratio = Decimal(frustration_core) / Decimal(target_core)
        local_cost_ratio = Decimal(local_cost_core) / Decimal(target_core)
        capture_ratio = Decimal(frustration_numerator) / Decimal(local_cost_numerator)
    print(
        f"PASS k={level}: mismatches/edges={mismatch_fraction}, "
        f"Fr/target={frustration_ratio}, "
        f"sum(h)/target={local_cost_ratio}, Fr/sum(h)={capture_ratio}"
    )
    return reduction


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--levels",
        default="12-15",
        help="comma-separated levels/ranges from 12,...,15 (default: 12-15)",
    )
    arguments = parser.parse_args()
    levels = parse_levels(arguments.levels)

    verify_indexing()
    print("PASS: closed residue indexing, lift fibers, and S3 edge signatures")
    verify_local_frustration_lemma()
    print("PASS: exhaustive bounded local frustration lemma, including tied argmins")
    for level in levels:
        verify_record(level)
    print(
        "CONCLUSION: the pinned selected records pass the finite "
        "argmin-frustration sufficient comparison; no all-level theorem is claimed"
    )


if __name__ == "__main__":
    main()
