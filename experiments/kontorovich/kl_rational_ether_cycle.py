#!/usr/bin/env python3
"""Reconstruct the rational ether KL cycle in stored exact certificates.

The linked-glider chart identifies the 3-adic boundary center

    c* = -881/473.

In the positive-center coordinate h=-c, its six KL predecessor chords are

    R2, R8, R2, R8, R8, R8.

This worker follows only that theorem-derived rational cycle.  At each stored
certificate level it reduces the six rational centers modulo 3^k, reads the
three potential values in each chord fiber, and reconstructs the exact fiber
deviation product D_E.  It then compares D_E with the certified lower weight
product W_E = B2^2 B8^4 using fractions and cross multiplication.

Large certificate vectors are SHA-checked and opened with numpy mmap.  The
output is finite certificate evidence.  It does not infer a k -> infinity
limit, an infinite linked glider chain, or a Collatz counterexample.
"""

from __future__ import annotations

import argparse
import gc
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence

import numpy as np


ROOT = Path(__file__).resolve().parents[2]
KL_DIR = ROOT / "experiments" / "kl"
TAIL_CHART_ARTIFACT = (
    ROOT
    / "experiments"
    / "kontorovich"
    / "breakoff_ether_glider_kl_tail_chart_audit.json"
)
DEFAULT_ARTIFACT = Path(__file__).with_name("kl_rational_ether_cycle.json")
DEFAULT_LEVELS = tuple(range(12, 20))
SCHEMA = "kl-rational-ether-cycle-v1"

FIXED_CENTER = Fraction(-881, 473)
POSITIVE_CENTER = -FIXED_CENTER
WORD = ("R2", "R8", "R2", "R8", "R8", "R8")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(16 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def worker_sha256() -> str:
    return sha256(Path(__file__).resolve())


def fraction_record(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def fraction_from_record(record: dict[str, Any]) -> Fraction:
    return Fraction(int(record["numerator"]), int(record["denominator"]))


def canonical_bytes(value: dict[str, Any]) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def rational_residue(value: Fraction, modulus: int) -> int:
    if modulus < 2 or value.denominator % 3 == 0:
        raise AssertionError("rational center is not a 3-adic integer here")
    return (value.numerator * pow(value.denominator, -1, modulus)) % modulus


def center_step(center: Fraction, branch: str) -> Fraction:
    center_class = rational_residue(center, 9)
    if branch == "R2":
        if center_class != 7:
            raise AssertionError("R2 applied outside positive-center class 7 mod 9")
        return (4 * center + 2) / 3
    if branch == "R8":
        if center_class != 1:
            raise AssertionError("R8 applied outside positive-center class 1 mod 9")
        return (2 * center + 1) / 3
    raise AssertionError(f"unknown KL chord {branch}")


def rational_cycle() -> tuple[Fraction, ...]:
    centers = [POSITIVE_CENTER]
    for branch in WORD:
        centers.append(center_step(centers[-1], branch))
    if centers[-1] != centers[0]:
        raise AssertionError("rational ether word did not close")
    return tuple(centers)


def compose_positive_word() -> tuple[Fraction, Fraction]:
    """Return a,b for the positive-center map h |-> a*h+b."""

    slope = Fraction(1)
    intercept = Fraction(0)
    for branch in WORD:
        if branch == "R2":
            slope, intercept = 4 * slope / 3, (4 * intercept + 2) / 3
        else:
            slope, intercept = 2 * slope / 3, (2 * intercept + 1) / 3
    return slope, intercept


def cycle_theorem_record() -> dict[str, Any]:
    centers = rational_cycle()
    slope, intercept = compose_positive_word()
    if (slope, intercept) != (Fraction(256, 729), Fraction(881, 729)):
        raise AssertionError("six-chord affine composition changed")
    if slope * POSITIVE_CENTER + intercept != POSITIVE_CENTER:
        raise AssertionError("881/473 is not the positive-center fixed point")

    edges = []
    for index, branch in enumerate(WORD):
        source = centers[index]
        target = centers[index + 1]
        edges.append(
            {
                "index": index,
                "branch": branch,
                "positive_center_source": fraction_record(source),
                "positive_center_target": fraction_record(target),
                "positive_center_source_mod_9": rational_residue(source, 9),
                "negative_state_source_mod_9": rational_residue(-source, 9),
            }
        )
    return {
        "fixed_negative_center": fraction_record(FIXED_CENTER),
        "fixed_positive_center": fraction_record(POSITIVE_CENTER),
        "cyclic_word": list(WORD),
        "counts": {"R2": WORD.count("R2"), "R8": WORD.count("R8")},
        "edges": edges,
        "positive_center_predecessor_composition": "h |-> (256*h+881)/729",
        "negative_state_predecessor_composition": "c |-> (256*c-881)/729",
        "inverse_ether_map": "F_E(c)=(729*c+881)/256",
        "fixed_point_identity": "F_E(-881/473)=-881/473",
    }


def close_vector(vector: Any) -> None:
    mapping = getattr(vector, "_mmap", None)
    if mapping is not None:
        mapping.close()


def load_certificate(level: int) -> tuple[dict[str, Any], Any, dict[str, Any]]:
    certificate_path = KL_DIR / f"cert_k{level}.json"
    certificate = json.loads(certificate_path.read_text())
    required = {"k", "B2", "B8", "SC_W", "SC_C"}
    if not required.issubset(certificate):
        raise AssertionError(f"level {level} certificate manifest is incomplete")
    if int(certificate["k"]) != level:
        raise AssertionError(f"level mismatch in {certificate_path}")

    inputs: dict[str, Any] = {
        "certificate_path": str(certificate_path.relative_to(ROOT)),
        "certificate_sha256": sha256(certificate_path),
    }
    if "C" in certificate:
        vector = certificate["C"]
        storage = "inline_json"
    else:
        sidecar_name = certificate.get("C_file")
        expected_hash = certificate.get("C_sha256")
        if not isinstance(sidecar_name, str) or not isinstance(expected_hash, str):
            raise AssertionError(f"level {level} has no valid vector sidecar manifest")
        sidecar_path = certificate_path.with_name(sidecar_name)
        actual_hash = sha256(sidecar_path)
        if actual_hash != expected_hash:
            raise AssertionError(f"level {level} vector SHA-256 mismatch")
        vector = np.load(sidecar_path, mmap_mode="r")
        if vector.ndim != 1 or vector.dtype != np.dtype("int64"):
            close_vector(vector)
            raise AssertionError(f"level {level} vector has wrong shape or dtype")
        storage = "numpy_mmap"
        inputs.update(
            {
                "vector_path": str(sidecar_path.relative_to(ROOT)),
                "vector_sha256": actual_hash,
                "manifest_vector_sha256": expected_hash,
            }
        )
    if len(vector) != 3 ** (level - 1):
        close_vector(vector)
        raise AssertionError(f"level {level} vector has wrong length")
    inputs["vector_storage"] = storage
    inputs["vector_length"] = len(vector)
    return certificate, vector, inputs


def potential(vector: Any, state: int) -> int:
    if state < 0 or state % 3 != 2:
        raise AssertionError(f"invalid KL state {state}")
    value = int(vector[(state - 2) // 3])
    if value <= 0:
        raise AssertionError("KL potential is not positive")
    return value


def chord_fiber(source_state: int, branch: str, modulus: int) -> tuple[int, int, int]:
    parent_modulus = modulus // 3
    if branch == "R2":
        if source_state % 9 != 2:
            raise AssertionError("R2 source state is not 2 mod 9")
        base = ((4 * source_state - 2) // 3) % parent_modulus
    elif branch == "R8":
        if source_state % 9 != 8:
            raise AssertionError("R8 source state is not 8 mod 9")
        base = ((2 * source_state - 1) // 3) % parent_modulus
    else:
        raise AssertionError(f"unknown KL chord {branch}")
    fiber = (base, base + parent_modulus, base + 2 * parent_modulus)
    if any(state % 3 != 2 for state in fiber):
        raise AssertionError("KL refinement fiber left the state space")
    return fiber


def audit_level(
    level: int, certificate: dict[str, Any], vector: Any, inputs: dict[str, Any]
) -> dict[str, Any]:
    modulus = 3**level
    centers = rational_cycle()
    weight_by_branch = {
        "R2": Fraction(int(certificate["B2"]), int(certificate["SC_W"])),
        "R8": Fraction(int(certificate["B8"]), int(certificate["SC_W"])),
    }
    deviation_product = Fraction(1)
    weight_product = Fraction(1)
    edges = []

    for index, branch in enumerate(WORD):
        source_state = rational_residue(-centers[index], modulus)
        target_state = rational_residue(-centers[index + 1], modulus)
        fiber = chord_fiber(source_state, branch, modulus)
        if target_state not in fiber:
            raise AssertionError("rational target is absent from its KL chord fiber")
        values = tuple(potential(vector, state) for state in fiber)
        minimum = min(values)
        desired_index = fiber.index(target_state)
        target_value = values[desired_index]
        deviation = Fraction(target_value, minimum)
        weight = weight_by_branch[branch]

        source_value = potential(vector, source_state)
        local_margin = deviation * source_value - weight * target_value
        if local_margin < 0:
            raise AssertionError("certificate misses the exact local edge calibration")

        deviation_product *= deviation
        weight_product *= weight
        edges.append(
            {
                "index": index,
                "branch": branch,
                "source_state_mod_3^k": source_state,
                "target_state_mod_3^k": target_state,
                "source_potential_integer": source_value,
                "fiber_states": list(fiber),
                "fiber_potential_integers": list(values),
                "minimum_lift_indices": [
                    lift_index
                    for lift_index, value in enumerate(values)
                    if value == minimum
                ],
                "desired_lift_index": desired_index,
                "selected_lift": target_value == minimum,
                "deviation": fraction_record(deviation),
                "certified_weight_lower": fraction_record(weight),
                "local_calibration_margin": fraction_record(local_margin),
            }
        )

    expected_weight = weight_by_branch["R2"] ** 2 * weight_by_branch["R8"] ** 4
    if weight_product != expected_weight:
        raise AssertionError("cycle weight lost B2^2 B8^4")
    ratio = deviation_product / weight_product
    if ratio <= 1:
        raise AssertionError("finite rational ether cycle lost its positive KL tax")
    selected = sum(bool(edge["selected_lift"]) for edge in edges)
    return {
        "level": level,
        "inputs": inputs,
        "center_residue_mod_3^k": rational_residue(FIXED_CENTER, modulus),
        "certificate_weights": {
            "B2_over_SC_W": fraction_record(weight_by_branch["R2"]),
            "B8_over_SC_W": fraction_record(weight_by_branch["R8"]),
            "formula": "W_E=(B2/SC_W)^2*(B8/SC_W)^4",
        },
        "edges": edges,
        "D_E": fraction_record(deviation_product),
        "W_E": fraction_record(weight_product),
        "D_E_over_W_E": fraction_record(ratio),
        "strict_tax_numerator": ratio.numerator - ratio.denominator,
        "selected_edges": selected,
        "nonselected_edges": len(edges) - selected,
    }


def monotonicity_record(rows: Sequence[dict[str, Any]]) -> dict[str, Any]:
    comparisons = []
    for left_row, right_row in zip(rows, rows[1:]):
        left = fraction_from_record(left_row["D_E_over_W_E"])
        right = fraction_from_record(right_row["D_E_over_W_E"])
        left_cross = left.numerator * right.denominator
        right_cross = right.numerator * left.denominator
        difference = left_cross - right_cross
        if difference <= 0:
            raise AssertionError(
                f"D_E/W_E did not decrease from k={left_row['level']} "
                f"to k={right_row['level']}"
            )
        comparisons.append(
            {
                "from_level": int(left_row["level"]),
                "to_level": int(right_row["level"]),
                "left_cross_product": left_cross,
                "right_cross_product": right_cross,
                "positive_difference": difference,
            }
        )
    return {
        "method": "a/b > c/d certified by exact integer comparison a*d > c*b",
        "strictly_decreasing_at_every_stored_step": True,
        "comparisons": comparisons,
    }


def literal_level_twelve_crosscheck(row: dict[str, Any]) -> dict[str, Any]:
    if int(row["level"]) != 12:
        raise AssertionError("literal cross-check requires the level-12 row")
    literal = json.loads(TAIL_CHART_ARTIFACT.read_text())
    ether = literal["fixed_precision_kl_tax"]["ether_cycle"]
    if fraction_from_record(ether["deviation_factor"]) != fraction_from_record(
        row["D_E"]
    ):
        raise AssertionError("rational and literal level-12 deviations disagree")
    if fraction_from_record(
        ether["certified_lower_weight_product"]
    ) != fraction_from_record(row["W_E"]):
        raise AssertionError("rational and literal level-12 weights disagree")
    if (
        int(ether["selected_edges"]),
        int(ether["nonselected_edges"]),
    ) != (int(row["selected_edges"]), int(row["nonselected_edges"])):
        raise AssertionError("rational and literal level-12 selections disagree")
    return {
        "artifact_path": str(TAIL_CHART_ARTIFACT.relative_to(ROOT)),
        "artifact_sha256": sha256(TAIL_CHART_ARTIFACT),
        "deviation_factor_equal": True,
        "certified_weight_equal": True,
        "selected_nonselected_counts_equal": True,
    }


def build_artifact(levels: Sequence[int] = DEFAULT_LEVELS) -> dict[str, Any]:
    level_tuple = tuple(int(level) for level in levels)
    if not level_tuple or any(level < 2 for level in level_tuple):
        raise ValueError("certificate levels must all be at least two")
    if any(left >= right for left, right in zip(level_tuple, level_tuple[1:])):
        raise ValueError("certificate levels must be strictly increasing")

    rows = []
    for level in level_tuple:
        certificate, vector, inputs = load_certificate(level)
        try:
            rows.append(audit_level(level, certificate, vector, inputs))
        finally:
            close_vector(vector)
            del vector
            gc.collect()

    return {
        "schema": SCHEMA,
        "worker_sha256": worker_sha256(),
        "scope": {
            "levels": list(level_tuple),
            "exact_finite_claim": (
                "For the theorem-derived rational six-chord ether cycle, every "
                "displayed D_E, W_E, and D_E/W_E is reconstructed exactly from "
                "the SHA-pinned stored KL certificate at that level; adjacent "
                "displayed ratios decrease by exact positive cross products."
            ),
            "nonclaim": (
                "Finite monotonicity at k=12..19 is not a k-to-infinity limit "
                "theorem, does not construct an infinite linked glider chain, "
                "and does not disprove Collatz."
            ),
        },
        "rational_cycle": cycle_theorem_record(),
        "rows": rows,
        "literal_level_12_crosscheck": (
            literal_level_twelve_crosscheck(
                next(row for row in rows if int(row["level"]) == 12)
            )
            if 12 in level_tuple
            else None
        ),
        "monotonicity": monotonicity_record(rows),
        "finite_evidence_only": True,
        "limit_theorem": None,
        "counterexample": None,
    }


def command_build(path: Path, levels: Sequence[int]) -> None:
    payload = canonical_bytes(build_artifact(levels))
    path.write_bytes(payload)
    print(f"wrote {path}")
    print(f"sha256 {hashlib.sha256(payload).hexdigest()}")


def command_verify(path: Path) -> None:
    advertised = json.loads(path.read_text())
    if advertised.get("schema") != SCHEMA:
        raise AssertionError("artifact schema mismatch")
    if advertised.get("worker_sha256") != worker_sha256():
        raise AssertionError("artifact worker SHA-256 mismatch")
    levels = advertised.get("scope", {}).get("levels")
    if not isinstance(levels, list):
        raise AssertionError("artifact has no reconstructible level list")
    expected = canonical_bytes(build_artifact([int(level) for level in levels]))
    actual = path.read_bytes()
    if actual != expected:
        raise AssertionError(f"artifact reconstruction mismatch: {path}")
    print(f"verified {path}")
    print(f"sha256 {hashlib.sha256(actual).hexdigest()}")


def command_selftest() -> None:
    centers = rational_cycle()
    expected = (
        Fraction(881, 473),
        Fraction(1490, 473),
        Fraction(1151, 473),
        Fraction(1850, 473),
        Fraction(1391, 473),
        Fraction(1085, 473),
        Fraction(881, 473),
    )
    if centers != expected:
        raise AssertionError("rational cycle regression changed")

    modulus = 3**5
    for index, branch in enumerate(WORD):
        source = rational_residue(-centers[index], modulus)
        target = rational_residue(-centers[index + 1], modulus)
        if target not in chord_fiber(source, branch, modulus):
            raise AssertionError("small-level rational fiber regression changed")

    mock_rows = [
        {"level": 2, "D_E_over_W_E": fraction_record(Fraction(7, 4))},
        {"level": 3, "D_E_over_W_E": fraction_record(Fraction(5, 3))},
        {"level": 4, "D_E_over_W_E": fraction_record(Fraction(3, 2))},
    ]
    record = monotonicity_record(mock_rows)
    if [row["positive_difference"] for row in record["comparisons"]] != [1, 1]:
        raise AssertionError("exact cross-product regression changed")
    print("selftest passed")


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    build_parser = subparsers.add_parser("build")
    build_parser.add_argument("artifact", nargs="?", type=Path, default=DEFAULT_ARTIFACT)
    build_parser.add_argument(
        "--levels", nargs="+", type=int, default=list(DEFAULT_LEVELS)
    )
    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("artifact", nargs="?", type=Path, default=DEFAULT_ARTIFACT)
    subparsers.add_parser("selftest")

    arguments = parser.parse_args()
    if arguments.command == "build":
        command_build(arguments.artifact, arguments.levels)
    elif arguments.command == "verify":
        command_verify(arguments.artifact)
    else:
        command_selftest()


if __name__ == "__main__":
    main()
