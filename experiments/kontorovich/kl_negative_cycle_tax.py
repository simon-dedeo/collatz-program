#!/usr/bin/env python3
"""Exact KL escape-tax audit for three standard negative-cycle templates.

The Krasikov--Lagarias predecessor graph has three relevant edge types.  In
the positive center ``h=-m`` they are

    S:   h -> 4h,
    R2:  h -> (4h+2)/3  when h = 7 (mod 9),
    R8:  h -> (2h+1)/3  when h = 1 (mod 9).

The cycles encoded below are the predecessor presentations of the signed
shortcut-Collatz cycles through -1, -5, and -17.  This worker verifies those
integer identities, SHA-checks the certified KL feasible subeigenvectors at
levels 12 through 19, and compares the exact product of their non-minimal
fiber deviations with the corresponding certified lower edge weight.

This is a finite calibration diagnostic.  It neither classifies all negative
cycles nor proves a limiting eigenvector law or a positive counterexample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parents[2]
KL_DIR = ROOT / "experiments" / "kl"
DEFAULT_ARTIFACT = Path(__file__).with_name("kl_negative_cycle_tax_audit.json")
LEVELS = tuple(range(12, 20))

# Each pair is (center, outgoing KL predecessor edge).  The listed edge lands
# at the next center cyclically.
CYCLES = (
    {
        "name": "minus_one",
        "signed_cycle_seed": -1,
        "center_edges": ((1, "R8"),),
    },
    {
        "name": "minus_five",
        "signed_cycle_seed": -5,
        "center_edges": ((7, "R2"), (10, "R8")),
    },
    {
        "name": "minus_seventeen",
        "signed_cycle_seed": -17,
        "center_edges": (
            (25, "R2"),
            (34, "S"),
            (136, "R8"),
            (91, "R8"),
            (61, "R2"),
            (82, "R8"),
            (55, "R8"),
            (37, "R8"),
        ),
    },
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def reduced_pair(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def load_certificate(level: int) -> tuple[dict[str, Any], Any, dict[str, str]]:
    cert_path = KL_DIR / f"cert_k{level}.json"
    with cert_path.open() as handle:
        cert = json.load(handle)
    if cert["k"] != level:
        raise AssertionError(f"level mismatch in {cert_path}")

    inputs = {
        "certificate": str(cert_path.relative_to(ROOT)),
        "certificate_sha256": sha256(cert_path),
    }
    if "C" in cert:
        vector = cert["C"]
    else:
        vector_path = cert_path.with_name(cert["C_file"])
        actual_hash = sha256(vector_path)
        if actual_hash != cert["C_sha256"]:
            raise AssertionError(f"sidecar hash mismatch at level {level}")
        vector = np.load(vector_path, mmap_mode="r")
        inputs.update(
            {
                "vector": str(vector_path.relative_to(ROOT)),
                "vector_sha256": actual_hash,
            }
        )
    if len(vector) != 3 ** (level - 1):
        raise AssertionError(f"wrong vector length at level {level}")
    return cert, vector, inputs


def c_at(vector: Any, state: int) -> int:
    if state < 2 or state % 3 != 2:
        raise AssertionError(f"invalid KL state {state}")
    return int(vector[(state - 2) // 3])


def signed_syracuse(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def center_child(center: int, branch: str) -> int:
    if center <= 0 or center % 3 != 1:
        raise AssertionError(f"invalid positive center {center}")
    if branch == "S":
        return 4 * center
    if branch == "R2":
        if center % 9 != 7:
            raise AssertionError(f"R2 domain failure at center {center}")
        return (4 * center + 2) // 3
    if branch == "R8":
        if center % 9 != 1:
            raise AssertionError(f"R8 domain failure at center {center}")
        return (2 * center + 1) // 3
    raise AssertionError(f"unknown branch {branch}")


def edge_forward_length(branch: str) -> int:
    return 1 if branch == "R8" else 2


def signed_cycle(seed: int) -> list[int]:
    if seed >= 0:
        raise AssertionError("signed cycle seed must be negative")
    orbit = [seed]
    value = signed_syracuse(seed)
    while value != seed:
        if value in orbit or len(orbit) >= 100:
            raise AssertionError(f"failed to close signed cycle through {seed}")
        orbit.append(value)
        value = signed_syracuse(value)
    return orbit


def verify_template(template: dict[str, Any]) -> dict[str, Any]:
    edges = template["center_edges"]
    counts = {"R2": 0, "R8": 0, "S": 0}
    edge_checks = []
    for index, (center, branch) in enumerate(edges):
        child = center_child(center, branch)
        expected = edges[(index + 1) % len(edges)][0]
        if child != expected:
            raise AssertionError(
                f"{template['name']} edge {center} {branch} lands at {child}, "
                f"not {expected}"
            )
        value = -child
        forward = [value]
        for _ in range(edge_forward_length(branch)):
            value = signed_syracuse(value)
            forward.append(value)
        if value != -center:
            raise AssertionError("grouped predecessor edge failed signed semantics")
        counts[branch] += 1
        edge_checks.append(
            {
                "target_center": center,
                "branch": branch,
                "child_center": child,
                "signed_forward_segment": forward,
            }
        )

    chord_count = counts["R2"] + counts["R8"]
    time_cost = counts["R8"] + 2 * counts["R2"] + 2 * counts["S"]
    separator_left = 3**chord_count
    separator_right = 2**time_cost
    if separator_left <= separator_right:
        raise AssertionError(f"template {template['name']} is not outward")

    orbit = signed_cycle(template["signed_cycle_seed"])
    if template["signed_cycle_seed"] not in orbit:
        raise AssertionError("signed seed disappeared")
    return {
        "name": template["name"],
        "signed_cycle_seed": template["signed_cycle_seed"],
        "signed_shortcut_cycle": orbit,
        "center_edges": edge_checks,
        "counts": counts,
        "chord_count": chord_count,
        "time_cost": time_cost,
        "outward_separator": {
            "three_pow_chords": separator_left,
            "two_pow_time_cost": separator_right,
            "strict_margin": separator_left - separator_right,
        },
    }


def audit_cycle(
    template: dict[str, Any], level: int, cert: dict[str, Any], vector: Any
) -> dict[str, Any]:
    modulus = 3**level
    parent_modulus = 3 ** (level - 1)
    deviation_product = Fraction(1)
    weight_product = Fraction(1)
    edge_rows = []
    counts = {"R2": 0, "R8": 0, "S": 0}

    edges = template["center_edges"]
    for index, (center, branch) in enumerate(edges):
        child = edges[(index + 1) % len(edges)][0]
        if center_child(center, branch) != child:
            raise AssertionError("template changed after verification")
        source_state = (-center) % modulus

        if branch == "S":
            expected_child = (4 * source_state) % modulus
            desired_child = (-child) % modulus
            if expected_child != desired_child:
                raise AssertionError("transport residue mismatch")
            edge_weight = Fraction(cert["SC_L"], cert["A"]) ** 2
            weight_product *= edge_weight
            counts[branch] += 1
            edge_rows.append(
                {
                    "target_center": center,
                    "branch": branch,
                    "child_center": child,
                    "source_state": source_state,
                    "desired_child_state": desired_child,
                    "certified_weight_lower": reduced_pair(edge_weight),
                    "deviation_factor": reduced_pair(Fraction(1)),
                }
            )
            continue

        source_class = source_state % 9
        expected_class = 2 if branch == "R2" else 8
        if source_class != expected_class:
            raise AssertionError("branch residue class mismatch")
        if branch == "R2":
            coarse_child = ((4 * source_state - 2) // 3) % parent_modulus
            edge_weight = Fraction(cert["B2"], cert["SC_W"])
        else:
            coarse_child = ((2 * source_state - 1) // 3) % parent_modulus
            edge_weight = Fraction(cert["B8"], cert["SC_W"])

        lift_states = [coarse_child + digit * parent_modulus for digit in range(3)]
        desired_child = (-child) % modulus
        if desired_child not in lift_states:
            raise AssertionError("exact negative child is not in refinement fiber")
        lift_values = [c_at(vector, state) for state in lift_states]
        minimum = min(lift_values)
        desired_index = lift_states.index(desired_child)
        desired_value = lift_values[desired_index]
        deviation = Fraction(desired_value, minimum)
        deviation_product *= deviation
        weight_product *= edge_weight
        counts[branch] += 1
        edge_rows.append(
            {
                "target_center": center,
                "branch": branch,
                "child_center": child,
                "source_state": source_state,
                "coarse_child_state": coarse_child,
                "lift_states": lift_states,
                "lift_values": lift_values,
                "minimum_lift_index": lift_values.index(minimum),
                "desired_lift_index": desired_index,
                "desired_child_state": desired_child,
                "certified_weight_lower": reduced_pair(edge_weight),
                "deviation_factor": reduced_pair(deviation),
            }
        )

    surplus = deviation_product / weight_product
    if surplus <= 1:
        raise AssertionError(
            f"cycle {template['name']} misses the finite tax at level {level}"
        )
    return {
        "name": template["name"],
        "counts": counts,
        "edges": edge_rows,
        "deviation_product": reduced_pair(deviation_product),
        "certified_weight_product_lower": reduced_pair(weight_product),
        "deviation_over_weight": reduced_pair(surplus),
        "deviation_over_weight_decimal": format(float(surplus), ".15g"),
        "strict_surplus_numerator": surplus.numerator - surplus.denominator,
    }


def audit_level(level: int) -> dict[str, Any]:
    cert, vector, inputs = load_certificate(level)
    return {
        "level": level,
        "inputs": inputs,
        "lambda_lower": reduced_pair(Fraction(cert["A"], cert["SC_L"])),
        "cycles": [audit_cycle(template, level, cert, vector) for template in CYCLES],
    }


def build_artifact() -> dict[str, Any]:
    templates = [verify_template(template) for template in CYCLES]
    rows = [audit_level(level) for level in LEVELS]
    for cycle_index, template in enumerate(CYCLES):
        surpluses = [
            Fraction(
                row["cycles"][cycle_index]["deviation_over_weight"]["numerator"],
                row["cycles"][cycle_index]["deviation_over_weight"]["denominator"],
            )
            for row in rows
        ]
        if not all(left > right for left, right in zip(surpluses, surpluses[1:])):
            raise AssertionError(
                f"finite tax surplus is not decreasing for {template['name']}"
            )
    for row in rows:
        exact_surpluses = [
            Fraction(
                cycle["deviation_over_weight"]["numerator"],
                cycle["deviation_over_weight"]["denominator"],
            )
            for cycle in row["cycles"]
        ]
        if not exact_surpluses[0] < min(exact_surpluses[1:]):
            raise AssertionError("minus-one template is not the cheapest row")

    return {
        "schema": "kl-negative-cycle-tax-v1",
        "scope": {
            "levels": list(LEVELS),
            "exact_claim": (
                "The three displayed integer center cycles expand to the signed "
                "shortcut-Collatz cycles through -1, -5, and -17.  At every "
                "stored level, each exact deviation product strictly exceeds its "
                "certified rational lower edge-weight product, and each of the "
                "three eight-level surplus sequences is strictly decreasing."
            ),
            "finite_evidence": (
                "These negative cycles are finite KL near-equality templates; "
                "among the three, the minus-one template has the smallest "
                "observed surplus at every audited level."
            ),
            "nonclaim": (
                "The audit does not classify negative cycles, identify a critical "
                "eigenvector, prove convergence, construct an infinite positive "
                "orbit, or disprove the Collatz conjecture."
            ),
        },
        "templates": templates,
        "rows": rows,
        "all_strict": True,
        "all_surplus_sequences_strictly_decreasing": True,
        "minus_one_smallest_at_every_level": True,
        "counterexample": None,
    }


def canonical_bytes(value: dict[str, Any]) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def command_build(path: Path) -> None:
    payload = canonical_bytes(build_artifact())
    path.write_bytes(payload)
    print(f"wrote {path}")
    print(f"sha256 {hashlib.sha256(payload).hexdigest()}")


def command_verify(path: Path) -> None:
    expected = canonical_bytes(build_artifact())
    actual = path.read_bytes()
    if actual != expected:
        raise AssertionError(f"artifact mismatch: {path}")
    print(f"verified {path}")
    print(f"sha256 {hashlib.sha256(actual).hexdigest()}")


def command_selftest() -> None:
    templates = [verify_template(template) for template in CYCLES]
    expected_orbits = (
        [-1],
        [-5, -7, -10],
        [-17, -25, -37, -55, -82, -41, -61, -91, -136, -68, -34],
    )
    if [row["signed_shortcut_cycle"] for row in templates] != list(expected_orbits):
        raise AssertionError("signed-cycle regression changed")
    if any(template["outward_separator"]["strict_margin"] <= 0 for template in templates):
        raise AssertionError("outward separator regression changed")
    print("selftest passed")


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    build_parser = subparsers.add_parser("build")
    build_parser.add_argument("artifact", nargs="?", type=Path, default=DEFAULT_ARTIFACT)
    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("artifact", nargs="?", type=Path, default=DEFAULT_ARTIFACT)
    subparsers.add_parser("selftest")
    args = parser.parse_args()

    if args.command == "build":
        command_build(args.artifact)
    elif args.command == "verify":
        command_verify(args.artifact)
    else:
        command_selftest()


if __name__ == "__main__":
    main()
