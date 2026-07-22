#!/usr/bin/env python3
"""Compile an exact block of the divergent base-3/2 map into a splash link.

Eliahou--Verger-Gaugry's saturated-word map is

    U(n) = (3n+1)/2  for odd n,
           (3n+2)/2  for even n.

On a fixed D-bit binary address, ``U^D`` is affine with slope ``3^D``.
Two-rail index handoffs have slope ``3^R/2^D`` before the address is removed.
This checker finds and certifies a link with ``R=D=7`` whose target family
index is literally ``U^7`` of its source family index.

The target does not renew on the saturated orbit and the ordinary seed reaches
1.  This is an exact compiler primitive, not a counterexample.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict
from pathlib import Path

from two_rail_gate import two_rail_gate, verify_member
from two_rail_prefix_code import decode_payload
from two_rail_transducer import (
    continuation,
    index_instruction,
    universally_outward_on_instruction,
    verify_instruction,
)


SCHEMA = "collatz-two-rail-u-bridge-v1"


def saturated_step(value: int) -> int:
    if value < 0:
        raise ValueError("U expects a natural")
    return (3 * value + (1 if value % 2 else 2)) // 2


def saturated_iterate(value: int, steps: int) -> tuple[int, list[int]]:
    digits: list[int] = []
    for _ in range(steps):
        digit = 1 if value % 2 else 2
        digits.append(digit)
        value = (3 * value + digit) // 2
    return value, digits


def search_u_edges() -> tuple[int, list[dict[str, object]]]:
    bounds = {
        "max_source_amp_ticks": 10,
        "max_source_clean_ticks": 4,
        "max_source_collision_extra": 3,
        "max_source_output_gap": 11,
        "max_target_clean_ticks": 4,
        "max_target_collision_extra": 3,
    }
    checked = 0
    hits: list[dict[str, object]] = []
    for r in range(1, bounds["max_source_amp_ticks"] + 1):
        for s in range(bounds["max_source_clean_ticks"] + 1):
            power_three_exponent = r + s + 2
            for a in range(1, bounds["max_source_collision_extra"] + 1):
                for b in range(1, bounds["max_source_collision_extra"] + 1):
                    for output_gap in range(
                        2, bounds["max_source_output_gap"] + 1
                    ):
                        source = two_rail_gate(r, s, a, b, output_gap)
                        target_r = output_gap - 1
                        for target_s in range(
                            bounds["max_target_clean_ticks"] + 1
                        ):
                            for target_a in range(
                                1, bounds["max_target_collision_extra"] + 1
                            ):
                                for target_b in range(
                                    1,
                                    bounds["max_target_collision_extra"] + 1,
                                ):
                                    # Force target address bits D to equal R.
                                    target_output_gap = (
                                        power_three_exponent
                                        - target_a
                                        - target_b
                                        - 2 * target_s
                                        - 2
                                    )
                                    if target_output_gap < 2:
                                        continue
                                    target = two_rail_gate(
                                        target_r,
                                        target_s,
                                        target_a,
                                        target_b,
                                        target_output_gap,
                                    )
                                    instruction = index_instruction(source, target)
                                    checked += 1
                                    z, w = instruction.indices(0)
                                    u_value, digits = saturated_iterate(
                                        z, instruction.address_bits
                                    )
                                    if u_value == w:
                                        hits.append(
                                            {
                                                "source_shape": asdict(
                                                    instruction.source
                                                ),
                                                "target_shape": asdict(
                                                    instruction.target
                                                ),
                                                "address_bits": (
                                                    instruction.address_bits
                                                ),
                                                "source_index_base": z,
                                                "target_index_base": w,
                                                "U_digits": digits,
                                                "source_family_outward": (
                                                    universally_outward_on_instruction(
                                                        instruction
                                                    )
                                                ),
                                            }
                                        )
    return checked, hits


def build_certificate() -> dict[str, object]:
    source = two_rail_gate(5, 0, 2, 1, 2)
    target = two_rail_gate(1, 0, 2, 1, 2)
    instruction = index_instruction(source, target)
    verify_instruction(instruction, tails=64)
    if instruction.address_bits != 7:
        raise AssertionError("U bridge address length changed")

    z0, w0 = instruction.indices(0)
    u0, digits = saturated_iterate(z0, 7)
    if (z0, w0, u0, digits) != (95, 1640, 1640, [1, 1, 1, 1, 1, 2, 1]):
        raise AssertionError("U bridge base regression changed")

    # Universal affine identity on the accepted cylinder:
    # U^7(95+2^7*t)=1640+3^7*t.  Exact branch checks for t=0 and t=1
    # determine the two affine coefficients; the fixed seven parity digits
    # follow because the inputs agree modulo 2^7.
    for tail in range(64):
        z, w = instruction.indices(tail)
        value, tail_digits = saturated_iterate(z, 7)
        if value != w or tail_digits != digits:
            raise AssertionError("U bridge affine identity failed")

    start0, endpoint0 = verify_member(source, z0)
    start1, endpoint1 = verify_member(source, z0 + (1 << 7))
    if not start0 < endpoint0 or not start1 - start0 < endpoint1 - endpoint0:
        raise AssertionError("U bridge source family is not universally outward")

    # The saturated U orbit enters this address at time 41.
    saturated = 0
    for _ in range(41):
        saturated = saturated_step(saturated)
    if saturated != 26_906_975 or saturated % 128 != 95:
        raise AssertionError("saturated-orbit entry regression changed")
    saturated_after, saturated_digits = saturated_iterate(saturated, 7)
    if saturated_after != 459_730_910 or saturated_digits != digits:
        raise AssertionError("saturated U block regression changed")

    sat_start, sat_endpoint = verify_member(source, saturated)
    target_index = (saturated_after - target.input_payload_base)  # sentinel
    # The linked target family index is U^7(saturated), not a payload.
    if target_index == 0:
        raise AssertionError("index/payload sentinel unexpectedly vanished")
    linked_target_start, linked_target_endpoint = verify_member(
        target, saturated_after
    )
    if sat_endpoint != linked_target_start:
        raise AssertionError("saturated U bridge states do not link")
    renewal = decode_payload(target.output_gap - 1, target.payloads(saturated_after)[2])
    if renewal is not None:
        raise AssertionError("saturated witness unexpectedly renewed")

    checked, hits = search_u_edges()
    if checked != 67_500 or len(hits) != 3:
        raise AssertionError("bounded U-edge search regression changed")
    if sum(bool(hit["source_family_outward"]) for hit in hits) != 1:
        raise AssertionError("bounded outward U-edge count changed")

    return {
        "schema": SCHEMA,
        "claim_scope": (
            "exact U^7 compiler primitive on an unbounded affine family, "
            "plus a bounded shape search; not an infinite Collatz program"
        ),
        "base_3_over_2_map": {
            "definition": "U(n)=(3n+1)/2 odd; (3n+2)/2 even",
            "rational_base_action": "append digit 1 or 2",
            "U_is_divergent": True,
        },
        "source_gate": asdict(source),
        "target_gate": asdict(target),
        "instruction": asdict(instruction),
        "universal_index_identity": {
            "formula": "U^7(95+128*t)=1640+2187*t for every t>=0",
            "U_digits_little_time_order": digits,
            "tails_replayed": 64,
            "source_family_universally_outward": True,
        },
        "saturated_orbit_witness": {
            "source_U_time": 41,
            "source_index": saturated,
            "target_U_time": 48,
            "target_index": saturated_after,
            "collatz_source_state": sat_start,
            "collatz_target_state": sat_endpoint,
            "linked_target_gate_endpoint": linked_target_endpoint,
            "next_two_rail_renewal_exists": False,
            "ordinary_continuation": continuation(sat_start),
        },
        "bounded_shape_search": {
            "candidate_links_checked": checked,
            "exact_U_macro_links": len(hits),
            "outward_source_links": 1,
            "hits": hits,
        },
    }


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported artifact schema")
    if data != build_certificate():
        raise ValueError("U-bridge artifact failed exact reconstruction")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        saturated_iterate(0, 64)
        build_certificate()
        print("two_rail_u_bridge selftest: PASS")
    elif args.command == "build":
        args.output.write_text(json.dumps(build_certificate(), indent=2) + "\n")
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("two_rail_u_bridge artifact: PASS")


if __name__ == "__main__":
    main()
