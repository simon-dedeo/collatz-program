#!/usr/bin/env python3
"""Invariant unit-collision slice of the capped splash hierarchy.

Every hierarchy level has a primitive register

    V = r + m*K,
    V = 2^(a*n+b)*g,
    V' = (3^(c*n+d)*g + s*17)/2^e.

Because m is odd and invertible modulo 17, exactly one packet class
``K=k0 (mod 17)`` makes V divisible by 17.  This class is invariant: writing
``V=17*H`` and ``g=17*h`` cancels the entire collision particle and gives

    H = 2^(a*n+b)*h,
    H' = (3^(c*n+d)*h + s)/2^e.

Thus the nonlocal splash leaves only unit debris ``+1`` or ``-1``.  This
verifier constructs the unit ISA at six finite hierarchy levels, compares its
complete affine branches coefficientwise with the corresponding mod-17
subcylinders of the parent +/-17 ISA, checks bounded members through the
public unit map, and literally replays bounded level-one members.  It supplies
no infinite unit orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

from breakoff_delay_gate import v2
from breakoff_ether_glider import glider_macro, replay_macro_member
from breakoff_renormalization import construct_hierarchy
from breakoff_superether import AffineMacro, RegisterISA, affine_macro


SCHEMA = "collatz-breakoff-unit-slice-v1"


@dataclass(frozen=True)
class UnitISA:
    level: int
    parent_packet_residue_mod_17: int
    register_offset: int
    register_stride: int
    binary_cell: int
    binary_offset: int
    ternary_cell: int
    ternary_offset: int
    division_exponent: int
    collision_sign: int


@dataclass(frozen=True)
class UnitBranch:
    cells: int
    input_packet_base: int
    input_packet_stride_exponent: int
    output_packet_base: int
    output_packet_stride: int
    parent_macro_tail_base: int
    parent_macro_tail_stride: int

    def member(self, tail: int) -> tuple[int, int]:
        if tail < 0:
            raise ValueError("unit branch tail must be nonnegative")
        return (
            self.input_packet_base
            + (1 << self.input_packet_stride_exponent) * tail,
            self.output_packet_base + self.output_packet_stride * tail,
        )


def unit_isa(parent: RegisterISA) -> UnitISA:
    if parent.register_stride % 17 == 0:
        raise ValueError("parent stride is not invertible modulo 17")
    residue = (
        -parent.register_offset * pow(parent.register_stride, -1, 17)
    ) % 17
    numerator = parent.register_offset + parent.register_stride * residue
    if numerator % 17:
        raise AssertionError("unit packet residue did not divide the register")
    return UnitISA(
        level=parent.level,
        parent_packet_residue_mod_17=residue,
        register_offset=numerator // 17,
        register_stride=parent.register_stride,
        binary_cell=parent.binary_cell,
        binary_offset=parent.binary_offset,
        ternary_cell=parent.ternary_cell,
        ternary_offset=parent.ternary_offset,
        division_exponent=parent.division_exponent,
        collision_sign=parent.collision_sign,
    )


def unit_branch(parent: RegisterISA, cells: int) -> UnitBranch:
    if cells < 1:
        raise ValueError("unit branch cell count must be positive")
    unit = unit_isa(parent)
    binary_exponent = unit.binary_cell * cells + unit.binary_offset
    ternary_exponent = unit.ternary_cell * cells + unit.ternary_offset
    invariant_residue = (
        unit.register_offset
        * pow(1 << binary_exponent, -1, unit.register_stride)
    ) % unit.register_stride
    execution_residue = (
        -unit.collision_sign
        * pow(pow(3, ternary_exponent), -1, 1 << unit.division_exponent)
    ) % (1 << unit.division_exponent)
    odd_base = invariant_residue + unit.register_stride * (
        (execution_residue - invariant_residue)
        * pow(unit.register_stride, -1, 1 << unit.division_exponent)
        % (1 << unit.division_exponent)
    )
    if odd_base == 0:
        odd_base = unit.register_stride * (1 << unit.division_exponent)
    if odd_base % 2 != 1:
        raise AssertionError("unit branch odd base is not odd")
    input_register = (1 << binary_exponent) * odd_base
    numerator = (
        pow(3, ternary_exponent) * odd_base + unit.collision_sign
    )
    if numerator % (1 << unit.division_exponent):
        raise AssertionError("unit branch missed its fixed division")
    output_register = numerator >> unit.division_exponent
    if (
        (input_register - unit.register_offset) % unit.register_stride
        or (output_register - unit.register_offset) % unit.register_stride
    ):
        raise AssertionError("unit branch lost its packet invariant")
    input_base = (
        input_register - unit.register_offset
    ) // unit.register_stride
    output_base = (
        output_register - unit.register_offset
    ) // unit.register_stride

    # Independently intersect the parent +/-17 branch with K=k0 (mod 17).
    parent_branch = affine_macro(parent, cells)
    parent_tail = (
        (unit.parent_packet_residue_mod_17 - parent_branch.input_packet_base)
        * pow(
            1 << parent_branch.input_packet_stride_exponent,
            -1,
            17,
        )
    ) % 17
    parent_input = parent_branch.input_packet_base + (
        (1 << parent_branch.input_packet_stride_exponent) * parent_tail
    )
    parent_output = (
        parent_branch.output_packet_base
        + parent_branch.output_packet_stride * parent_tail
    )
    if (
        parent_input % 17 != unit.parent_packet_residue_mod_17
        or parent_output % 17 != unit.parent_packet_residue_mod_17
    ):
        raise AssertionError("parent unit subcylinder is not invariant")
    if (
        (parent_input - unit.parent_packet_residue_mod_17) // 17
        != input_base
        or (parent_output - unit.parent_packet_residue_mod_17) // 17
        != output_base
    ):
        raise AssertionError("unit and parent branch bases disagree")
    result = UnitBranch(
        cells=cells,
        input_packet_base=input_base,
        input_packet_stride_exponent=parent_branch.input_packet_stride_exponent,
        output_packet_base=output_base,
        output_packet_stride=parent_branch.output_packet_stride,
        parent_macro_tail_base=parent_tail,
        parent_macro_tail_stride=17,
    )
    if result.output_packet_base <= result.input_packet_base:
        raise AssertionError("unit branch base is not outward")
    return result


def check_member(parent: RegisterISA, candidate: UnitBranch, tail: int) -> None:
    unit = unit_isa(parent)
    source, target = candidate.member(tail)
    source_register = unit.register_offset + unit.register_stride * source
    target_register = unit.register_offset + unit.register_stride * target
    exponent = unit.binary_cell * candidate.cells + unit.binary_offset
    if v2(source_register) != exponent:
        raise AssertionError("unit member has the wrong input valuation")
    odd = source_register >> exponent
    numerator = (
        pow(
            3,
            unit.ternary_cell * candidate.cells + unit.ternary_offset,
        )
        * odd
        + unit.collision_sign
    )
    if (
        numerator % (1 << unit.division_exponent)
        or numerator >> unit.division_exponent != target_register
    ):
        raise AssertionError("public unit map and affine member disagree")

    parent_tail = candidate.parent_macro_tail_base + 17 * tail
    parent_input, parent_output = affine_macro(parent, candidate.cells).member(
        parent_tail
    )
    residue = unit.parent_packet_residue_mod_17
    if (
        parent_input != residue + 17 * source
        or parent_output != residue + 17 * target
    ):
        raise AssertionError("unit member and parent subcylinder disagree")


def decimal_sha256(value: int) -> str:
    return hashlib.sha256(str(value).encode()).hexdigest()


def branch_digest(branches: list[UnitBranch]) -> str:
    payload = json.dumps(
        [asdict(branch) for branch in branches],
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    return hashlib.sha256(payload).hexdigest()


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("breakoff_renormalization.py"),
        Path(__file__).with_name("breakoff_superether.py"),
        Path(__file__).with_name("breakoff_ether_glider.py"),
        Path(__file__).with_name("breakoff_delay_gate.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def build_certificate(
    levels: int,
    max_cells: int,
    tails_per_branch: int,
    literal_level_one_cells: int,
) -> dict[str, object]:
    if min(levels, max_cells, tails_per_branch, literal_level_one_cells) < 1:
        raise ValueError("all unit-slice bounds must be positive")
    if literal_level_one_cells > max_cells:
        raise ValueError("literal replay bound exceeds branch bound")
    hierarchy, _ = construct_hierarchy(levels)
    level_records: list[dict[str, object]] = []
    checks = 0
    for parent in hierarchy:
        unit = unit_isa(parent)
        branches = [unit_branch(parent, n) for n in range(1, max_cells + 1)]
        for branch in branches:
            for tail in range(tails_per_branch):
                check_member(parent, branch, tail)
                checks += 1
        level_records.append(
            {
                "level": parent.level,
                "parent_packet_residue_mod_17": (
                    unit.parent_packet_residue_mod_17
                ),
                "collision_sign": unit.collision_sign,
                "unit_register_offset_decimal_digits": len(
                    str(abs(unit.register_offset))
                ),
                "unit_register_offset_decimal_sha256": decimal_sha256(
                    unit.register_offset
                ),
                "register_stride_decimal_digits": len(
                    str(unit.register_stride)
                ),
                "register_stride_decimal_sha256": decimal_sha256(
                    unit.register_stride
                ),
                "branch_digest_sha256": branch_digest(branches),
                "first_branch": {
                    key: str(value)
                    for key, value in asdict(branches[0]).items()
                },
                "last_branch": {
                    key: str(value)
                    for key, value in asdict(branches[-1]).items()
                },
            }
        )

    literal_replays = []
    parent = hierarchy[0]
    for cells in range(1, literal_level_one_cells + 1):
        candidate = unit_branch(parent, cells)
        for tail in range(min(2, tails_per_branch)):
            parent_tail = candidate.parent_macro_tail_base + 17 * tail
            literal_replays.append(
                replay_macro_member(glider_macro(cells), parent_tail)
            )
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact invariant V/17 unit slice for six finite hierarchy "
            "levels by default; bounded coefficient/member checks and "
            "bounded level-one literal replay; no infinite unit orbit"
        ),
        "unit_map": (
            "H=2^(a*n+b)h -> H'=(3^(c*n+d)h+s)/2^e"
        ),
        "bounds": {
            "levels": levels,
            "cells_per_level": [1, max_cells],
            "tails_per_branch": tails_per_branch,
            "literal_level_one_cells": [1, literal_level_one_cells],
        },
        "level_count": len(hierarchy),
        "branch_count": levels * max_cells,
        "exact_branch_members_checked": checks,
        "literal_level_one_members": len(literal_replays),
        "literal_lower_links_replayed": sum(
            replay.linked_members_replayed for replay in literal_replays
        ),
        "literal_gate_macros_replayed": sum(
            replay.literal_gate_macros_replayed for replay in literal_replays
        ),
        "levels": level_records,
    }


def selftest() -> None:
    hierarchy, _ = construct_hierarchy(2)
    first = unit_isa(hierarchy[0])
    if first.parent_packet_residue_mod_17 != 3:
        raise AssertionError("level-one unit packet residue changed")
    if first.register_offset != 4911712:
        raise AssertionError("level-one unit register offset changed")
    candidate = unit_branch(hierarchy[0], 1)
    check_member(hierarchy[0], candidate, 0)


def render(certificate: dict[str, object]) -> str:
    return json.dumps(certificate, indent=2, sort_keys=True) + "\n"


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(100_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--levels", type=int, default=6)
    build.add_argument("--max-cells", type=int, default=32)
    build.add_argument("--tails-per-branch", type=int, default=4)
    build.add_argument("--literal-level-one-cells", type=int, default=16)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("breakoff unit-slice selftest: PASS")
    elif args.command == "build":
        certificate = build_certificate(
            args.levels,
            args.max_cells,
            args.tails_per_branch,
            args.literal_level_one_cells,
        )
        args.output.write_text(render(certificate))
        print(f"wrote {args.output}")
    else:
        expected = json.loads(args.artifact.read_text())
        if expected.get("schema") != SCHEMA:
            raise ValueError("unexpected artifact schema")
        bounds = expected["bounds"]
        actual = build_certificate(
            int(bounds["levels"]),
            int(bounds["cells_per_level"][1]),
            int(bounds["tails_per_branch"]),
            int(bounds["literal_level_one_cells"][1]),
        )
        if actual != expected:
            raise AssertionError("artifact differs from exact recomputation")
        print("breakoff unit-slice artifact: PASS")


if __name__ == "__main__":
    main()
