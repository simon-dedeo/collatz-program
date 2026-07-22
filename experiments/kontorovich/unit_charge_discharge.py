#!/usr/bin/env python3
"""Exact charge--discharge ``-5`` slice of the level-two unit ISA.

At sign-negative hierarchy level two, compose a length-N unit instruction
with the one-cell instruction.  Eliminating the intermediate core gives

    2^(p(N')+p(1))*h'
      =3^(q(N)+q(1))*h-(3^q(1)+2^p(1)).

The fixed debris factors as

    3^57+2^77 = 5*D,
    D=314038802961906688057474567.

Since D is coprime to the odd unit-register stride, one unique packet class
makes the public register divisible by D, and the class is invariant under
the two-step composition.  Dividing by D produces the autonomous public map

    G=2^(23N+3)g  ->  G'=(3^(17N+97)g-5)/2^128.

This worker constructs its complete affine branches directly by CRT and
independently by composing and restricting the two existing unit branches.
It proves a small exact counterexample interface: every successful branch is
strictly outward, so any infinite orbit in this ISA would refute Collatz.
No such orbit is supplied.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

from breakoff_delay_gate import v2
from breakoff_renormalization import construct_hierarchy
from breakoff_superether import AffineMacro, link_macros
from breakoff_unit_slice import UnitBranch, unit_branch, unit_isa


SCHEMA = "collatz-unit-charge-discharge-v1"


@dataclass(frozen=True)
class ChargeISA:
    parent_level: int
    packet_residue_mod_divisor: int
    removed_divisor: int
    residual_collision_constant: int
    register_offset: int
    register_stride: int
    binary_cell: int
    binary_offset: int
    ternary_cell: int
    ternary_offset: int
    division_exponent: int


@dataclass(frozen=True)
class ChargeBranch:
    cells: int
    input_packet_base: int
    input_packet_stride_exponent: int
    output_packet_base: int
    output_packet_stride: int
    composed_tail_base: int
    composed_tail_stride: int

    def member(self, tail: int) -> tuple[int, int]:
        if tail < 0:
            raise ValueError("charge tail must be nonnegative")
        return (
            self.input_packet_base
            + (1 << self.input_packet_stride_exponent) * tail,
            self.output_packet_base + self.output_packet_stride * tail,
        )


def as_macro(branch: UnitBranch) -> AffineMacro:
    return AffineMacro(
        cells=branch.cells,
        input_packet_base=branch.input_packet_base,
        input_packet_stride_exponent=branch.input_packet_stride_exponent,
        output_packet_base=branch.output_packet_base,
        output_packet_stride=branch.output_packet_stride,
    )


def compose(first: AffineMacro, second: AffineMacro) -> AffineMacro:
    source_tail, target_tail = link_macros(first, second)
    return AffineMacro(
        cells=first.cells + second.cells,
        input_packet_base=(
            first.input_packet_base
            + (1 << first.input_packet_stride_exponent) * source_tail
        ),
        input_packet_stride_exponent=(
            first.input_packet_stride_exponent
            + second.input_packet_stride_exponent
        ),
        output_packet_base=(
            second.output_packet_base
            + second.output_packet_stride * target_tail
        ),
        output_packet_stride=(
            first.output_packet_stride * second.output_packet_stride
        ),
    )


def construct_isa() -> ChargeISA:
    hierarchy, _ = construct_hierarchy(6)
    parent = hierarchy[1]
    unit = unit_isa(parent)
    if unit.level != 2 or unit.collision_sign != -1:
        raise AssertionError("charge ISA requires sign-negative level two")
    one_binary = unit.binary_cell + unit.binary_offset + unit.division_exponent
    one_ternary = unit.ternary_cell + unit.ternary_offset
    debris = pow(3, one_ternary) + (1 << one_binary)
    residual = 5
    if debris % residual:
        raise AssertionError("two-step debris lost its factor five")
    divisor = debris // residual
    if math.gcd(divisor, unit.register_stride) != 1:
        raise AssertionError("debris divisor is not transverse to the register")
    packet_residue = (
        -unit.register_offset * pow(unit.register_stride, -1, divisor)
    ) % divisor
    numerator = unit.register_offset + unit.register_stride * packet_residue
    if numerator % divisor:
        raise AssertionError("charge register did not divide by its debris")
    result = ChargeISA(
        parent_level=unit.level,
        packet_residue_mod_divisor=packet_residue,
        removed_divisor=divisor,
        residual_collision_constant=residual,
        register_offset=numerator // divisor,
        register_stride=unit.register_stride,
        binary_cell=unit.binary_cell,
        binary_offset=unit.binary_offset,
        ternary_cell=unit.ternary_cell,
        ternary_offset=unit.ternary_offset + one_ternary,
        division_exponent=unit.division_exponent + one_binary,
    )
    if (
        result.ternary_offset != 97
        or result.division_exponent != 128
        or result.binary_cell != 23
        or result.binary_offset != 3
        or result.ternary_cell != 17
    ):
        raise AssertionError("charge ISA parameters changed")
    return result


def direct_branch(isa: ChargeISA, cells: int) -> ChargeBranch:
    if cells < 1:
        raise ValueError("charge cell count must be positive")
    binary = isa.binary_cell * cells + isa.binary_offset
    ternary = isa.ternary_cell * cells + isa.ternary_offset
    invariant_residue = (
        isa.register_offset
        * pow(1 << binary, -1, isa.register_stride)
    ) % isa.register_stride
    execution_residue = (
        isa.residual_collision_constant
        * pow(pow(3, ternary), -1, 1 << isa.division_exponent)
    ) % (1 << isa.division_exponent)
    odd_base = invariant_residue + isa.register_stride * (
        (execution_residue - invariant_residue)
        * pow(isa.register_stride, -1, 1 << isa.division_exponent)
        % (1 << isa.division_exponent)
    )
    if odd_base == 0:
        odd_base = isa.register_stride * (1 << isa.division_exponent)
    if odd_base % 2 != 1 or odd_base % 3 == 0:
        raise AssertionError("charge core base is not coprime to six")
    input_register = (1 << binary) * odd_base
    numerator = pow(3, ternary) * odd_base - isa.residual_collision_constant
    if numerator % (1 << isa.division_exponent):
        raise AssertionError("charge branch missed its fixed division")
    output_register = numerator >> isa.division_exponent
    if (
        (input_register - isa.register_offset) % isa.register_stride
        or (output_register - isa.register_offset) % isa.register_stride
    ):
        raise AssertionError("charge branch lost register invariance")
    exponent = binary + isa.division_exponent
    if not pow(3, ternary) > (1 << exponent):
        raise AssertionError("charge branch lost its amplifying slope")
    if output_register <= input_register:
        raise AssertionError("charge branch base is not outward")
    return ChargeBranch(
        cells=cells,
        input_packet_base=(
            input_register - isa.register_offset
        ) // isa.register_stride,
        input_packet_stride_exponent=exponent,
        output_packet_base=(
            output_register - isa.register_offset
        ) // isa.register_stride,
        output_packet_stride=pow(3, ternary),
        composed_tail_base=0,
        composed_tail_stride=0,
    )


def composed_branch(cells: int) -> ChargeBranch:
    hierarchy, _ = construct_hierarchy(6)
    parent = hierarchy[1]
    unit = unit_isa(parent)
    isa = construct_isa()
    first = unit_branch(parent, cells)
    second = unit_branch(parent, 1)
    compiled = compose(as_macro(first), as_macro(second))
    modulus = isa.removed_divisor
    tail_base = (
        (isa.packet_residue_mod_divisor - compiled.input_packet_base)
        * pow(1 << compiled.input_packet_stride_exponent, -1, modulus)
    ) % modulus
    input_packet = compiled.input_packet_base + (
        (1 << compiled.input_packet_stride_exponent) * tail_base
    )
    output_packet = (
        compiled.output_packet_base + compiled.output_packet_stride * tail_base
    )
    residue = isa.packet_residue_mod_divisor
    if input_packet % modulus != residue or output_packet % modulus != residue:
        raise AssertionError("composed unit pair lost the divisor slice")
    candidate = ChargeBranch(
        cells=cells,
        input_packet_base=(input_packet - residue) // modulus,
        input_packet_stride_exponent=compiled.input_packet_stride_exponent,
        output_packet_base=(output_packet - residue) // modulus,
        output_packet_stride=compiled.output_packet_stride,
        composed_tail_base=tail_base,
        composed_tail_stride=modulus,
    )
    direct = direct_branch(isa, cells)
    if (
        candidate.cells,
        candidate.input_packet_base,
        candidate.input_packet_stride_exponent,
        candidate.output_packet_base,
        candidate.output_packet_stride,
    ) != (
        direct.cells,
        direct.input_packet_base,
        direct.input_packet_stride_exponent,
        direct.output_packet_base,
        direct.output_packet_stride,
    ):
        raise AssertionError("direct and composed charge branches disagree")
    if unit.collision_sign != -1:
        raise AssertionError("parent unit sign changed")
    return candidate


def locate_tail(branch: UnitBranch, packet: int) -> int:
    difference = packet - branch.input_packet_base
    stride = 1 << branch.input_packet_stride_exponent
    if difference < 0 or difference % stride:
        raise AssertionError("packet missed a unit branch")
    return difference // stride


def replay_member(candidate: ChargeBranch, tail: int) -> dict[str, object]:
    hierarchy, _ = construct_hierarchy(6)
    parent = hierarchy[1]
    unit = unit_isa(parent)
    isa = construct_isa()
    input_packet, output_packet = candidate.member(tail)
    original_input = (
        isa.packet_residue_mod_divisor
        + isa.removed_divisor * input_packet
    )
    original_output = (
        isa.packet_residue_mod_divisor
        + isa.removed_divisor * output_packet
    )
    first = unit_branch(parent, candidate.cells)
    second = unit_branch(parent, 1)
    first_tail = locate_tail(first, original_input)
    first_input, intermediate = first.member(first_tail)
    second_tail = locate_tail(second, intermediate)
    second_input, second_output = second.member(second_tail)
    if (
        first_input != original_input
        or second_input != intermediate
        or second_output != original_output
    ):
        raise AssertionError("two-unit charge replay failed")

    input_register = isa.register_offset + isa.register_stride * input_packet
    output_register = isa.register_offset + isa.register_stride * output_packet
    binary = isa.binary_cell * candidate.cells + isa.binary_offset
    if v2(input_register) != binary:
        raise AssertionError("charge input has the wrong public valuation")
    core = input_register >> binary
    numerator = (
        pow(3, isa.ternary_cell * candidate.cells + isa.ternary_offset) * core
        - isa.residual_collision_constant
    )
    if (
        numerator % (1 << isa.division_exponent)
        or numerator >> isa.division_exponent != output_register
    ):
        raise AssertionError("charge public recurrence failed")
    if output_register <= input_register:
        raise AssertionError("charge member is not outward")
    return {
        "cells": candidate.cells,
        "tail": tail,
        "input_packet_bits": input_packet.bit_length(),
        "intermediate_packet_bits": intermediate.bit_length(),
        "output_packet_bits": output_packet.bit_length(),
        "first_unit_tail_bits": first_tail.bit_length(),
        "second_unit_tail_bits": second_tail.bit_length(),
        "two_unit_macros_replayed": 2,
        "public_charge_recurrence_checked": True,
        "strict_outwardness_checked": True,
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("breakoff_unit_slice.py"),
        Path(__file__).with_name("breakoff_renormalization.py"),
        Path(__file__).with_name("breakoff_superether.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def build_certificate(cell_bound: int = 32, tails: int = 4) -> dict[str, object]:
    if min(cell_bound, tails) < 1:
        raise ValueError("charge audit bounds must be positive")
    isa = construct_isa()
    branches = []
    replays = []
    for cells in range(1, cell_bound + 1):
        branch = composed_branch(cells)
        branches.append(asdict(branch))
        for tail in range(tails):
            replays.append(replay_member(branch, tail))
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact research-side autonomous -5 charge--discharge ISA at "
            "finite hierarchy level two; direct CRT branches are compared "
            "with restricted two-unit compositions and bounded members are "
            "replayed; no infinite orbit is claimed"
        ),
        "isa": asdict(isa),
        "public_map": (
            "G=2^(23*N+3)*g -> G'=(3^(17*N+97)*g-5)/2^128"
        ),
        "conditional_disproof": (
            "an infinite successful positive charge-ISA orbit is a strictly "
            "outward ordinary Collatz macro-orbit and refutes Collatz"
        ),
        "bounds": {
            "cell_bound": cell_bound,
            "members_per_branch": tails,
            "branches": len(branches),
            "two_unit_macro_replays": 2 * len(replays),
        },
        "branches": branches,
        "replays": replays,
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported charge-discharge schema")
    bounds = data["bounds"]
    expected = build_certificate(
        int(bounds["cell_bound"]), int(bounds["members_per_branch"])
    )
    if data != expected:
        raise ValueError("charge-discharge artifact failed reconstruction")


def selftest() -> None:
    construct_isa()
    for cells in (1, 2, 7):
        branch = composed_branch(cells)
        replay_member(branch, 0)
        replay_member(branch, 1)


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(200_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--cell-bound", type=int, default=32)
    build.add_argument("--tails", type=int, default=4)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("unit charge-discharge selftest: PASS")
    elif args.command == "build":
        data = build_certificate(args.cell_bound, args.tails)
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit charge-discharge artifact: PASS")


if __name__ == "__main__":
    main()
