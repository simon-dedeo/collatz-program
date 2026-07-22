#!/usr/bin/env python3
"""Exact self-regenerating hierarchy of the ``-5`` charge ISA.

Start with the level-two charge--discharge register

    G=2^(23*N+3)*g -> G'=(3^(17*N+97)*g-5)/2^128.

Compose its length-N branch with its one-cell branch.  If the current
ternary offset and division exponent are ``d,e``, the fixed debris is

    5*(3^(17+d)+2^(26+e)).

Whenever the factor in parentheses is coprime to the register stride, one
packet slice is divisible by it.  Dividing both endpoints preserves ``-5``
and gives the next ISA with

    d' = 2*d+17,       e' = 2*e+26.

Consequently

    d_j=114*2^j-17,    e_j=154*2^j-26,
    D_j=(3^114)^(2^j)+(2^154)^(2^j).

The coprimality test is finite for *all* j.  If a prime r != 3 dividing the
80-bit odd register stride also divided D_j, then the order of
3^114/2^154 modulo r would be divisible by 2^(j+1), so 2^(j+1)<stride.
It is therefore enough to check j=0,...,78 exactly; r=3 is immediate.

This verifier performs that all-depth check, builds bounded exact levels,
constructs every branch both by CRT and by restricted parent composition,
and recursively expands selected members to the original unit macros.  The
hierarchy is an arbitrarily deep finite compiler, not an infinite ordinary
orbit.  Indeed every child packet lifts to ``rho+D_j*K`` with K positive,
so a canonical infinite nesting changes and enlarges its ancestor packet.
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
from breakoff_superether import AffineMacro, link_macros
from unit_charge_discharge import (
    construct_isa as construct_base_isa,
    direct_branch as base_direct_branch,
    replay_member as replay_base_member,
)


SCHEMA = "collatz-unit-charge-hierarchy-v1"
COLLISION = 5


@dataclass(frozen=True)
class ChargeLevel:
    depth: int
    register_offset: int
    register_stride: int
    binary_cell: int
    binary_offset: int
    ternary_cell: int
    ternary_offset: int
    division_exponent: int


@dataclass(frozen=True)
class ChargeStep:
    parent_depth: int
    child_depth: int
    one_cell_ternary_exponent: int
    one_cell_total_binary_exponent: int
    removed_divisor: int
    packet_residue_mod_divisor: int
    child: ChargeLevel


@dataclass(frozen=True)
class ChargeBranch:
    cells: int
    input_packet_base: int
    input_packet_stride_exponent: int
    output_packet_base: int
    output_packet_stride: int
    parent_tail_base: int
    parent_tail_stride: int

    def member(self, tail: int) -> tuple[int, int]:
        if tail < 0:
            raise ValueError("charge tail must be nonnegative")
        return (
            self.input_packet_base
            + (1 << self.input_packet_stride_exponent) * tail,
            self.output_packet_base + self.output_packet_stride * tail,
        )


def as_macro(branch: ChargeBranch) -> AffineMacro:
    return AffineMacro(
        cells=branch.cells,
        input_packet_base=branch.input_packet_base,
        input_packet_stride_exponent=branch.input_packet_stride_exponent,
        output_packet_base=branch.output_packet_base,
        output_packet_stride=branch.output_packet_stride,
    )


def compose(first: ChargeBranch, second: ChargeBranch) -> AffineMacro:
    source_tail, target_tail = link_macros(as_macro(first), as_macro(second))
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


def base_level() -> ChargeLevel:
    base = construct_base_isa()
    return ChargeLevel(
        depth=0,
        register_offset=base.register_offset,
        register_stride=base.register_stride,
        binary_cell=base.binary_cell,
        binary_offset=base.binary_offset,
        ternary_cell=base.ternary_cell,
        ternary_offset=base.ternary_offset,
        division_exponent=base.division_exponent,
    )


def closed_offsets(depth: int) -> tuple[int, int]:
    if depth < 0:
        raise ValueError("charge depth must be nonnegative")
    scale = 1 << depth
    return 114 * scale - 17, 154 * scale - 26


def divisor_residue_mod_stride(depth: int, stride: int) -> int:
    ternary_offset, division = closed_offsets(depth)
    q_one = 17 + ternary_offset
    p_one = 26 + division
    return (pow(3, q_one, stride) + pow(2, p_one, stride)) % stride


def certify_all_depth_coprime(stride: int) -> list[dict[str, int]]:
    """Finite exact certificate for gcd(D_j,stride)=1 at every depth j."""
    if stride <= 1 or stride % 2 == 0:
        raise ValueError("charge stride must be odd and nontrivial")
    checks = []
    # If r | stride and r | D_j for r != 3, then 2^(j+1) | r-1 < stride.
    # Thus j+1 < bit_length(stride).  The prime r=3 never divides D_j.
    for depth in range(stride.bit_length() - 1):
        residue = divisor_residue_mod_stride(depth, stride)
        gcd = math.gcd(residue, stride)
        if gcd != 1:
            raise AssertionError("charge divisor met the register stride")
        ternary_offset, division = closed_offsets(depth)
        checks.append(
            {
                "depth": depth,
                "ternary_offset": ternary_offset,
                "division_exponent": division,
                "divisor_residue_mod_stride": residue,
                "gcd": gcd,
            }
        )
    return checks


def renormalize(parent: ChargeLevel) -> ChargeStep:
    q_one = parent.ternary_cell + parent.ternary_offset
    p_one = (
        parent.binary_cell
        + parent.binary_offset
        + parent.division_exponent
    )
    divisor = pow(3, q_one) + (1 << p_one)
    if math.gcd(divisor, parent.register_stride) != 1:
        raise AssertionError("recursive charge divisor is not transverse")
    residue = (
        -parent.register_offset
        * pow(parent.register_stride, -1, divisor)
    ) % divisor
    numerator = parent.register_offset + parent.register_stride * residue
    if numerator % divisor:
        raise AssertionError("recursive charge register did not divide")
    child = ChargeLevel(
        depth=parent.depth + 1,
        register_offset=numerator // divisor,
        register_stride=parent.register_stride,
        binary_cell=parent.binary_cell,
        binary_offset=parent.binary_offset,
        ternary_cell=parent.ternary_cell,
        ternary_offset=parent.ternary_offset + q_one,
        division_exponent=parent.division_exponent + p_one,
    )
    expected_d, expected_e = closed_offsets(child.depth)
    if (
        child.ternary_offset != expected_d
        or child.division_exponent != expected_e
    ):
        raise AssertionError("recursive charge exponents lost closed form")
    return ChargeStep(
        parent_depth=parent.depth,
        child_depth=child.depth,
        one_cell_ternary_exponent=q_one,
        one_cell_total_binary_exponent=p_one,
        removed_divisor=divisor,
        packet_residue_mod_divisor=residue,
        child=child,
    )


def construct_hierarchy(level_count: int) -> tuple[list[ChargeLevel], list[ChargeStep]]:
    if level_count < 1:
        raise ValueError("charge hierarchy needs at least one level")
    levels = [base_level()]
    steps = []
    certify_all_depth_coprime(levels[0].register_stride)
    while len(levels) < level_count:
        step = renormalize(levels[-1])
        steps.append(step)
        levels.append(step.child)
    return levels, steps


def direct_branch(level: ChargeLevel, cells: int) -> ChargeBranch:
    if cells < 1:
        raise ValueError("charge cell count must be positive")
    binary = level.binary_cell * cells + level.binary_offset
    ternary = level.ternary_cell * cells + level.ternary_offset
    invariant_residue = (
        level.register_offset
        * pow(1 << binary, -1, level.register_stride)
    ) % level.register_stride
    execution_residue = (
        COLLISION
        * pow(pow(3, ternary), -1, 1 << level.division_exponent)
    ) % (1 << level.division_exponent)
    odd_base = invariant_residue + level.register_stride * (
        (execution_residue - invariant_residue)
        * pow(level.register_stride, -1, 1 << level.division_exponent)
        % (1 << level.division_exponent)
    )
    if odd_base == 0:
        odd_base = level.register_stride * (1 << level.division_exponent)
    if odd_base % 2 != 1 or odd_base % 3 == 0:
        raise AssertionError("charge core base is not coprime to six")
    input_register = (1 << binary) * odd_base
    numerator = pow(3, ternary) * odd_base - COLLISION
    if numerator % (1 << level.division_exponent):
        raise AssertionError("charge branch missed fixed division")
    output_register = numerator >> level.division_exponent
    if (
        (input_register - level.register_offset) % level.register_stride
        or (output_register - level.register_offset) % level.register_stride
    ):
        raise AssertionError("charge branch lost register invariance")
    exponent = binary + level.division_exponent
    if pow(3, ternary) <= (1 << exponent):
        raise AssertionError("recursive charge branch is not outward")
    return ChargeBranch(
        cells=cells,
        input_packet_base=(
            input_register - level.register_offset
        ) // level.register_stride,
        input_packet_stride_exponent=exponent,
        output_packet_base=(
            output_register - level.register_offset
        ) // level.register_stride,
        output_packet_stride=pow(3, ternary),
        parent_tail_base=0,
        parent_tail_stride=0,
    )


def composed_branch(parent: ChargeLevel, step: ChargeStep, cells: int) -> ChargeBranch:
    if step.parent_depth != parent.depth:
        raise ValueError("charge step does not belong to parent")
    compiled = compose(direct_branch(parent, cells), direct_branch(parent, 1))
    modulus = step.removed_divisor
    residue = step.packet_residue_mod_divisor
    tail_base = (
        (residue - compiled.input_packet_base)
        * pow(1 << compiled.input_packet_stride_exponent, -1, modulus)
    ) % modulus
    input_packet = compiled.input_packet_base + (
        (1 << compiled.input_packet_stride_exponent) * tail_base
    )
    output_packet = (
        compiled.output_packet_base + compiled.output_packet_stride * tail_base
    )
    if input_packet % modulus != residue or output_packet % modulus != residue:
        raise AssertionError("recursive composition lost divisor slice")
    candidate = ChargeBranch(
        cells=cells,
        input_packet_base=(input_packet - residue) // modulus,
        input_packet_stride_exponent=compiled.input_packet_stride_exponent,
        output_packet_base=(output_packet - residue) // modulus,
        output_packet_stride=compiled.output_packet_stride,
        parent_tail_base=tail_base,
        parent_tail_stride=modulus,
    )
    direct = direct_branch(step.child, cells)
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
        raise AssertionError("direct and composed recursive branches disagree")
    return candidate


def locate_tail(branch: ChargeBranch, packet: int) -> int:
    difference = packet - branch.input_packet_base
    stride = 1 << branch.input_packet_stride_exponent
    if difference < 0 or difference % stride:
        raise AssertionError("packet missed recursive charge branch")
    return difference // stride


def replay_direct(level: ChargeLevel, cells: int, packet: int) -> tuple[int, int]:
    branch = direct_branch(level, cells)
    tail = locate_tail(branch, packet)
    source, target = branch.member(tail)
    source_register = level.register_offset + level.register_stride * source
    target_register = level.register_offset + level.register_stride * target
    binary = level.binary_cell * cells + level.binary_offset
    ternary = level.ternary_cell * cells + level.ternary_offset
    if v2(source_register) != binary:
        raise AssertionError("recursive charge input valuation is not exact")
    core = source_register >> binary
    numerator = pow(3, ternary) * core - COLLISION
    if (
        numerator % (1 << level.division_exponent)
        or numerator >> level.division_exponent != target_register
    ):
        raise AssertionError("recursive charge public recurrence failed")
    if target_register <= source_register:
        raise AssertionError("recursive charge member is not outward")
    return target, tail


def expand_member(
    levels: list[ChargeLevel],
    steps: list[ChargeStep],
    depth: int,
    cells: int,
    packet: int,
) -> dict[str, int]:
    target, tail = replay_direct(levels[depth], cells, packet)
    if depth == 0:
        base_isa = construct_base_isa()
        base_branch = base_direct_branch(base_isa, cells)
        base_tail = locate_tail(
            ChargeBranch(
                cells=base_branch.cells,
                input_packet_base=base_branch.input_packet_base,
                input_packet_stride_exponent=base_branch.input_packet_stride_exponent,
                output_packet_base=base_branch.output_packet_base,
                output_packet_stride=base_branch.output_packet_stride,
                parent_tail_base=0,
                parent_tail_stride=0,
            ),
            packet,
        )
        replay_base_member(base_branch, base_tail)
        return {
            "output_packet": target,
            "level_zero_charge_macros": 1,
            "original_unit_macros": 2,
            "maximum_packet_bits": max(packet.bit_length(), target.bit_length()),
        }

    step = steps[depth - 1]
    parent = levels[depth - 1]
    lifted_input = step.packet_residue_mod_divisor + step.removed_divisor * packet
    lifted_output = step.packet_residue_mod_divisor + step.removed_divisor * target
    first_target, _ = replay_direct(parent, cells, lifted_input)
    second_target, _ = replay_direct(parent, 1, first_target)
    if second_target != lifted_output:
        raise AssertionError("recursive expansion disagrees with child endpoint")
    first = expand_member(levels, steps, depth - 1, cells, lifted_input)
    second = expand_member(levels, steps, depth - 1, 1, first_target)
    if first["output_packet"] != first_target or second["output_packet"] != second_target:
        raise AssertionError("recursive subexpansion lost an endpoint")
    return {
        "output_packet": target,
        "level_zero_charge_macros": (
            first["level_zero_charge_macros"]
            + second["level_zero_charge_macros"]
        ),
        "original_unit_macros": (
            first["original_unit_macros"] + second["original_unit_macros"]
        ),
        "maximum_packet_bits": max(
            packet.bit_length(),
            target.bit_length(),
            first["maximum_packet_bits"],
            second["maximum_packet_bits"],
        ),
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("unit_charge_discharge.py"),
        Path(__file__).with_name("breakoff_unit_slice.py"),
        Path(__file__).with_name("breakoff_renormalization.py"),
        Path(__file__).with_name("breakoff_superether.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def build_certificate(
    level_count: int = 8, cell_bound: int = 8, tails: int = 2
) -> dict[str, object]:
    if min(level_count, cell_bound, tails) < 1:
        raise ValueError("charge hierarchy audit bounds must be positive")
    levels, steps = construct_hierarchy(level_count)
    coprime = certify_all_depth_coprime(levels[0].register_stride)
    branches = []
    members = []
    for depth, level in enumerate(levels):
        for cells in range(1, cell_bound + 1):
            direct = direct_branch(level, cells)
            if depth:
                candidate = composed_branch(levels[depth - 1], steps[depth - 1], cells)
            else:
                candidate = direct
            branches.append(
                {
                    "depth": depth,
                    **asdict(candidate),
                }
            )
            for tail in range(tails):
                source, target = direct.member(tail)
                replayed_target, located_tail = replay_direct(level, cells, source)
                if replayed_target != target or located_tail != tail:
                    raise AssertionError("bounded recursive member replay failed")
                members.append(
                    {
                        "depth": depth,
                        "cells": cells,
                        "tail": tail,
                        "input_packet_bits": source.bit_length(),
                        "output_packet_bits": target.bit_length(),
                        "strict_outwardness_checked": True,
                    }
                )

    expansions = []
    for depth, level in enumerate(levels):
        cells = depth + 1
        branch = direct_branch(level, cells)
        source, target = branch.member(0)
        replay = expand_member(levels, steps, depth, cells, source)
        if replay["output_packet"] != target:
            raise AssertionError("canonical recursive expansion failed")
        expansions.append(
            {
                "depth": depth,
                "cells": cells,
                "input_packet_bits": source.bit_length(),
                "output_packet_bits": target.bit_length(),
                "maximum_expanded_packet_bits": replay["maximum_packet_bits"],
                "level_zero_charge_macros": replay["level_zero_charge_macros"],
                "original_unit_macros": replay["original_unit_macros"],
            }
        )

    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact all-depth coprimality and formula-level recursive -5 "
            "charge constructor; bounded levels compare direct CRT branches "
            "with restricted parent compositions and selected members expand "
            "to original unit macros; no infinite ordinary orbit is claimed"
        ),
        "closed_forms": {
            "ternary_offset": "114*2^depth-17",
            "division_exponent": "154*2^depth-26",
            "removed_divisor": "3^(114*2^depth)+2^(154*2^depth)",
            "public_map": (
                "G=2^(23*N+3)*g -> "
                "G'=(3^(17*N+114*2^depth-17)*g-5)/"
                "2^(154*2^depth-26)"
            ),
        },
        "all_depth_coprime_argument": {
            "register_stride": levels[0].register_stride,
            "register_stride_bit_length": levels[0].register_stride.bit_length(),
            "checked_depth_min": 0,
            "checked_depth_max": len(coprime) - 1,
            "exact_gcd_checks": coprime,
            "order_bound": (
                "a prime r!=3 dividing a failed depth j would satisfy "
                "2^(j+1)|r-1<register_stride; r=3 never divides the divisor"
            ),
        },
        "ordinary_nesting_obstruction": (
            "at every recursive step a positive child packet K lifts to "
            "rho+D*K with D>1, hence exceeds K; an infinite canonical "
            "nesting cannot stabilize to one ordinary packet"
        ),
        "bounds": {
            "level_count": level_count,
            "cell_bound": cell_bound,
            "members_per_branch": tails,
            "branches": len(branches),
            "members": len(members),
            "recursive_expansions": len(expansions),
            "expanded_original_unit_macros": sum(
                row["original_unit_macros"] for row in expansions
            ),
        },
        "levels": [asdict(level) for level in levels],
        "steps": [asdict(step) for step in steps],
        "branches": branches,
        "members": members,
        "recursive_expansions": expansions,
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported charge hierarchy schema")
    bounds = data["bounds"]
    expected = build_certificate(
        int(bounds["level_count"]),
        int(bounds["cell_bound"]),
        int(bounds["members_per_branch"]),
    )
    if data != expected:
        raise ValueError("charge hierarchy artifact failed reconstruction")


def selftest() -> None:
    levels, steps = construct_hierarchy(3)
    assert closed_offsets(0) == (97, 128)
    assert closed_offsets(1) == (211, 282)
    assert len(certify_all_depth_coprime(levels[0].register_stride)) == 79
    for depth, level in enumerate(levels):
        for cells in (1, 2, 5):
            branch = direct_branch(level, cells)
            source, target = branch.member(0)
            replayed, _ = replay_direct(level, cells, source)
            assert replayed == target
            if depth:
                composed_branch(levels[depth - 1], steps[depth - 1], cells)
    branch = direct_branch(levels[2], 3)
    source, _ = branch.member(0)
    expansion = expand_member(levels, steps, 2, 3, source)
    assert expansion["level_zero_charge_macros"] == 4
    assert expansion["original_unit_macros"] == 8


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(500_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--level-count", type=int, default=8)
    build.add_argument("--cell-bound", type=int, default=8)
    build.add_argument("--tails", type=int, default=2)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("unit charge hierarchy selftest: PASS")
    elif args.command == "build":
        data = build_certificate(args.level_count, args.cell_bound, args.tails)
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit charge hierarchy artifact: PASS")


if __name__ == "__main__":
    main()
