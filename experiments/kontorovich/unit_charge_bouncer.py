#!/usr/bin/env python3
"""Exact fixed-form bouncer inside the level-two ``-5`` charge ISA.

For the charge register G, put

    A=3^114, B=2^154, F=(A-B)/5,
    Z=F*G-2^26.

The one-cell charge instruction is exactly the homogeneous delay wire

    B*Z' = A*Z.

A defect instruction of length N=m+1 satisfies

    2^(154+23m) Z'
      =3^(114+17m) Z + 2^26*A*(3^(17m)-2^(23m)).

At a defect boundary Z=2^26*y.  Write C=3^17 and D=2^23.  The state itself
then selects

    m = v2(y+1)/23,
    E = C^m*(y+1)-D^m,
    h = (v2(E)-23m)/154.

When m,h are positive integers, the defect followed by h-1 background cells
returns

    y' = A^h * E/2^(23m+154h).

Continuation requires v2(y'+1) to be another positive multiple of 23.
The fixed register is encoded by y=0 (mod M), y=-1 (mod F), where

    M=3^33*(3^17-2^23).

This worker constructs complete bounded transition families in two ways:
the displayed partial map and literal compositions of charge branches.  It
replays every bounded member through the charge layer and its underlying two
unit macros.  The map is exactly reversible on accepted transitions:
``v3(y')=114h`` and, after removing that power, the predecessor count is read
from one further 3-adic valuation.  Any infinite accepted positive y-orbit
would be an infinite outward ordinary Collatz macro-orbit.  No such orbit is
supplied.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

from breakoff_delay_gate import v2
from breakoff_superether import AffineMacro, link_macros
from unit_charge_discharge import (
    ChargeBranch,
    construct_isa,
    direct_branch,
    replay_member as replay_charge_member,
)


SCHEMA = "collatz-unit-charge-bouncer-v1"
A = pow(3, 114)
B = 1 << 154
C = pow(3, 17)
D = 1 << 23
DELTA = C - D
F = (A - B) // 5
TWO_26 = 1 << 26


@dataclass(frozen=True)
class BouncerTransition:
    input_defect_cells: int
    background_cells: int
    output_defect_cells: int
    input_packet_base: int
    input_packet_stride_exponent: int
    output_packet_base: int
    output_packet_stride: int
    block_source_tail_base: int
    next_defect_tail_base: int

    def member(self, tail: int) -> tuple[int, int]:
        if tail < 0:
            raise ValueError("bouncer tail must be nonnegative")
        return (
            self.input_packet_base
            + (1 << self.input_packet_stride_exponent) * tail,
            self.output_packet_base + self.output_packet_stride * tail,
        )


@dataclass(frozen=True)
class BouncerStep:
    input_defect_cells: int
    background_cells: int
    output_defect_cells: int
    first_valuation: int
    collision_valuation: int
    input_y: int
    output_y: int


def vp(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("valuation of zero is not used")
    exponent = 0
    value = abs(value)
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def as_macro(branch: ChargeBranch) -> AffineMacro:
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


def constants() -> dict[str, int]:
    isa = construct_isa()
    if A - B != 5 * F or F <= 0:
        raise AssertionError("fixed-form denominator identity failed")
    if isa.register_stride != pow(3, 33) * DELTA:
        raise AssertionError("charge stride lost its difference factor")
    if (F * isa.register_offset - TWO_26) % isa.register_stride:
        raise AssertionError("fixed form is not integral on the register")
    if pow(D, 154) != pow(B, 23):
        raise AssertionError("binary bouncer exponents lost rank-one relation")
    if pow(A, 23) != 81 * pow(C, 154):
        raise AssertionError("ternary bouncer determinant is no longer four")
    return {
        "A": A,
        "B": B,
        "C": C,
        "D": D,
        "delta": DELTA,
        "F": F,
        "M": isa.register_stride,
        "register_offset": isa.register_offset,
        "fixed_form_packet_offset": (
            F * isa.register_offset - TWO_26
        ) // isa.register_stride,
    }


def packet_to_y(packet: int) -> int:
    if packet < 0:
        raise ValueError("charge packet must be nonnegative")
    isa = construct_isa()
    register = isa.register_offset + isa.register_stride * packet
    numerator = F * register - TWO_26
    if numerator % TWO_26:
        raise ValueError("packet is not at a defect boundary")
    y = numerator // TWO_26
    if y <= 0:
        raise ValueError("bouncer state must be positive")
    return y


def defect_phase(y: int) -> int:
    values = constants()
    if y <= 0 or y % 2 != 1:
        raise ValueError("bouncer state must be positive and odd")
    if y % values["M"] or (y + 1) % F:
        raise ValueError("bouncer state missed its fixed register")
    exponent = v2(y + 1)
    if exponent < 23 or exponent % 23:
        raise ValueError("bouncer state has no defect opcode")
    return exponent // 23


def bouncer_step(y: int) -> BouncerStep:
    m = defect_phase(y)
    collision = pow(C, m) * (y + 1) - pow(D, m)
    if collision <= 0:
        raise AssertionError("positive bouncer collision became nonpositive")
    collision_valuation = v2(collision)
    difference = collision_valuation - 23 * m
    if difference < 154 or difference % 154:
        raise ValueError("bouncer collision did not expose a whole background block")
    h = difference // 154
    odd = collision >> collision_valuation
    output = pow(A, h) * odd
    next_m = defect_phase(output)
    return BouncerStep(
        input_defect_cells=m + 1,
        background_cells=h - 1,
        output_defect_cells=next_m + 1,
        first_valuation=23 * m,
        collision_valuation=collision_valuation,
        input_y=y,
        output_y=output,
    )


def reverse_bouncer_step(output: int) -> BouncerStep:
    """Recover the unique predecessor and both opcodes of an accepted step."""
    defect_phase(output)
    ternary_valuation = vp(output, 3)
    if ternary_valuation < 114 or ternary_valuation % 114:
        raise ValueError("bouncer output has no recharge readback")
    h = ternary_valuation // 114
    odd = output // pow(A, h)
    if odd % 3 == 0:
        raise AssertionError("bouncer odd collision quotient retained a three")
    reverse_collision = 1 + pow(B, h) * odd
    reverse_valuation = vp(reverse_collision, 3)
    if reverse_valuation < 17 or reverse_valuation % 17:
        raise ValueError("bouncer output has no defect readback")
    m = reverse_valuation // 17
    predecessor = (
        pow(D, m) * (reverse_collision // pow(C, m)) - 1
    )
    forward = bouncer_step(predecessor)
    if (
        forward.output_y != output
        or forward.input_defect_cells != m + 1
        or forward.background_cells != h - 1
    ):
        raise AssertionError("bouncer reverse readback failed")
    return forward


def block_macro(defect_cells: int, background_cells: int) -> AffineMacro:
    if defect_cells < 2 or background_cells < 0:
        raise ValueError("invalid bouncer block shape")
    isa = construct_isa()
    result = as_macro(direct_branch(isa, defect_cells))
    background = as_macro(direct_branch(isa, 1))
    for _ in range(background_cells):
        result = compose(result, background)
    return result


def transition_family(
    defect_cells: int, background_cells: int, next_defect_cells: int
) -> BouncerTransition:
    if next_defect_cells < 2:
        raise ValueError("next bouncer defect must have at least two cells")
    isa = construct_isa()
    block = block_macro(defect_cells, background_cells)
    following = as_macro(direct_branch(isa, next_defect_cells))
    source_tail, target_tail = link_macros(block, following)
    input_packet = (
        block.input_packet_base
        + (1 << block.input_packet_stride_exponent) * source_tail
    )
    output_packet = block.output_packet_base + block.output_packet_stride * source_tail
    following_input = (
        following.input_packet_base
        + (1 << following.input_packet_stride_exponent) * target_tail
    )
    if output_packet != following_input:
        raise AssertionError("bouncer block did not meet its next defect")
    return BouncerTransition(
        input_defect_cells=defect_cells,
        background_cells=background_cells,
        output_defect_cells=next_defect_cells,
        input_packet_base=input_packet,
        input_packet_stride_exponent=(
            block.input_packet_stride_exponent
            + following.input_packet_stride_exponent
        ),
        output_packet_base=output_packet,
        output_packet_stride=(
            block.output_packet_stride
            * (1 << following.input_packet_stride_exponent)
        ),
        block_source_tail_base=source_tail,
        next_defect_tail_base=target_tail,
    )


def locate_tail(branch: ChargeBranch, packet: int) -> int:
    difference = packet - branch.input_packet_base
    stride = 1 << branch.input_packet_stride_exponent
    if difference < 0 or difference % stride:
        raise AssertionError("bouncer packet missed a charge branch")
    return difference // stride


def replay_transition(family: BouncerTransition, tail: int) -> dict[str, object]:
    isa = construct_isa()
    packet, expected_output = family.member(tail)
    input_y = packet_to_y(packet)
    state = packet
    charge_macros = 0
    original_unit_macros = 0
    word = [family.input_defect_cells] + [1] * family.background_cells
    for cells in word:
        branch = direct_branch(isa, cells)
        branch_tail = locate_tail(branch, state)
        source, target = branch.member(branch_tail)
        if source != state:
            raise AssertionError("bouncer replay lost its charge source")
        replay_charge_member(branch, branch_tail)
        state = target
        charge_macros += 1
        original_unit_macros += 2
    if state != expected_output:
        raise AssertionError("bouncer replay lost its linked endpoint")
    output_y = packet_to_y(state)
    formula = bouncer_step(input_y)
    if (
        formula.input_defect_cells != family.input_defect_cells
        or formula.background_cells != family.background_cells
        or formula.output_defect_cells != family.output_defect_cells
        or formula.output_y != output_y
    ):
        raise AssertionError("fixed-form bouncer disagrees with macro replay")
    reverse = reverse_bouncer_step(output_y)
    if reverse.input_y != input_y:
        raise AssertionError("bouncer readback did not recover its predecessor")
    input_register = isa.register_offset + isa.register_stride * packet
    output_register = isa.register_offset + isa.register_stride * state
    if output_register <= input_register:
        raise AssertionError("bouncer block is not outward")
    return {
        "input_defect_cells": family.input_defect_cells,
        "background_cells": family.background_cells,
        "output_defect_cells": family.output_defect_cells,
        "tail": tail,
        "input_y_bits": input_y.bit_length(),
        "output_y_bits": output_y.bit_length(),
        "charge_macros_replayed": charge_macros,
        "original_unit_macros_replayed": original_unit_macros,
        "strict_outwardness_checked": True,
        "reverse_readback_checked": True,
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
    defect_bound: int = 4, background_bound: int = 3, tails: int = 2
) -> dict[str, object]:
    if min(defect_bound, tails) < 1 or background_bound < 0:
        raise ValueError("bouncer audit bounds are invalid")
    values = constants()
    families = []
    replays = []
    for m in range(1, defect_bound + 1):
        for background in range(background_bound + 1):
            for next_m in range(1, defect_bound + 1):
                family = transition_family(m + 1, background, next_m + 1)
                families.append(asdict(family))
                for tail in range(tails):
                    replays.append(replay_transition(family, tail))
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact fixed-form charge bouncer identity and bounded complete "
            "transition families, replayed through charge and original unit "
            "macros; no infinite accepted orbit is claimed"
        ),
        "constants": values,
        "fixed_form": "Z=F*G-2^26",
        "background_law": "2^154*Z'=3^114*Z",
        "partial_map": (
            "m=v2(y+1)/23; E=3^(17*m)*(y+1)-2^(23*m); "
            "h=(v2(E)-23*m)/154; y'=3^(114*h)*oddpart(E); "
            "accept positive integral m,h and another defect phase"
        ),
        "reverse_readback": (
            "h=v3(y')/114; q=y'/3^(114*h); "
            "m=v3(1+2^(154*h)*q)/17; "
            "y=2^(23*m)*(1+2^(154*h)*q)/3^(17*m)-1"
        ),
        "exponent_determinant": (
            "114*23-154*17=4; equivalently 2^(23*154)=2^(154*23) "
            "and 3^(114*23)=3^4*3^(17*154)"
        ),
        "conditional_disproof": (
            "an infinite accepted positive bouncer orbit compiles to an "
            "infinite strictly outward ordinary Collatz macro-orbit"
        ),
        "bounds": {
            "input_defect_extra_bound": defect_bound,
            "background_cell_bound": background_bound,
            "output_defect_extra_bound": defect_bound,
            "members_per_family": tails,
            "families": len(families),
            "members": len(replays),
            "charge_macros_replayed": sum(
                int(row["charge_macros_replayed"]) for row in replays
            ),
            "original_unit_macros_replayed": sum(
                int(row["original_unit_macros_replayed"]) for row in replays
            ),
        },
        "families": families,
        "replays": replays,
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported charge bouncer schema")
    bounds = data["bounds"]
    expected = build_certificate(
        int(bounds["input_defect_extra_bound"]),
        int(bounds["background_cell_bound"]),
        int(bounds["members_per_family"]),
    )
    if data != expected:
        raise ValueError("charge bouncer artifact failed reconstruction")


def selftest() -> None:
    constants()
    for m in (1, 2):
        for background in (0, 1, 3):
            for next_m in (1, 2):
                family = transition_family(m + 1, background, next_m + 1)
                replay_transition(family, 0)
                replay_transition(family, 1)


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(500_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--defect-bound", type=int, default=4)
    build.add_argument("--background-bound", type=int, default=3)
    build.add_argument("--tails", type=int, default=2)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("unit charge bouncer selftest: PASS")
    elif args.command == "build":
        data = build_certificate(
            args.defect_bound, args.background_bound, args.tails
        )
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit charge bouncer artifact: PASS")


if __name__ == "__main__":
    main()
