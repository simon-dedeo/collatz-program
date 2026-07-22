#!/usr/bin/env python3
"""Autonomous one-register normal form of the returning ether glider.

Write

    Y = 83790531*K - 874281.

For a positive invariant register ``Y = -874281 (mod 83790531)``, let
``e=v2(Y)`` and ``h=Y/2^e``.  A returning ether macro is executable exactly
on the branches

    e = 8*n-5,
    3^(6*n+11)*h + 51 = 0 (mod 2^20),       n>=1,

and its output register is

    Y' = (3^(6*n+11)*h + 51) / 2^20.

The large constants in the two defect links cancel to 51.  For each n, CRT
gives one complete odd h-class modulo ``83790531*2^20``.  In the original K
coordinate this branch is *identically* the compiled glider macro

    K=R_n+2^(8*n+15)*q -> K'=S_n+3^(6*n+11)*q.

An infinite successful orbit of this partial map would therefore be an
infinite returning Collatz glider.  This module proves/checks the coordinate
equivalence; it does not supply such an orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path

from breakoff_delay_gate import v2
from breakoff_ether_glider import glider_macro, replay_macro_member


SCHEMA = "collatz-breakoff-ether-counter-v1"
REGISTER_OFFSET = -874281
REGISTER_STRIDE = 83790531
DIVISION_EXPONENT = 20
OUTPUT_CONSTANT = 51
ODD_MODULUS = REGISTER_STRIDE * (1 << DIVISION_EXPONENT)


@dataclass(frozen=True)
class EtherCounterBranch:
    ether_cells: int
    input_valuation: int
    ternary_exponent: int
    odd_base: int
    odd_stride: int
    input_register_base: int
    input_register_stride: int
    output_register_base: int
    output_register_stride: int
    input_packet_base: int
    input_packet_stride: int
    output_packet_base: int
    output_packet_stride: int

    def member(self, tail: int) -> tuple[int, int, int, int]:
        if tail < 0:
            raise ValueError("branch tail must be nonnegative")
        h = self.odd_base + self.odd_stride * tail
        y = self.input_register_base + self.input_register_stride * tail
        y_next = self.output_register_base + self.output_register_stride * tail
        return h, y, y_next, (y - REGISTER_OFFSET) // REGISTER_STRIDE


def packet_to_register(packet: int) -> int:
    if packet < 1:
        raise ValueError("packet must be positive")
    return REGISTER_OFFSET + REGISTER_STRIDE * packet


def register_to_packet(register: int) -> int:
    difference = register - REGISTER_OFFSET
    if register <= 0 or difference % REGISTER_STRIDE:
        raise ValueError("register is outside the ordinary packet invariant")
    packet = difference // REGISTER_STRIDE
    if packet < 1:
        raise ValueError("register corresponds to a nonpositive packet")
    return packet


def counter_next(register: int) -> int | None:
    """Execute the public autonomous partial map, with no hidden metadata."""
    try:
        register_to_packet(register)
    except ValueError:
        return None
    exponent = v2(register)
    if exponent < 3 or (exponent - 3) % 8:
        return None
    ether_cells = (exponent + 5) // 8
    ternary_exponent = 6 * ether_cells + 11
    odd = register >> exponent
    numerator = pow(3, ternary_exponent) * odd + OUTPUT_CONSTANT
    if numerator % (1 << DIVISION_EXPONENT):
        return None
    result = numerator >> DIVISION_EXPONENT
    try:
        register_to_packet(result)
    except ValueError as error:
        raise AssertionError("successful counter step lost its invariant") from error
    if result <= register:
        raise AssertionError("successful ether counter step is not outward")
    return result


def branch(ether_cells: int) -> EtherCounterBranch:
    if ether_cells < 1:
        raise ValueError("ether length must be positive")
    exponent = 8 * ether_cells - 5
    ternary_exponent = 6 * ether_cells + 11

    # The invariant Y=r (mod A) fixes h modulo A; executable boundary return
    # fixes h modulo 2^20.  CRT is elementary because A is odd.
    invariant_residue = (
        REGISTER_OFFSET * pow(1 << exponent, -1, REGISTER_STRIDE)
    ) % REGISTER_STRIDE
    execution_residue = (
        -OUTPUT_CONSTANT
        * pow(pow(3, ternary_exponent), -1, 1 << DIVISION_EXPONENT)
    ) % (1 << DIVISION_EXPONENT)
    odd_base = invariant_residue + REGISTER_STRIDE * (
        (execution_residue - invariant_residue)
        * pow(REGISTER_STRIDE, -1, 1 << DIVISION_EXPONENT)
        % (1 << DIVISION_EXPONENT)
    )
    if odd_base == 0:
        odd_base = ODD_MODULUS
    if odd_base % 2 != 1:
        raise AssertionError("CRT branch base is not odd")

    input_base = (1 << exponent) * odd_base
    input_stride = (1 << exponent) * ODD_MODULUS
    output_numerator = pow(3, ternary_exponent) * odd_base + OUTPUT_CONSTANT
    if output_numerator % (1 << DIVISION_EXPONENT):
        raise AssertionError("CRT branch missed the fixed division")
    output_base = output_numerator >> DIVISION_EXPONENT
    output_stride = pow(3, ternary_exponent) * REGISTER_STRIDE
    if (input_base - REGISTER_OFFSET) % REGISTER_STRIDE:
        raise AssertionError("input branch lost the packet invariant")
    if (output_base - REGISTER_OFFSET) % REGISTER_STRIDE:
        raise AssertionError("output branch lost the packet invariant")

    input_packet_base = register_to_packet(input_base)
    output_packet_base = register_to_packet(output_base)
    input_packet_stride = input_stride // REGISTER_STRIDE
    output_packet_stride = output_stride // REGISTER_STRIDE
    compiled = glider_macro(ether_cells)
    if (
        input_packet_base != compiled.input_packet_base
        or input_packet_stride != 1 << compiled.input_packet_stride_exponent
        or output_packet_base != compiled.output_packet_base
        or output_packet_stride != compiled.output_packet_stride
    ):
        raise AssertionError("autonomous branch and returning macro disagree")
    if output_base <= input_base or output_stride < input_stride:
        raise AssertionError("branch coefficient comparison is not outward")
    return EtherCounterBranch(
        ether_cells=ether_cells,
        input_valuation=exponent,
        ternary_exponent=ternary_exponent,
        odd_base=odd_base,
        odd_stride=ODD_MODULUS,
        input_register_base=input_base,
        input_register_stride=input_stride,
        output_register_base=output_base,
        output_register_stride=output_stride,
        input_packet_base=input_packet_base,
        input_packet_stride=input_packet_stride,
        output_packet_base=output_packet_base,
        output_packet_stride=output_packet_stride,
    )


def check_branch_member(candidate: EtherCounterBranch, tail: int) -> None:
    h, register, register_next, packet = candidate.member(tail)
    if v2(register) != candidate.input_valuation:
        raise AssertionError("branch member emitted the wrong valuation")
    if register != (1 << candidate.input_valuation) * h:
        raise AssertionError("branch odd-part factorization failed")
    if packet_to_register(packet) != register:
        raise AssertionError("packet/register input conversion failed")
    if counter_next(register) != register_next:
        raise AssertionError("public counter map and affine branch disagree")
    output_packet = register_to_packet(register_next)
    compiled = glider_macro(candidate.ether_cells)
    macro_input, macro_output = compiled.member(tail)
    if packet != macro_input or output_packet != macro_output:
        raise AssertionError("counter member and glider member disagree")


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def build_certificate(
    max_ether_cells: int, tails_per_branch: int, executable_replay_cells: int
) -> dict[str, object]:
    if min(max_ether_cells, tails_per_branch, executable_replay_cells) < 1:
        raise ValueError("all bounds must be positive")
    if executable_replay_cells > max_ether_cells:
        raise ValueError("executable replay bound exceeds branch bound")
    branches = [branch(n) for n in range(1, max_ether_cells + 1)]
    checks = 0
    for candidate in branches:
        for tail in range(tails_per_branch):
            check_branch_member(candidate, tail)
            checks += 1
    executable = [
        replay_macro_member(glider_macro(n), tail)
        for n in range(1, executable_replay_cells + 1)
        for tail in range(min(2, tails_per_branch))
    ]
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact CRT construction and coefficient equivalence between "
            "the autonomous register branch and every returning macro in "
            "the stated n box; bounded literal executable samples; no "
            "infinite counter orbit claim"
        ),
        "register": "Y=83790531*K-874281",
        "public_partial_map": (
            "e=v2(Y)=8n-5, h=Y/2^e, "
            "Y'=(3^(6n+11)*h+51)/2^20 when integral and invariant"
        ),
        "bounds": {
            "ether_cells": [1, max_ether_cells],
            "tails_per_branch": tails_per_branch,
            "literal_executable_replay_cells": [1, executable_replay_cells],
        },
        "branch_count": len(branches),
        "exact_branch_members_checked": checks,
        "literal_executable_macro_members": len(executable),
        "literal_linked_members": sum(
            replay.linked_members_replayed for replay in executable
        ),
        "literal_gate_macros": sum(
            replay.literal_gate_macros_replayed for replay in executable
        ),
        "branches": [asdict(candidate) for candidate in branches],
    }


def selftest() -> None:
    first = branch(1)
    if first.input_packet_base != 3520715 or first.output_packet_base != 54200376:
        raise AssertionError("one-cell autonomous branch changed")
    for tail in range(3):
        check_branch_member(first, tail)
    if counter_next(1) is not None:
        raise AssertionError("malformed register was accepted")


def render(certificate: dict[str, object]) -> str:
    return json.dumps(certificate, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-ether-cells", type=int, default=128)
    build.add_argument("--tails-per-branch", type=int, default=4)
    build.add_argument("--executable-replay-cells", type=int, default=32)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("breakoff ether-counter selftest: PASS")
    elif args.command == "build":
        certificate = build_certificate(
            args.max_ether_cells,
            args.tails_per_branch,
            args.executable_replay_cells,
        )
        args.output.write_text(render(certificate))
        print(f"wrote {args.output}")
    else:
        expected = json.loads(args.artifact.read_text())
        if expected.get("schema") != SCHEMA:
            raise ValueError("unexpected artifact schema")
        bounds = expected["bounds"]
        actual = build_certificate(
            int(bounds["ether_cells"][1]),
            int(bounds["tails_per_branch"]),
            int(bounds["literal_executable_replay_cells"][1]),
        )
        if actual != expected:
            raise AssertionError("artifact differs from exact recomputation")
        print("breakoff ether-counter artifact: PASS")


if __name__ == "__main__":
    main()
