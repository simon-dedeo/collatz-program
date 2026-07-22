#!/usr/bin/env python3
"""Exact checker for a nonlocal gap amplifier in the delay writer.

The dispatcher ``(q,j,q')=(1,1,1)`` has write exponent ``A=5`` and a
complete word alphabet ``0 <= b < 3^5``.  Choose

    b = 3^5 - 2^L,       v = K*2^L - 1.

Its native linked-tail instruction then gives the exact carry identity

    b + 3^5*v = 2^L*(3^5*K - 1).

Thus an input packet ending in ``L`` one-bits emits at least ``L`` zero-bits.
If ``v2(3^5*K-1)=D``, the output tail has exactly ``L+D`` zero-bits.  The
low ``D+1`` bits of the remote odd packet ``K`` select any desired finite
extra gap.  This is a finite regenerative component, not an infinite orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from functools import cache
from pathlib import Path

from breakoff_delay_gate import (
    check_link_member,
    complete_five_trit_writer,
    gate,
    link,
    v2,
)


SCHEMA = "collatz-splash-gap-amplifier-v1"
RADIX_POWER = 5
RADIX = pow(3, RADIX_POWER)


@dataclass(frozen=True)
class AmplifierReplay:
    inherited_gap: int
    extra_gap: int
    word: int
    next_opcode: int
    next_delay: int
    binary_read_width: int
    remote_packet: int
    remote_packet_modulus: int
    input_residual: int
    output_tail: int
    output_odd_part: int
    exact_output_gap: int


def remote_packet(extra_gap: int) -> tuple[int, int]:
    """Least positive odd K with v2(3^5*K-1) exactly extra_gap."""
    if extra_gap < 1:
        raise ValueError("extra gap must be positive")
    modulus = 1 << (extra_gap + 1)
    residue = (
        (1 + (1 << extra_gap)) * pow(RADIX, -1, modulus)
    ) % modulus
    if residue == 0:
        residue = modulus
    if residue % 2 != 1 or v2(RADIX * residue - 1) != extra_gap:
        raise AssertionError("remote-packet constructor missed exact valuation")
    return residue, modulus


@cache
def writer_witnesses() -> dict[int, dict[str, int]]:
    writer = complete_five_trit_writer()
    if writer["write_width_trits"] != RADIX_POWER:
        raise AssertionError("dispatcher write width changed")
    return {record["word"]: record for record in writer["witnesses"]}


@cache
def amplifier_instruction(inherited_gap: int):
    """Return the selected exact link and its public target metadata."""
    word = RADIX - (1 << inherited_gap)
    witness = writer_witnesses()[word]
    first = gate(1, 1, 1)
    second = gate(
        first.next_delay,
        witness["next_opcode"],
        witness["next_delay"],
    )
    instruction = link(first, second)
    return instruction, witness["next_opcode"], witness["next_delay"]


def replay(inherited_gap: int, extra_gap: int) -> AmplifierReplay:
    if inherited_gap < 1 or (1 << inherited_gap) > RADIX:
        raise ValueError("the selected word must be nonnegative")
    word = RADIX - (1 << inherited_gap)
    instruction, next_opcode, next_delay = amplifier_instruction(inherited_gap)
    if instruction.second_tail_base != word:
        raise AssertionError("writer witness emits the wrong word")
    if instruction.second_tail_stride != RADIX:
        raise AssertionError("dispatcher lost its 3^5 tail stride")

    packet, packet_modulus = remote_packet(extra_gap)
    residual = packet * (1 << inherited_gap) - 1
    first_tail, output_tail = instruction.member(residual)
    check_link_member(instruction, residual)
    if first_tail < 0:
        raise AssertionError("linked source tail is not ordinary")
    expected = (1 << inherited_gap) * (RADIX * packet - 1)
    if output_tail != expected:
        raise AssertionError("sacrificial carry identity failed")
    exact_gap = v2(output_tail)
    if exact_gap != inherited_gap + extra_gap:
        raise AssertionError("amplified gap is not exact")
    odd_part = output_tail >> exact_gap
    if odd_part % 2 != 1:
        raise AssertionError("amplified output odd part is not odd")
    return AmplifierReplay(
        inherited_gap=inherited_gap,
        extra_gap=extra_gap,
        word=word,
        next_opcode=next_opcode,
        next_delay=next_delay,
        binary_read_width=instruction.first_tail_stride.bit_length() - 1,
        remote_packet=packet,
        remote_packet_modulus=packet_modulus,
        input_residual=residual,
        output_tail=output_tail,
        output_odd_part=odd_part,
        exact_output_gap=exact_gap,
    )


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def build_certificate(max_extra_gap: int) -> dict[str, object]:
    if max_extra_gap < 1:
        raise ValueError("max extra gap must be positive")
    max_inherited_gap = RADIX.bit_length() - 1
    records = [
        replay(inherited, extra)
        for inherited in range(1, max_inherited_gap + 1)
        for extra in range(1, max_extra_gap + 1)
    ]
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "universal integer carry identity for the seven displayed "
            "3^5-2^L writer words; exact linked-gate replay for every "
            "listed (L,D); no returning controller or infinite orbit claim"
        ),
        "dispatcher": {
            "delay": 1,
            "collision_opcode": 1,
            "next_delay": 1,
            "write_exponent": RADIX_POWER,
            "write_radix": RADIX,
        },
        "universal_identity": (
            "(3^5-2^L)+3^5*(K*2^L-1)=2^L*(3^5*K-1)"
        ),
        "remote_packet_class": (
            "3^5*K=1+2^D (mod 2^(D+1)), hence "
            "v2(3^5*K-1)=D"
        ),
        "bounds": {
            "inherited_gap": [1, max_inherited_gap],
            "extra_gap": [1, max_extra_gap],
        },
        "linked_members_replayed": len(records),
        "literal_gate_macros_replayed": 2 * len(records),
        "records": [asdict(record) for record in records],
    }


def selftest() -> None:
    record = replay(3, 5)
    if record.word != 235 or record.exact_output_gap != 8:
        raise AssertionError("gap-amplifier regression changed")


def render(certificate: dict[str, object]) -> str:
    return json.dumps(certificate, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-extra-gap", type=int, default=32)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("splash gap-amplifier selftest: PASS")
    elif args.command == "build":
        certificate = build_certificate(args.max_extra_gap)
        args.output.write_text(render(certificate))
        print(f"wrote {args.output}")
    else:
        expected = json.loads(args.artifact.read_text())
        if expected.get("schema") != SCHEMA:
            raise ValueError("unexpected artifact schema")
        actual = build_certificate(int(expected["bounds"]["extra_gap"][1]))
        if actual != expected:
            raise AssertionError("artifact differs from exact recomputation")
        print("splash gap-amplifier artifact: PASS")


if __name__ == "__main__":
    main()
