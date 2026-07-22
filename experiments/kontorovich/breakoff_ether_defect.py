#!/usr/bin/env python3
"""Exact checker for a regenerative finite ether in the delay-gate machine.

The delay gate E=(1,2,1) self-links by

    t = 20 + 2^8*v  ->  t' = 57 + 3^6*v.

Its affine fixed point is tau=-12/473, since

    473*t' + 12 = (3^6/2^8) * (473*t + 12).

Thus ``v2(473*t+12)=8*n`` is an exact n-cell delay line.  The defect gate
H=(1,136,1) gives an E->H->E return.  A Mersenne-coded residual reduces its
returned E tail to

    473*t + 12 = 2^8 * (r + A*K),

for fixed odd integers r and A.  One odd class of K modulo 2^(D+1) therefore
creates exactly 8+D ether bits for every D>=1.  Choosing D=8*n-8 emits an
exact n-cell finite ether.

This is an arbitrarily long *finite* delay-line constructor.  It does not
show that the boundary after those n cells regenerates another defect input,
and it is not an infinite Collatz orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from functools import cache
from pathlib import Path

from breakoff_delay_gate import check_link_member, gate, link, v2


SCHEMA = "collatz-breakoff-ether-defect-v1"
ETHER_DENOMINATOR = 473
ETHER_NUMERATOR = 12


@dataclass(frozen=True)
class EtherComponents:
    first_address_base: int
    first_address_exponent: int
    first_word: int
    return_address_base: int
    return_word: int
    bridge_residual_base: int
    bridge_tail_base: int
    return_constant: int
    return_stride: int
    shifted_constant: int
    ether_odd_offset: int
    ether_odd_stride: int
    inherited_ether_bits: int


@dataclass(frozen=True)
class EtherReplay:
    ether_cells: int
    extra_ether_bits: int
    remote_packet: int
    remote_packet_modulus: int
    defect_input_residual: int
    defect_input_tail: int
    defect_tail: int
    return_tail: int
    return_ether_odd_part: int
    boundary_tail: int
    ordinary_start: int
    linked_members_replayed: int
    literal_gate_macros_replayed: int


@cache
def machines():
    ether = gate(1, 2, 1)
    defect = gate(1, 136, 1)
    return (
        ether,
        defect,
        link(ether, defect),
        link(defect, ether),
        link(ether, ether),
    )


@cache
def components() -> EtherComponents:
    ether, defect, into_defect, from_defect, _ = machines()
    if into_defect.first_tail_stride & (into_defect.first_tail_stride - 1):
        raise AssertionError("defect address stride is not dyadic")
    first_exponent = into_defect.first_tail_stride.bit_length() - 1
    if from_defect.first_tail_stride != 256:
        raise AssertionError("return address does not read one ether cell")
    if into_defect.second_tail_stride != 729:
        raise AssertionError("ether writer lost its 3^6 stride")

    # Solve b+3^6*v = a+2^8*w with v=v0+2^8*u and
    # w=w0+3^6*u.  The least lift keeps both residuals natural.
    v0 = (
        (from_defect.first_tail_base - into_defect.second_tail_base)
        * pow(729, -1, 256)
    ) % 256
    w0 = (
        into_defect.second_tail_base
        + 729 * v0
        - from_defect.first_tail_base
    ) // 256
    if w0 < 0:
        lifts = (-w0 + 728) // 729
        v0 += 256 * lifts
        w0 += 729 * lifts
    if (
        into_defect.second_tail_base + 729 * v0
        != from_defect.first_tail_base + 256 * w0
    ):
        raise AssertionError("defect-return congruence failed")

    defect_write_exponent = defect.collision_opcode + 2 * defect.delay + 2
    return_constant = (
        from_defect.second_tail_base
        + pow(3, defect_write_exponent) * w0
    )
    return_stride = pow(3, defect_write_exponent + 6)
    shifted_constant = return_constant - return_stride
    numerator = (
        ETHER_DENOMINATOR * shifted_constant + ETHER_NUMERATOR
    )
    inherited_bits = v2(abs(numerator))
    if inherited_bits != 8:
        raise AssertionError("selected defect no longer emits one ether cell")
    odd_offset = numerator >> inherited_bits
    odd_stride = ETHER_DENOMINATOR * return_stride
    if odd_offset % 2 != 1 or odd_stride % 2 != 1:
        raise AssertionError("ether amplifier lost odd invertibility")

    return EtherComponents(
        first_address_base=into_defect.first_tail_base,
        first_address_exponent=first_exponent,
        first_word=into_defect.second_tail_base,
        return_address_base=from_defect.first_tail_base,
        return_word=from_defect.second_tail_base,
        bridge_residual_base=v0,
        bridge_tail_base=w0,
        return_constant=return_constant,
        return_stride=return_stride,
        shifted_constant=shifted_constant,
        ether_odd_offset=odd_offset,
        ether_odd_stride=odd_stride,
        inherited_ether_bits=inherited_bits,
    )


def remote_packet(extra_bits: int) -> tuple[int, int]:
    """Least positive K making v2(r+A*K) exactly extra_bits."""
    if extra_bits < 1:
        raise ValueError("extra ether precision must be positive")
    data = components()
    modulus = 1 << (extra_bits + 1)
    packet = (
        ((1 << extra_bits) - data.ether_odd_offset)
        * pow(data.ether_odd_stride, -1, modulus)
    ) % modulus
    if packet == 0:
        packet = modulus
    if packet % 2 != 1:
        raise AssertionError("remote packet is not odd")
    if v2(
        data.ether_odd_offset + data.ether_odd_stride * packet
    ) != extra_bits:
        raise AssertionError("remote packet missed exact ether precision")
    return packet, modulus


def replay(ether_cells: int) -> EtherReplay:
    if ether_cells < 2:
        raise ValueError("this constructor uses a positive extra-bit class")
    extra_bits = 8 * ether_cells - components().inherited_ether_bits
    packet, packet_modulus = remote_packet(extra_bits)
    data = components()
    ether, _, into_defect, from_defect, self_link = machines()

    # u=2^8*K-1 is the sacrificial Mersenne packet.  The first bridge
    # residual then has the exact class v=v0+2^8*u.
    u = 256 * packet - 1
    v = data.bridge_residual_base + 256 * u
    first_tail, defect_tail = into_defect.member(v)
    check_link_member(into_defect, v)
    if first_tail != (
        data.first_address_base + (1 << data.first_address_exponent) * v
    ):
        raise AssertionError("defect input tail changed")

    w = data.bridge_tail_base + 729 * u
    if defect_tail != data.return_address_base + 256 * w:
        raise AssertionError("two defect links do not meet")
    checked_defect_tail, returned_tail = from_defect.member(w)
    check_link_member(from_defect, w)
    if checked_defect_tail != defect_tail:
        raise AssertionError("return link starts at a different tail")
    expected_return = data.shifted_constant + 256 * data.return_stride * packet
    if returned_tail != expected_return:
        raise AssertionError("defect return formula failed")

    ether_numerator = (
        ETHER_DENOMINATOR * returned_tail + ETHER_NUMERATOR
    )
    if v2(ether_numerator) != 8 * ether_cells:
        raise AssertionError("returned ether has the wrong exact depth")
    odd_part = ether_numerator >> (8 * ether_cells)
    if odd_part % 2 != 1:
        raise AssertionError("returned ether quotient is not odd")

    # Each self-link consumes one eight-bit ether cell and multiplies the
    # remaining defect packet by 3^6.  Replay all n linked members exactly.
    current = returned_tail
    for remaining in range(ether_cells, 0, -1):
        if v2(
            ETHER_DENOMINATOR * current + ETHER_NUMERATOR
        ) != 8 * remaining:
            raise AssertionError("ether depth did not decrement by one cell")
        difference = current - self_link.first_tail_base
        if difference < 0 or difference % self_link.first_tail_stride:
            raise AssertionError("ether tail missed its self-link address")
        residual = difference // self_link.first_tail_stride
        checked, following = self_link.member(residual)
        check_link_member(self_link, residual)
        if checked != current:
            raise AssertionError("ether self-link starts at a different tail")
        current = following
    if v2(ETHER_DENOMINATOR * current + ETHER_NUMERATOR) != 0:
        raise AssertionError("finite ether did not expose its boundary")

    ordinary_start = ether.member(first_tail)[3]
    linked_members = ether_cells + 2
    return EtherReplay(
        ether_cells=ether_cells,
        extra_ether_bits=extra_bits,
        remote_packet=packet,
        remote_packet_modulus=packet_modulus,
        defect_input_residual=v,
        defect_input_tail=first_tail,
        defect_tail=defect_tail,
        return_tail=returned_tail,
        return_ether_odd_part=odd_part,
        boundary_tail=current,
        ordinary_start=ordinary_start,
        linked_members_replayed=linked_members,
        literal_gate_macros_replayed=2 * linked_members,
    )


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def build_certificate(max_ether_cells: int) -> dict[str, object]:
    if max_ether_cells < 2:
        raise ValueError("max ether cells must be at least two")
    records = [replay(n) for n in range(2, max_ether_cells + 1)]
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "universal exact affine identities for the displayed E/H "
            "defect and remote-packet class; literal linked-gate replay "
            "for every listed finite ether; no boundary return or infinite "
            "orbit claim"
        ),
        "ether_gate": {"delay": 1, "collision_opcode": 2, "next_delay": 1},
        "defect_gate": {"delay": 1, "collision_opcode": 136, "next_delay": 1},
        "ether_fixed_point": "-12/473",
        "ether_self_link": "t=20+2^8*v -> t'=57+3^6*v",
        "ether_invariant": (
            "473*t'+12=(3^6/2^8)*(473*t+12) on the self-link cylinder"
        ),
        "defect_return": asdict(components()),
        "remote_packet_class": (
            "r+A*K=2^D (mod 2^(D+1)); returned ether depth is 8+D"
        ),
        "bounds": {"ether_cells": [2, max_ether_cells]},
        "record_count": len(records),
        "linked_members_replayed": sum(
            record.linked_members_replayed for record in records
        ),
        "literal_gate_macros_replayed": sum(
            record.literal_gate_macros_replayed for record in records
        ),
        "records": [asdict(record) for record in records],
    }


def selftest() -> None:
    record = replay(2)
    if record.extra_ether_bits != 8:
        raise AssertionError("two-cell ether precision changed")
    if components().bridge_residual_base != 177:
        raise AssertionError("defect bridge regression changed")


def render(certificate: dict[str, object]) -> str:
    return json.dumps(certificate, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-ether-cells", type=int, default=32)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("breakoff ether-defect selftest: PASS")
    elif args.command == "build":
        certificate = build_certificate(args.max_ether_cells)
        args.output.write_text(render(certificate))
        print(f"wrote {args.output}")
    else:
        expected = json.loads(args.artifact.read_text())
        if expected.get("schema") != SCHEMA:
            raise ValueError("unexpected artifact schema")
        actual = build_certificate(int(expected["bounds"]["ether_cells"][1]))
        if actual != expected:
            raise AssertionError("artifact differs from exact recomputation")
        print("breakoff ether-defect artifact: PASS")


if __name__ == "__main__":
    main()
