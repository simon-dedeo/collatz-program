#!/usr/bin/env python3
"""Exact returning finite-ether macros in the break-off delay machine.

Let E=(1,2,1) be the ether gate and H=(1,1,1) the unique immediate
E->H->E defect whose E-input address is odd.  Their exact tail links are

    E -> H:  67 + 2^7*v  -> 381 + 3^6*v,
    H -> E: 151 + 2^8*w  -> 144 + 3^5*w.

They meet for ``v=170+2^8*u`` and ``w=485+3^6*u``.  On the Mersenne packet
``u=2^5*K-1``, the returned E tail ``t`` satisfies

    473*t+12 = 2^5*(-874281 + 83790531*K).

One odd class of K therefore writes exactly n ether cells.  Requiring the
exposed odd boundary to enter the same defect input consumes one more binary
address block and yields the complete returning macro

    K = R_n + 2^(8*n+15)*q  ->  K' = S_n + 3^(6*n+11)*q.

The macro starts at an E-state ready for H, executes E->H->E, crosses n
ether self-links, and ends at another E-state ready for H.  This is a finite
glider instruction for every n>=1, not one ordinary infinite orbit.  A fixed
n schedule is periodically obstructed; a disproof still requires one payload
which generates a genuinely aperiodic infinite sequence of n values.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from functools import cache
from pathlib import Path

from breakoff_delay_gate import check_link_member, gate, link, v2


SCHEMA = "collatz-breakoff-ether-glider-v1"
ETHER_DENOMINATOR = 473
ETHER_NUMERATOR = 12


@dataclass(frozen=True)
class GliderComponents:
    first_address_base: int
    first_address_exponent: int
    first_word: int
    return_address_base: int
    return_word: int
    bridge_residual_base: int
    bridge_tail_base: int
    inherited_ether_bits: int
    defect_input_constant: int
    defect_input_stride_exponent: int
    return_constant: int
    return_stride: int
    ether_odd_offset: int
    ether_odd_stride: int


@dataclass(frozen=True)
class GliderMacro:
    ether_cells: int
    input_packet_base: int
    input_packet_stride_exponent: int
    output_packet_base: int
    output_packet_stride: int
    remote_packet_base: int
    remote_packet_modulus: int
    boundary_parameter_base: int

    def member(self, tail: int) -> tuple[int, int]:
        if tail < 0:
            raise ValueError("macro tail must be nonnegative")
        return (
            self.input_packet_base
            + (1 << self.input_packet_stride_exponent) * tail,
            self.output_packet_base + self.output_packet_stride * tail,
        )


@dataclass(frozen=True)
class GliderReplay:
    ether_cells: int
    macro_tail: int
    input_packet: int
    output_packet: int
    ordinary_start: int
    ordinary_endpoint: int
    defect_input_tail: int
    returned_ether_tail: int
    exposed_boundary_tail: int
    linked_members_replayed: int
    literal_gate_macros_replayed: int


@dataclass(frozen=True)
class StaircaseFailure:
    source_ether_cells: int
    first_link_macro_tail: int
    generated_next_macro_tail: int
    mismatch_valuation: int
    required_next_address_bits: int


@cache
def machines():
    ether = gate(1, 2, 1)
    defect = gate(1, 1, 1)
    return (
        ether,
        defect,
        link(ether, defect),
        link(defect, ether),
        link(ether, ether),
    )


@cache
def components() -> GliderComponents:
    ether, defect, into_defect, from_defect, _ = machines()
    if into_defect.first_tail_stride != 128:
        raise AssertionError("odd defect input address changed")
    if into_defect.second_tail_stride != 729:
        raise AssertionError("ether write stride changed")
    if from_defect.first_tail_stride != 256:
        raise AssertionError("defect return address changed")

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
        raise AssertionError("odd defect bridges do not meet")

    defect_write_exponent = defect.collision_opcode + 2 * defect.delay + 2
    return_constant = (
        from_defect.second_tail_base
        + pow(3, defect_write_exponent) * w0
    )
    return_stride = pow(3, defect_write_exponent + 6)
    numerator = (
        ETHER_DENOMINATOR * (return_constant - return_stride)
        + ETHER_NUMERATOR
    )
    inherited_bits = v2(abs(numerator))
    odd_offset = numerator >> inherited_bits
    odd_stride = ETHER_DENOMINATOR * return_stride
    if inherited_bits != 5 or odd_offset != -874281:
        raise AssertionError("odd defect ether factorization changed")
    if odd_stride != 83790531:
        raise AssertionError("odd defect ether stride changed")

    input_exponent = 7 + 8 + inherited_bits
    input_constant = (
        into_defect.first_tail_base
        + 128 * (v0 - 256)
    )
    if input_exponent != 20 or input_constant != -10941:
        raise AssertionError("odd defect input normal form changed")
    return GliderComponents(
        first_address_base=into_defect.first_tail_base,
        first_address_exponent=7,
        first_word=into_defect.second_tail_base,
        return_address_base=from_defect.first_tail_base,
        return_word=from_defect.second_tail_base,
        bridge_residual_base=v0,
        bridge_tail_base=w0,
        inherited_ether_bits=inherited_bits,
        defect_input_constant=input_constant,
        defect_input_stride_exponent=input_exponent,
        return_constant=return_constant,
        return_stride=return_stride,
        ether_odd_offset=odd_offset,
        ether_odd_stride=odd_stride,
    )


def exact_remote_packet(extra_bits: int) -> tuple[int, int]:
    if extra_bits < 1:
        raise ValueError("extra ether bits must be positive")
    data = components()
    modulus = 1 << (extra_bits + 1)
    packet = (
        ((1 << extra_bits) - data.ether_odd_offset)
        * pow(data.ether_odd_stride, -1, modulus)
    ) % modulus
    if packet == 0:
        packet = modulus
    value = data.ether_odd_offset + data.ether_odd_stride * packet
    if packet % 2 != 1 or value <= 0 or v2(value) != extra_bits:
        raise AssertionError("remote packet missed exact ether depth")
    return packet, modulus


@cache
def glider_macro(ether_cells: int) -> GliderMacro:
    if ether_cells < 1:
        raise ValueError("ether length must be positive")
    data = components()
    extra_bits = 8 * ether_cells - data.inherited_ether_bits
    packet, packet_modulus = exact_remote_packet(extra_bits)
    ether_odd_part = (
        data.ether_odd_offset + data.ether_odd_stride * packet
    ) >> extra_bits
    if ether_odd_part % 2 != 1:
        raise AssertionError("ether quotient is not odd")

    boundary_base = (
        pow(729, ether_cells) * ether_odd_part - ETHER_NUMERATOR
    ) // ETHER_DENOMINATOR
    if (
        ETHER_DENOMINATOR * boundary_base + ETHER_NUMERATOR
        != pow(729, ether_cells) * ether_odd_part
    ):
        raise AssertionError("ether boundary is not integral")

    # K=packet+2^(extra_bits+1)*p changes the boundary by
    # 2*3^(6n+11)*p.  Intersect this affine family with
    # X(K')=-10941+2^20*K', the next odd defect input.
    output_stride = pow(3, 6 * ether_cells + 11)
    boundary_parameter_modulus = (
        1 << (data.defect_input_stride_exponent - 1)
    )
    parameter = (
        ((data.defect_input_constant - boundary_base) // 2)
        * pow(output_stride, -1, boundary_parameter_modulus)
    ) % boundary_parameter_modulus
    difference = (
        boundary_base
        + 2 * output_stride * parameter
        - data.defect_input_constant
    )
    if difference % (1 << data.defect_input_stride_exponent):
        raise AssertionError("exposed boundary missed the next defect cylinder")
    output_base = difference >> data.defect_input_stride_exponent
    if output_base < 0:
        lifts = (-output_base + output_stride - 1) // output_stride
        parameter += boundary_parameter_modulus * lifts
        output_base += output_stride * lifts

    input_base = packet + packet_modulus * parameter
    input_exponent = (
        extra_bits
        + 1
        + data.defect_input_stride_exponent
        - 1
    )
    if input_exponent != 8 * ether_cells + 15:
        raise AssertionError("glider input address width changed")
    result = GliderMacro(
        ether_cells=ether_cells,
        input_packet_base=input_base,
        input_packet_stride_exponent=input_exponent,
        output_packet_base=output_base,
        output_packet_stride=output_stride,
        remote_packet_base=packet,
        remote_packet_modulus=packet_modulus,
        boundary_parameter_base=parameter,
    )
    replay_macro_member(result, 0)
    return result


def replay_macro_member(candidate: GliderMacro, tail: int) -> GliderReplay:
    data = components()
    ether, _, into_defect, from_defect, self_link = machines()
    input_packet, output_packet = candidate.member(tail)
    u = (1 << data.inherited_ether_bits) * input_packet - 1
    v = data.bridge_residual_base + 256 * u
    first_tail, defect_tail = into_defect.member(v)
    check_link_member(into_defect, v)
    expected_first = (
        data.defect_input_constant
        + (1 << data.defect_input_stride_exponent) * input_packet
    )
    if first_tail != expected_first:
        raise AssertionError("glider macro starts outside its defect family")

    w = data.bridge_tail_base + 729 * u
    if defect_tail != data.return_address_base + 256 * w:
        raise AssertionError("defect bridge tails disagree")
    checked_defect, returned = from_defect.member(w)
    check_link_member(from_defect, w)
    if checked_defect != defect_tail:
        raise AssertionError("return link starts at another defect tail")

    numerator = ETHER_DENOMINATOR * returned + ETHER_NUMERATOR
    if v2(numerator) != 8 * candidate.ether_cells:
        raise AssertionError("glider macro emitted the wrong ether depth")
    current = returned
    for remaining in range(candidate.ether_cells, 0, -1):
        if v2(
            ETHER_DENOMINATOR * current + ETHER_NUMERATOR
        ) != 8 * remaining:
            raise AssertionError("glider ether depth did not decrement")
        difference = current - self_link.first_tail_base
        if difference < 0 or difference % self_link.first_tail_stride:
            raise AssertionError("glider ether missed its self-link")
        residual = difference // self_link.first_tail_stride
        checked, following = self_link.member(residual)
        check_link_member(self_link, residual)
        if checked != current:
            raise AssertionError("glider ether link starts elsewhere")
        current = following
    if current != (
        data.defect_input_constant
        + (1 << data.defect_input_stride_exponent) * output_packet
    ):
        raise AssertionError("exposed boundary did not return to the defect")

    ordinary_start = ether.member(first_tail)[3]
    ordinary_endpoint = ether.member(current)[3]
    if ordinary_endpoint <= ordinary_start:
        raise AssertionError("returning glider macro is not strictly outward")
    linked_members = candidate.ether_cells + 2
    return GliderReplay(
        ether_cells=candidate.ether_cells,
        macro_tail=tail,
        input_packet=input_packet,
        output_packet=output_packet,
        ordinary_start=ordinary_start,
        ordinary_endpoint=ordinary_endpoint,
        defect_input_tail=first_tail,
        returned_ether_tail=returned,
        exposed_boundary_tail=current,
        linked_members_replayed=linked_members,
        literal_gate_macros_replayed=2 * linked_members,
    )


def link_macros(
    first: GliderMacro, second: GliderMacro
) -> tuple[int, int]:
    """Least nonnegative q,s with first.output(q)=second.input(s)."""
    modulus = 1 << second.input_packet_stride_exponent
    q = (
        (second.input_packet_base - first.output_packet_base)
        * pow(first.output_packet_stride, -1, modulus)
    ) % modulus
    difference = (
        first.output_packet_base
        + first.output_packet_stride * q
        - second.input_packet_base
    )
    if difference % modulus:
        raise AssertionError("macro linker missed its dyadic cylinder")
    s = difference // modulus
    if s < 0:
        lifts = (-s + first.output_packet_stride - 1) // first.output_packet_stride
        q += modulus * lifts
        s += first.output_packet_stride * lifts
    if first.member(q)[1] != second.member(s)[0]:
        raise AssertionError("linked macro packets disagree")
    return q, s


def staircase_failure(n: int) -> StaircaseFailure:
    first = glider_macro(n)
    second = glider_macro(n + 1)
    third = glider_macro(n + 2)
    q, generated = link_macros(first, second)
    output = second.member(generated)[1]
    difference = output - third.input_packet_base
    mismatch = v2(abs(difference)) if difference else third.input_packet_stride_exponent
    if difference >= 0 and difference % (
        1 << third.input_packet_stride_exponent
    ) == 0:
        raise AssertionError("staircase unexpectedly continued at depth two")
    return StaircaseFailure(
        source_ether_cells=n,
        first_link_macro_tail=q,
        generated_next_macro_tail=generated,
        mismatch_valuation=mismatch,
        required_next_address_bits=third.input_packet_stride_exponent,
    )


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def build_certificate(
    max_ether_cells: int, replay_tails: int, staircase_bound: int
) -> dict[str, object]:
    if min(max_ether_cells, replay_tails, staircase_bound) < 1:
        raise ValueError("all bounds must be positive")
    macros = [glider_macro(n) for n in range(1, max_ether_cells + 1)]
    replays = [
        replay_macro_member(candidate, tail)
        for candidate in macros
        for tail in range(replay_tails)
    ]
    failures = [staircase_failure(n) for n in range(1, staircase_bound + 1)]
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "universal exact returning-macro constructor for every n>=1; "
            "literal linked-gate replay for listed n and tails; bounded "
            "failure only for the stated exhausted-tail staircase; no "
            "infinite macro orbit claim"
        ),
        "ether_gate": {"delay": 1, "collision_opcode": 2, "next_delay": 1},
        "defect_gate": {"delay": 1, "collision_opcode": 1, "next_delay": 1},
        "components": asdict(components()),
        "universal_macro": (
            "K=R_n+2^(8n+15)*q -> K'=S_n+3^(6n+11)*q"
        ),
        "bounds": {
            "ether_cells": [1, max_ether_cells],
            "tails_per_macro": replay_tails,
            "staircase_source_ether_cells": [1, staircase_bound],
        },
        "macro_count": len(macros),
        "macro_member_replays": len(replays),
        "linked_members_replayed": sum(
            replay.linked_members_replayed for replay in replays
        ),
        "literal_gate_macros_replayed": sum(
            replay.literal_gate_macros_replayed for replay in replays
        ),
        "macros": [asdict(candidate) for candidate in macros],
        "replay_samples": [
            asdict(replays[index])
            for index in sorted({0, len(replays) // 2, len(replays) - 1})
        ],
        "staircase_audit": {
            "schedule": "n -> n+1 with the first higher macro tail exhausted",
            "transitions_linked": len(failures),
            "depth_two_continuations": 0,
            "maximum_linked_macros": 2,
            "failures": [asdict(failure) for failure in failures],
        },
    }


def selftest() -> None:
    first = glider_macro(1)
    if first.input_packet_stride_exponent != 23:
        raise AssertionError("one-cell macro address width changed")
    replay_macro_member(first, 1)
    staircase_failure(1)


def render(certificate: dict[str, object]) -> str:
    return json.dumps(certificate, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-ether-cells", type=int, default=32)
    build.add_argument("--replay-tails", type=int, default=2)
    build.add_argument("--staircase-bound", type=int, default=128)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("breakoff ether-glider selftest: PASS")
    elif args.command == "build":
        certificate = build_certificate(
            args.max_ether_cells, args.replay_tails, args.staircase_bound
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
            int(bounds["tails_per_macro"]),
            int(bounds["staircase_source_ether_cells"][1]),
        )
        if actual != expected:
            raise AssertionError("artifact differs from exact recomputation")
        print("breakoff ether-glider artifact: PASS")


if __name__ == "__main__":
    main()
