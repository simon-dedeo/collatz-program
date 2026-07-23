#!/usr/bin/env python3
"""Exact successor cylinders and a finite ether-counter zero-tail transition.

The autonomous returning-glider counter has branch families

    K = R_n + 2^(8*n+15)*q  ->  K' = S_n + 3^(6*n+11)*q.

Intersecting the output of branch ``n`` with the input of branch ``m`` gives
one exact successor cylinder

    q  = a_(n,m) + 2^(8*m+15)*t,
    q' = b_(n,m) + 3^(6*n+11)*t.

Unlike a fixed lasso restriction, the surviving tail is multiplied by an odd
power of three.  It can therefore write low bits used by later branches.

For a compiled prefix, this module maintains the all-parameter invariant

    initial tail = A + 2^B*u,
    current tail = C + 3^P*u.

An extension whose new address digit is zero means that the canonical member
``u=0`` enters the next branch without consuming more nonzero bits of the
initial tail.  For an ordinary natural this eventually happens merely because
its binary expansion has ended, so one zero digit is not counter writing.
Exhausting all three-branch prefixes in
``1 <= n,m,l <= 160`` against the minimum-width next branch finds one such
event:

    115 -> 59 -> 9 -> 1.

The resulting ordinary positive packet executes four complete returning
glider macros and then halts.  Its zero digit starts exactly when the 574-bit
initial tail is exhausted; it is padding, not regenerated storage.  The true
target is a nonhalting deterministic tail-zero orbit.  This finite path is not
a Collatz counterexample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from functools import cache
from pathlib import Path
from typing import Any, Sequence

from breakoff_delay_gate import v2
from breakoff_ether_counter import (
    REGISTER_STRIDE,
    branch,
    check_branch_member,
    counter_next,
    packet_to_register,
    register_to_packet,
)
from breakoff_ether_glider import glider_macro, replay_macro_member


SCHEMA = "collatz-breakoff-ether-dynamics-v2"
MINIMUM_BRANCH_BITS = 23
CERTIFIED_BOUND = 160
ZERO_TAIL_BRANCHES = (115, 59, 9, 1)


def branch_input_packet(candidate: Any, tail: int) -> int:
    if tail < 0:
        raise ValueError("branch tail must be nonnegative")
    return candidate.input_packet_base + candidate.input_packet_stride * tail


def branch_output_packet(candidate: Any, tail: int) -> int:
    if tail < 0:
        raise ValueError("branch tail must be nonnegative")
    return candidate.output_packet_base + candidate.output_packet_stride * tail


@dataclass(frozen=True)
class SuccessorCylinder:
    source_branch: int
    target_branch: int
    address: int
    address_bits: int
    target_offset: int
    tail_multiplier: int

    def member(self, tail: int) -> tuple[int, int]:
        if tail < 0:
            raise ValueError("successor tail must be nonnegative")
        return (
            self.address + (1 << self.address_bits) * tail,
            self.target_offset + self.tail_multiplier * tail,
        )


@dataclass(frozen=True)
class PrefixCylinder:
    branches: tuple[int, ...]
    initial_address: int
    initial_bits: int
    current_offset: int
    current_multiplier: int
    address_digits: tuple[int, ...]
    address_widths: tuple[int, ...]

    @staticmethod
    def start(first_branch: int) -> "PrefixCylinder":
        if first_branch < 1:
            raise ValueError("ether branch must be positive")
        return PrefixCylinder(
            branches=(first_branch,),
            initial_address=0,
            initial_bits=0,
            current_offset=0,
            current_multiplier=1,
            address_digits=(),
            address_widths=(),
        )

    def extend(self, target_branch: int) -> "PrefixCylinder":
        edge = successor_cylinder(self.branches[-1], target_branch)
        modulus = 1 << edge.address_bits
        digit = (
            (edge.address - self.current_offset)
            * pow(self.current_multiplier, -1, modulus)
        ) % modulus
        numerator = (
            self.current_offset
            + self.current_multiplier * digit
            - edge.address
        )
        if numerator % modulus:
            raise AssertionError("prefix extension failed its exact division")
        residual = numerator // modulus
        if residual < 0:
            raise AssertionError("prefix extension produced a negative tail")
        return PrefixCylinder(
            branches=self.branches + (target_branch,),
            initial_address=(
                self.initial_address + (1 << self.initial_bits) * digit
            ),
            initial_bits=self.initial_bits + edge.address_bits,
            current_offset=(
                edge.target_offset + edge.tail_multiplier * residual
            ),
            current_multiplier=(
                edge.tail_multiplier * self.current_multiplier
            ),
            address_digits=self.address_digits + (digit,),
            address_widths=self.address_widths + (edge.address_bits,),
        )


@cache
def successor_cylinder(source_branch: int, target_branch: int) -> SuccessorCylinder:
    """Return the exact all-parameter intersection of two glider branches."""

    if source_branch < 1 or target_branch < 1:
        raise ValueError("ether branches must be positive")
    source = branch(source_branch)
    target = branch(target_branch)
    bits = target.input_packet_stride.bit_length() - 1
    if target.input_packet_stride != 1 << bits or bits != 8 * target_branch + 15:
        raise AssertionError("target branch lost its dyadic input stride")
    multiplier = source.output_packet_stride
    if multiplier != 3 ** source.ternary_exponent:
        raise AssertionError("source branch lost its ternary output stride")
    modulus = 1 << bits
    address = (
        (target.input_packet_base - source.output_packet_base)
        * pow(multiplier, -1, modulus)
    ) % modulus
    numerator = (
        source.output_packet_base
        + multiplier * address
        - target.input_packet_base
    )
    if numerator % modulus:
        raise AssertionError("successor cylinder failed its exact division")
    offset = numerator // modulus
    if offset < 0:
        raise AssertionError("least successor cylinder has negative output tail")
    result = SuccessorCylinder(
        source_branch=source_branch,
        target_branch=target_branch,
        address=address,
        address_bits=bits,
        target_offset=offset,
        tail_multiplier=multiplier,
    )
    for tail in (0, 1):
        source_tail, target_tail = result.member(tail)
        source_output = branch_output_packet(source, source_tail)
        target_input = branch_input_packet(target, target_tail)
        if source_output != target_input:
            raise AssertionError("successor cylinder coefficient identity failed")
    return result


def compile_prefix(branches: Sequence[int]) -> PrefixCylinder:
    if not branches:
        raise ValueError("branch prefix must be nonempty")
    prefix = PrefixCylinder.start(branches[0])
    for target in branches[1:]:
        prefix = prefix.extend(target)
    return prefix


def check_prefix_member(prefix: PrefixCylinder, tail: int) -> None:
    if tail < 0:
        raise ValueError("prefix tail must be nonnegative")
    initial_tail = prefix.initial_address + (1 << prefix.initial_bits) * tail
    current_tail = prefix.current_offset + prefix.current_multiplier * tail
    packet = branch_input_packet(branch(prefix.branches[0]), initial_tail)
    for source_branch, target_branch in zip(
        prefix.branches, prefix.branches[1:], strict=False
    ):
        source = branch(source_branch)
        source_difference = packet - source.input_packet_base
        if source_difference < 0 or source_difference % source.input_packet_stride:
            raise AssertionError("prefix packet missed its source branch")
        source_tail = source_difference // source.input_packet_stride
        packet = branch_output_packet(source, source_tail)
        target = branch(target_branch)
        target_difference = packet - target.input_packet_base
        if target_difference < 0 or target_difference % target.input_packet_stride:
            raise AssertionError("prefix packet missed its target branch")
    target = branch(prefix.branches[-1])
    if packet != branch_input_packet(target, current_tail):
        raise AssertionError("prefix closed form and linked packets disagree")


def exhaustive_branch_one_zero_tail(bound: int) -> dict[str, Any]:
    """Exhaust canonical three-branch prefixes for a zero-cost branch 1.

    The inner test needs only the generated current tail modulo ``2^23``.
    All divisions are nevertheless exact modular divisions: computing the
    numerator modulo ``2^(D+23)`` determines its quotient modulo ``2^23``.
    """

    if bound < max(ZERO_TAIL_BRANCHES[:-1]):
        raise ValueError("audit bound must contain the certified zero-tail path")
    transitions = [
        [None] * (bound + 1) for _ in range(bound + 1)
    ]
    multipliers = [0] * (bound + 1)
    for source in range(1, bound + 1):
        multipliers[source] = branch(source).output_packet_stride
        for target in range(1, bound + 1):
            transitions[source][target] = successor_cylinder(source, target)

    inverses = [
        [0] * (bound + 1) for _ in range(bound + 1)
    ]
    for source in range(1, bound + 1):
        for target in range(1, bound + 1):
            bits = transitions[1][target].address_bits
            inverses[source][target] = pow(
                multipliers[source], -1, 1 << bits
            )

    modulus_one = 1 << MINIMUM_BRANCH_BITS
    target_addresses = [0] * (bound + 1)
    for current in range(1, bound + 1):
        target_addresses[current] = successor_cylinder(current, 1).address

    hits: list[tuple[int, int, int]] = []
    checks = 0
    for middle in range(1, bound + 1):
        middle_multiplier_mod = multipliers[middle] % modulus_one
        for current in range(1, bound + 1):
            second = transitions[middle][current]
            bits = second.address_bits
            modulus = 1 << bits
            high_modulus = 1 << (bits + MINIMUM_BRANCH_BITS)
            high_mask = high_modulus - 1
            target_address = target_addresses[current]
            second_offset_mod = second.target_offset % modulus_one
            for first in range(1, bound + 1):
                first_edge = transitions[first][middle]
                digit = (
                    (second.address - first_edge.target_offset)
                    * inverses[first][current]
                ) % modulus
                numerator_mod = (
                    first_edge.target_offset
                    + (multipliers[first] % high_modulus) * digit
                    - second.address
                ) & high_mask
                if numerator_mod % modulus:
                    raise AssertionError("modular prefix quotient was not integral")
                residual_mod = numerator_mod >> bits
                current_offset_mod = (
                    second_offset_mod
                    + middle_multiplier_mod * residual_mod
                ) % modulus_one
                if current_offset_mod == target_address:
                    hits.append((first, middle, current))
                checks += 1

    if hits != [ZERO_TAIL_BRANCHES[:-1]]:
        raise AssertionError("bounded zero-tail census changed")
    prefix = compile_prefix(ZERO_TAIL_BRANCHES)
    if prefix.address_digits[-1] != 0:
        raise AssertionError("certified extension is not a zero address write")
    check_prefix_member(prefix, 0)
    check_prefix_member(prefix, 1)
    return {
        "branch_bound": bound,
        "triple_prefixes_checked": checks,
        "next_branch": 1,
        "next_branch_address_bits": MINIMUM_BRANCH_BITS,
        "hits": [list(hit) + [1] for hit in hits],
        "unique_hit": True,
        "scope": (
            "exhaustive for first,middle,current in 1..bound and a zero new "
            "address digit into branch 1; other next branches and longer "
            "prefixes are not excluded"
        ),
    }


def replay_zero_tail_transition() -> dict[str, Any]:
    prefix = compile_prefix(ZERO_TAIL_BRANCHES)
    if prefix.address_digits[-1] != 0:
        raise AssertionError("zero-tail prefix consumed another initial bit")
    initial_tail = prefix.initial_address
    first = branch(prefix.branches[0])
    initial_packet = branch_input_packet(first, initial_tail)
    initial_register = packet_to_register(initial_packet)
    if initial_register <= 0:
        raise AssertionError("zero-tail source is not an ordinary positive register")

    register = initial_register
    packet = initial_packet
    records: list[dict[str, Any]] = []
    preceding_ordinary_endpoint = None
    for expected_branch in ZERO_TAIL_BRANCHES:
        exponent = v2(register)
        actual_branch = (exponent + 5) // 8
        if exponent != 8 * expected_branch - 5 or actual_branch != expected_branch:
            raise AssertionError("public register selected the wrong branch")
        candidate = branch(expected_branch)
        difference = packet - candidate.input_packet_base
        if difference < 0 or difference % candidate.input_packet_stride:
            raise AssertionError("public packet missed its compiled branch")
        macro_tail = difference // candidate.input_packet_stride
        check_branch_member(candidate, macro_tail)
        replay = replay_macro_member(glider_macro(expected_branch), macro_tail)
        if preceding_ordinary_endpoint is not None and replay.ordinary_start != preceding_ordinary_endpoint:
            raise AssertionError("literal glider replays failed to link")
        following = counter_next(register)
        if following is None:
            raise AssertionError("certified public counter step halted early")
        output_packet = register_to_packet(following)
        if output_packet != replay.output_packet:
            raise AssertionError("public counter and literal glider endpoint disagree")
        records.append(
            {
                "branch": expected_branch,
                "macro_tail": macro_tail,
                "input_register": register,
                "output_register": following,
                "input_packet": packet,
                "output_packet": output_packet,
                "ordinary_start": replay.ordinary_start,
                "ordinary_endpoint": replay.ordinary_endpoint,
                "linked_members_replayed": replay.linked_members_replayed,
                "literal_gate_macros_replayed": replay.literal_gate_macros_replayed,
            }
        )
        preceding_ordinary_endpoint = replay.ordinary_endpoint
        register = following
        packet = output_packet

    if counter_next(register) is not None:
        raise AssertionError("finite zero-tail transition unexpectedly continued")
    successor_edges = []
    for source_branch, target_branch in zip(
        ZERO_TAIL_BRANCHES, ZERO_TAIL_BRANCHES[1:], strict=False
    ):
        edge = successor_cylinder(source_branch, target_branch)
        source = branch(source_branch)
        if edge.tail_multiplier <= 1 << edge.address_bits:
            raise AssertionError("zero-tail path lost its expanding tail slope")
        successor_edges.append(
            {
                "source_branch": source_branch,
                "target_branch": target_branch,
                "ternary_exponent": source.ternary_exponent,
                "address_bits_consumed": edge.address_bits,
                "tail_multiplier": edge.tail_multiplier,
                "tail_multiplier_floor_log2": edge.tail_multiplier.bit_length() - 1,
                "floor_log_scale_excess": (
                    edge.tail_multiplier.bit_length() - 1 - edge.address_bits
                ),
                "expanding_tail_slope": True,
            }
        )
    return {
        "branches": list(ZERO_TAIL_BRANCHES),
        "initial_tail": initial_tail,
        "initial_tail_bits": initial_tail.bit_length(),
        "initial_packet": initial_packet,
        "initial_packet_decimal_digits": len(str(initial_packet)),
        "initial_register": initial_register,
        "initial_register_decimal_digits": len(str(initial_register)),
        "prefix_address_bits": prefix.initial_bits,
        "address_digits": list(prefix.address_digits),
        "address_widths": list(prefix.address_widths),
        "final_address_digit_zero": True,
        "initial_tail_exhausted_before_zero_digit": (
            initial_tail.bit_length() == sum(prefix.address_widths[:-1])
        ),
        "zero_digit_interpretation": (
            "ordinary binary padding after the 574-bit initial tail is exhausted; "
            "not newly written independent storage"
        ),
        "generated_branch": 1,
        "successor_edges": successor_edges,
        "records": records,
        "successful_public_steps": len(records),
        "literal_linked_members_replayed": sum(
            record["linked_members_replayed"] for record in records
        ),
        "literal_gate_macros_replayed": sum(
            record["literal_gate_macros_replayed"] for record in records
        ),
        "ordinary_start": records[0]["ordinary_start"],
        "ordinary_endpoint": records[-1]["ordinary_endpoint"],
        "halting_register": register,
        "halting_register_v2": v2(register),
        "halt_reason": "public ether-counter transition is undefined after branch 1",
        "counterexample": None,
    }


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def build_audit(bound: int) -> dict[str, Any]:
    if bound != CERTIFIED_BOUND:
        raise ValueError(f"v1 certificate requires bound {CERTIFIED_BOUND}")
    # The complete pair box is reconstructed and checked coefficientwise by
    # the zero-tail census before its triple loop begins.
    census = exhaustive_branch_one_zero_tail(bound)
    replay = replay_zero_tail_transition()
    return {
        "successor_law": (
            "q=a_(n,m)+2^(8m+15)t; "
            "q'=b_(n,m)+3^(6n+11)t"
        ),
        "pair_cylinders_checked": bound * bound,
        "pair_tail_members_checked": 2 * bound * bound,
        "zero_tail_census": census,
        "finite_zero_tail_transition": replay,
        "claim_scope": (
            "exact coefficientwise successor cylinders in the stated pair "
            "box, exhaustive branch-1 zero-tail census in the stated triple "
            "box, and literal replay of the unique hit; finite only"
        ),
        "closure_status": {
            "counterexample": None,
            "achieved": "one ordinary finite transition after source-tail exhaustion",
            "missing": (
                "a nonhalting deterministic tail-zero orbit, equivalently one "
                "ordinary register with an infinite successful public-counter orbit"
            ),
        },
    }


def build_artifact(bound: int) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "verifier_sha256": source_sha256(),
        "audit": build_audit(bound),
    }
    data["artifact_sha256"] = hashlib.sha256(canonical_json(data)).hexdigest()
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    required = {
        "schema", "generated_at_utc", "verifier_sha256", "audit", "artifact_sha256"
    }
    if set(data) != required or data["schema"] != SCHEMA:
        raise ValueError("artifact schema mismatch")
    if data["verifier_sha256"] != source_sha256():
        raise ValueError("verifier hash mismatch")
    payload = dict(data)
    advertised = payload.pop("artifact_sha256")
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("artifact self-hash mismatch")
    bound = int(data["audit"]["zero_tail_census"]["branch_bound"])
    if data["audit"] != build_audit(bound):
        raise AssertionError("artifact differs from exact recomputation")
    finite = data["audit"]["finite_zero_tail_transition"]
    return {
        "artifact_sha256": advertised,
        "verifier_sha256": data["verifier_sha256"],
        "triple_prefixes_checked": data["audit"]["zero_tail_census"][
            "triple_prefixes_checked"
        ],
        "zero_tail_branches": finite["branches"],
        "successful_public_steps": finite["successful_public_steps"],
        "counterexample": None,
    }


def selftest() -> None:
    edge = successor_cylinder(1, 1)
    for tail in range(3):
        source_tail, target_tail = edge.member(tail)
        one = branch(1)
        if branch_output_packet(one, source_tail) != branch_input_packet(one, target_tail):
            raise AssertionError("one-cell successor cylinder changed")
    prefix = compile_prefix(ZERO_TAIL_BRANCHES)
    if prefix.address_digits[-1] != 0:
        raise AssertionError("zero-tail witness changed")
    check_prefix_member(prefix, 0)
    replay = replay_zero_tail_transition()
    if replay["successful_public_steps"] != 4 or replay["counterexample"] is not None:
        raise AssertionError("finite zero-tail replay changed")


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--branch-bound", type=int, default=CERTIFIED_BOUND)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv if argv is not None else None)
    if args.command == "selftest":
        selftest()
        print("breakoff ether-dynamics selftest: PASS")
        return 0
    if args.command == "build":
        selftest()
        args.output.write_text(
            json.dumps(build_artifact(args.branch_bound), indent=2, sort_keys=True) + "\n"
        )
        print(json.dumps(verify_artifact(args.output), sort_keys=True))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), sort_keys=True))
        return 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
