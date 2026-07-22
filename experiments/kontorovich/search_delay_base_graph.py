#!/usr/bin/env python3
"""Exact bounded search for ordinary base-to-base regenerative delay chains.

Every delay-gate shape ``(q,j,q')`` has one canonical least positive
coefficient in its affine residue class.  If its output coefficient is
literally the canonical coefficient of the next decoded shape, the link uses
tail zero on both sides: it asks for no additional bits of an initial 2-adic
address.  Such edges are therefore the sharpest small search for an ordinary
counter program after the dyadic-boundary theorem.

This worker exhausts a stated box of *symbolic gate shapes*, not a range of
Collatz seeds.  Retained edges are replayed through the canonical executable
gate checker.  Finite chains are not counterexamples.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path

from breakoff_delay_gate import check_gate_member, gate, v2


SCHEMA = "collatz-breakoff-base-graph-v2"


@dataclass(frozen=True)
class Shape:
    delay: int
    collision_opcode: int
    next_delay: int


@dataclass(frozen=True)
class RawGate:
    shape: Shape
    coefficient: int
    collision_payload: int
    output_coefficient: int


@dataclass(frozen=True)
class DecodedSuccessor:
    shape: Shape
    collision_payload: int
    output_coefficient: int


@dataclass(frozen=True)
class BaseEdge:
    source: Shape
    target: Shape
    source_coefficient: int
    linked_coefficient: int
    target_output_coefficient: int
    target_terminal_reason: str
    canonical_source: bool
    ordinary_start: int
    ordinary_steps_to_one: int
    ordinary_peak: int


def raw_gate(shape: Shape) -> RawGate:
    q = shape.delay
    j = shape.collision_opcode
    q_next = shape.next_delay
    if q < 1 or j < 0 or q_next < 1:
        raise ValueError("delays must be positive and opcode nonnegative")
    emitted_exponent = 3 * (q_next + 1)
    total_exponent = j + emitted_exponent
    ternary_exponent = j + 2 * q + 2
    modulus = 1 << (total_exponent + 1)
    target = (
        pow(3, j) - pow(2, j) + (1 << total_exponent)
    ) % modulus
    coefficient = (
        target * pow(pow(3, ternary_exponent), -1, modulus)
    ) % modulus
    if coefficient == 0:
        coefficient = modulus
    collision_numerator = pow(3, 2 * q + 2) * coefficient - 1
    if v2(collision_numerator) != j:
        raise AssertionError("raw constructor missed the collision opcode")
    payload = collision_numerator >> j
    renewal_numerator = pow(3, j) * payload + 1
    if v2(renewal_numerator) != emitted_exponent:
        raise AssertionError("raw constructor missed the output delay")
    return RawGate(
        shape=shape,
        coefficient=coefficient,
        collision_payload=payload,
        output_coefficient=renewal_numerator >> emitted_exponent,
    )


def coefficient_modulus(shape: Shape) -> int:
    return 1 << (shape.collision_opcode + 3 * (shape.next_delay + 1) + 1)


def decode_successor(delay: int, coefficient: int) -> tuple[
    DecodedSuccessor | None, str
]:
    if delay < 1 or coefficient <= 0 or coefficient % 2 == 0:
        raise ValueError("expected a positive delay and odd coefficient")
    collision = pow(3, 2 * delay + 2) * coefficient - 1
    opcode = v2(collision)
    payload = collision >> opcode
    renewal = pow(3, opcode) * payload + 1
    exponent = v2(renewal)
    if exponent < 6:
        return None, "output valuation below one clean delay cell"
    if exponent % 3:
        return None, "output valuation is not a multiple of three"
    next_delay = exponent // 3 - 1
    return DecodedSuccessor(
        shape=Shape(delay, opcode, next_delay),
        collision_payload=payload,
        output_coefficient=renewal >> exponent,
    ), "renewed"


def exact_collatz_continuation(start: int, cap: int = 100_000) -> tuple[int, int]:
    """Return exact ordinary step count and peak, requiring a visit to one."""
    if start <= 0:
        raise ValueError("expected a positive ordinary start")
    value = start
    peak = start
    for steps in range(cap + 1):
        if value == 1:
            return steps, peak
        value = value // 2 if value % 2 == 0 else 3 * value + 1
        peak = max(peak, value)
    raise AssertionError("retained base edge did not reach one within cap")


def check_base_edge(source_gate: RawGate) -> BaseEdge | None:
    successor, _ = decode_successor(
        source_gate.shape.next_delay, source_gate.output_coefficient
    )
    if successor is None:
        return None
    target_gate = raw_gate(successor.shape)
    if source_gate.output_coefficient != target_gate.coefficient:
        return None

    # The edge is independently replayed through every executable delay tick
    # and collision in the canonical router implementation.
    literal_source = gate(
        source_gate.shape.delay,
        source_gate.shape.collision_opcode,
        source_gate.shape.next_delay,
    )
    literal_target = gate(
        successor.shape.delay,
        successor.shape.collision_opcode,
        successor.shape.next_delay,
    )
    if literal_source.coefficient_residue != source_gate.coefficient:
        raise AssertionError("source constructor implementations disagree")
    if literal_target.coefficient_residue != target_gate.coefficient:
        raise AssertionError("target constructor implementations disagree")
    check_gate_member(literal_source, 0)
    check_gate_member(literal_target, 0)
    first_endpoint = literal_source.member(0)[5]
    second_start = literal_target.member(0)[3]
    if first_endpoint != second_start:
        raise AssertionError("base edge endpoints do not link")

    after_target, terminal_reason = decode_successor(
        successor.shape.next_delay, target_gate.output_coefficient
    )
    if after_target is not None:
        after_target_base = raw_gate(after_target.shape).coefficient
        if target_gate.output_coefficient == after_target_base:
            terminal_reason = "continues with another base edge"
        else:
            terminal_reason = "renews only in a positive-tail cylinder"
    ordinary_start = (
        9 * pow(2, 3 * source_gate.shape.delay) * source_gate.coefficient - 1
    )
    steps_to_one, peak = exact_collatz_continuation(ordinary_start)
    return BaseEdge(
        source=source_gate.shape,
        target=successor.shape,
        source_coefficient=source_gate.coefficient,
        linked_coefficient=source_gate.output_coefficient,
        target_output_coefficient=target_gate.output_coefficient,
        target_terminal_reason=terminal_reason,
        canonical_source=source_gate.coefficient % 8 != 0,
        ordinary_start=ordinary_start,
        ordinary_steps_to_one=steps_to_one,
        ordinary_peak=peak,
    )


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def build_certificate(
    max_delay: int, max_opcode: int, max_next_delay: int
) -> dict[str, object]:
    if min(max_delay, max_next_delay) < 1 or max_opcode < 0:
        raise ValueError("invalid audit bounds")
    counts = {
        "shapes": 0,
        "no_clean_successor": 0,
        "positive_tail_successor": 0,
        "canonical_base_edges": 0,
        "noncanonical_base_aliases": 0,
    }
    edges: list[BaseEdge] = []
    for q in range(1, max_delay + 1):
        for j in range(max_opcode + 1):
            for q_next in range(1, max_next_delay + 1):
                counts["shapes"] += 1
                source = raw_gate(Shape(q, j, q_next))
                successor, _ = decode_successor(
                    q_next, source.output_coefficient
                )
                if successor is None:
                    counts["no_clean_successor"] += 1
                    continue
                target = raw_gate(successor.shape)
                if source.output_coefficient != target.coefficient:
                    difference = source.output_coefficient - target.coefficient
                    if (
                        difference <= 0
                        or difference % coefficient_modulus(successor.shape)
                    ):
                        raise AssertionError(
                            "decoded successor missed its affine cylinder"
                        )
                    counts["positive_tail_successor"] += 1
                    continue
                edge = check_base_edge(source)
                if edge is None:
                    raise AssertionError("base-edge classifiers disagree")
                edges.append(edge)
                counts[
                    "canonical_base_edges"
                    if edge.canonical_source
                    else "noncanonical_base_aliases"
                ] += 1
    if sum(counts[key] for key in (
        "no_clean_successor",
        "positive_tail_successor",
        "canonical_base_edges",
        "noncanonical_base_aliases",
    )) != counts["shapes"]:
        raise AssertionError("classification is not exhaustive")
    canonical_edges = [edge for edge in edges if edge.canonical_source]
    depth_two = [
        edge for edge in canonical_edges
        if edge.target_terminal_reason == "continues with another base edge"
    ]
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exhaustive canonical-tail-zero classification of every delay "
            "gate shape in the stated source box; every retained edge and "
            "its target gate are literally replayed; no claim outside the "
            "source bounds and no infinite orbit claim"
        ),
        "bounds": {
            "delay": [1, max_delay],
            "collision_opcode": [0, max_opcode],
            "next_delay": [1, max_next_delay],
        },
        "counts": counts,
        "maximum_canonical_base_edge_chain": (
            2 if depth_two else (1 if canonical_edges else 0)
        ),
        "depth_two_base_edges": [asdict(edge) for edge in depth_two],
        "canonical_base_edges": [asdict(edge) for edge in canonical_edges],
        "noncanonical_base_aliases": [
            asdict(edge) for edge in edges if not edge.canonical_source
        ],
    }


def selftest() -> None:
    certificate = build_certificate(8, 16, 8)
    if certificate["counts"]["shapes"] != 8 * 17 * 8:
        raise AssertionError("selftest shape count changed")
    if certificate["maximum_canonical_base_edge_chain"] > 1:
        raise AssertionError("unexpected small depth-two base edge")


def render(certificate: dict[str, object]) -> str:
    return json.dumps(certificate, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-delay", type=int, default=100)
    build.add_argument("--max-opcode", type=int, default=100)
    build.add_argument("--max-next-delay", type=int, default=100)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("delay base-graph selftest: PASS")
    elif args.command == "build":
        certificate = build_certificate(
            args.max_delay, args.max_opcode, args.max_next_delay
        )
        args.output.write_text(render(certificate))
        print(f"wrote {args.output}")
    else:
        expected = json.loads(args.artifact.read_text())
        if expected.get("schema") != SCHEMA:
            raise ValueError("unexpected artifact schema")
        bounds = expected["bounds"]
        actual = build_certificate(
            int(bounds["delay"][1]),
            int(bounds["collision_opcode"][1]),
            int(bounds["next_delay"][1]),
        )
        if actual != expected:
            raise AssertionError("artifact differs from exact recomputation")
        print("delay base-graph artifact: PASS")


if __name__ == "__main__":
    main()
