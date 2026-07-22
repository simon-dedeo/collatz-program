#!/usr/bin/env python3
"""Exact tag-transducer semantics of linked two-rail Collatz gates.

A two-rail gate has an odd family index ``z`` only in the informal software
sense; the literal input and output payloads are

    P_in(z)  = a + 2^D z,
    P_out(z) = c + 2*3^R z.

Linking the output to a target gate therefore reads one residue of ``z``
modulo ``2^(D_target-1)``.  On the residual tail ``u`` the next family index
is ``w0 + 3^R u``.  This is an exact variable-length tag instruction: delete
a low binary address block, multiply the remaining tape by a power of three,
and append a fixed offset.

The bounded audit is a regression over gate *shapes*, not a seed interval.
It records a two-gate canonical handoff but no third gate in its stated box.
The witness reaches 1 and is not a counterexample.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path

from path_compiler import accelerated_step
from two_rail_gate import TwoRailGate, two_rail_gate, verify_member


SCHEMA = "collatz-two-rail-transducer-audit-v1"


@dataclass(frozen=True)
class GateShape:
    amp_ticks: int
    clean_ticks: int
    to_plus_extra: int
    to_minus_extra: int
    output_gap: int

    @classmethod
    def of(cls, gate: TwoRailGate) -> GateShape:
        return cls(
            amp_ticks=gate.amp_ticks,
            clean_ticks=gate.clean_ticks,
            to_plus_extra=gate.to_plus_extra,
            to_minus_extra=gate.to_minus_extra,
            output_gap=gate.output_gap,
        )

    def build(self) -> TwoRailGate:
        return two_rail_gate(
            self.amp_ticks,
            self.clean_ticks,
            self.to_plus_extra,
            self.to_minus_extra,
            self.output_gap,
        )


@dataclass(frozen=True)
class IndexInstruction:
    source: GateShape
    target: GateShape
    address_bits: int
    source_index_base: int
    source_index_stride: int
    target_index_base: int
    target_index_stride: int

    def indices(self, tail: int) -> tuple[int, int]:
        if tail < 0:
            raise ValueError("tail must be nonnegative")
        return (
            self.source_index_base + self.source_index_stride * tail,
            self.target_index_base + self.target_index_stride * tail,
        )


def _power_of_two_exponent(value: int) -> int:
    if value <= 0 or value & (value - 1):
        raise ValueError("expected a positive power of two")
    return value.bit_length() - 1


def index_instruction(source: TwoRailGate, target: TwoRailGate) -> IndexInstruction:
    """Return the complete nonnegative family linking ``source`` to ``target``."""
    if source.output_gap != target.input_gap:
        raise ValueError("the sparse output and input gaps do not link")

    source_multiplier = source.output_payload_stride // 2
    if source.output_payload_stride != 2 * source_multiplier:
        raise AssertionError("unexpected source output stride")
    target_exponent = _power_of_two_exponent(target.input_payload_stride)
    address_bits = target_exponent - 1
    modulus = 1 << address_bits
    offset = (source.output_payload_base - target.input_payload_base) // 2
    if source.output_payload_base % 2 != target.input_payload_base % 2:
        raise AssertionError("payload bases must have the same parity")

    residue = (-offset * pow(source_multiplier, -1, modulus)) % modulus
    target_base = (source_multiplier * residue + offset) // modulus
    if source_multiplier * residue + offset != modulus * target_base:
        raise AssertionError("index congruence solver failed")

    # Small representatives of the congruence can formally give a negative
    # target index.  Move to the first lift for which both indices are natural.
    if target_base < 0:
        lifts = (-target_base + source_multiplier - 1) // source_multiplier
        residue += modulus * lifts
        target_base += source_multiplier * lifts

    instruction = IndexInstruction(
        source=GateShape.of(source),
        target=GateShape.of(target),
        address_bits=address_bits,
        source_index_base=residue,
        source_index_stride=modulus,
        target_index_base=target_base,
        target_index_stride=source_multiplier,
    )
    verify_instruction(instruction, tails=8)
    return instruction


def verify_instruction(instruction: IndexInstruction, tails: int) -> None:
    source = instruction.source.build()
    target = instruction.target.build()
    if instruction.source_index_stride != 1 << instruction.address_bits:
        raise AssertionError("address stride mismatch")
    if instruction.target_index_stride != source.output_payload_stride // 2:
        raise AssertionError("triadic tail stride mismatch")
    for tail in range(tails):
        source_index, target_index = instruction.indices(tail)
        source_payload = source.payloads(source_index)[2]
        target_payload = target.payloads(target_index)[0]
        if source_payload != target_payload:
            raise AssertionError("linked payloads differ")
        source_endpoint = -1 + (1 << source.output_gap) * source_payload
        target_start = -1 + (1 << target.input_gap) * target_payload
        if source_endpoint != target_start:
            raise AssertionError("linked sparse states differ")


def sparse_bounds(gate: TwoRailGate, family_index: int) -> tuple[int, int]:
    p, _, p_next = gate.payloads(family_index)
    return (
        -1 + (1 << gate.input_gap) * p,
        -1 + (1 << gate.output_gap) * p_next,
    )


def universally_outward_on_instruction(instruction: IndexInstruction) -> bool:
    """Check the two affine coefficients, proving every linked member outward."""
    source = instruction.source.build()
    start0, endpoint0 = sparse_bounds(source, instruction.source_index_base)
    start1, endpoint1 = sparse_bounds(
        source,
        instruction.source_index_base + instruction.source_index_stride,
    )
    return endpoint0 > start0 and endpoint1 - endpoint0 >= start1 - start0


def continuation(seed: int, limit: int = 100_000) -> dict[str, int | bool]:
    state = seed
    peak = seed
    peak_at = 0
    steps = 0
    halvings = 0
    while state != 1 and steps < limit:
        state, valuation = accelerated_step(state)
        steps += 1
        halvings += valuation
        if state > peak:
            peak = state
            peak_at = steps
    return {
        "limit": limit,
        "reached_one": state == 1,
        "accelerated_steps": steps,
        "total_halvings": halvings,
        "ordinary_steps": steps + halvings,
        "peak": peak,
        "peak_at_accelerated_step": peak_at,
    }


def _enumerate_outward_gates(bounds: dict[str, int]) -> tuple[int, list[TwoRailGate]]:
    total = 0
    outward: list[TwoRailGate] = []
    for r in range(1, bounds["max_amp_ticks"] + 1):
        for s in range(bounds["max_clean_ticks"] + 1):
            for a in range(1, bounds["max_collision_extra"] + 1):
                for b in range(1, bounds["max_collision_extra"] + 1):
                    for output_gap in range(2, bounds["max_output_gap"] + 1):
                        gate = two_rail_gate(r, s, a, b, output_gap)
                        total += 1
                        start, endpoint = sparse_bounds(gate, 0)
                        if endpoint > start:
                            outward.append(gate)
    return total, outward


def _canonical_target_count(
    amp_ticks: int,
    input_payload: int,
    max_clean_ticks: int,
    max_collision_extra: int,
    max_output_gap: int,
) -> int:
    count = 0
    for s in range(max_clean_ticks + 1):
        for a in range(1, max_collision_extra + 1):
            for b in range(1, max_collision_extra + 1):
                for output_gap in range(2, max_output_gap + 1):
                    gate = two_rail_gate(amp_ticks, s, a, b, output_gap)
                    if gate.input_payload_base == input_payload:
                        count += 1
    return count


def bounded_audit() -> dict[str, object]:
    bounds = {
        "max_amp_ticks": 40,
        "max_clean_ticks": 4,
        "max_collision_extra": 4,
        "max_output_gap": 41,
    }
    total, outward = _enumerate_outward_gates(bounds)
    by_input: dict[tuple[int, int], list[int]] = defaultdict(list)
    sparse: list[tuple[int, int]] = []
    for index, gate in enumerate(outward):
        by_input[(gate.amp_ticks, gate.input_payload_base)].append(index)
        sparse.append(sparse_bounds(gate, 0))

    edges: dict[int, list[int]] = {}
    for index, gate in enumerate(outward):
        targets = by_input.get((gate.output_gap - 1, gate.output_payload_base), [])
        if targets:
            if any(sparse[index][1] != sparse[target][0] for target in targets):
                raise AssertionError("canonical sparse link mismatch")
            edges[index] = list(targets)

    # Every edge increases its literal state, so descending state order is a
    # topological order even if distinct gate shapes share a start.
    depth: dict[int, int] = {}
    next_gate: dict[int, int] = {}
    for index in sorted(range(len(outward)), key=lambda i: sparse[i][0], reverse=True):
        best_depth = 1
        best_target = -1
        for target in edges.get(index, []):
            candidate = 1 + depth[target]
            if candidate > best_depth:
                best_depth = candidate
                best_target = target
        depth[index] = best_depth
        if best_target >= 0:
            next_gate[index] = best_target

    maximum_depth = max(depth.values())
    first = min(
        (index for index, value in depth.items() if value == maximum_depth),
        key=lambda index: sparse[index][0],
    )
    chain_indices: list[int] = []
    cursor = first
    while True:
        chain_indices.append(cursor)
        if cursor not in next_gate:
            break
        cursor = next_gate[cursor]
    chain = [outward[index] for index in chain_indices]
    if len(chain) != 2:
        raise AssertionError("bounded canonical-chain regression changed")

    first_start, first_endpoint = verify_member(chain[0], 0)
    second_start, second_endpoint = verify_member(chain[1], 0)
    if first_endpoint != second_start:
        raise AssertionError("witness gates are not linked")
    first_word = (
        [1] * chain[0].amp_ticks
        + [1 + chain[0].to_plus_extra]
        + [2] * chain[0].clean_ticks
        + [2 + chain[0].to_minus_extra]
    )
    second_word = (
        [1] * chain[1].amp_ticks
        + [1 + chain[1].to_plus_extra]
        + [2] * chain[1].clean_ticks
        + [2 + chain[1].to_minus_extra]
    )
    next_target_bounds = {
        "target_amp_ticks": chain[1].output_gap - 1,
        "target_input_payload": chain[1].output_payload_base,
        "max_clean_ticks": 20,
        "max_collision_extra": 20,
        "max_output_gap": 300,
    }
    next_target_count = _canonical_target_count(
        amp_ticks=next_target_bounds["target_amp_ticks"],
        input_payload=next_target_bounds["target_input_payload"],
        max_clean_ticks=next_target_bounds["max_clean_ticks"],
        max_collision_extra=next_target_bounds["max_collision_extra"],
        max_output_gap=next_target_bounds["max_output_gap"],
    )
    return {
        "schema": SCHEMA,
        "claim_scope": (
            "exact bounded audit of canonical zero-preload links between "
            "two-rail gate shapes; not a seed-range verification"
        ),
        "bounds": bounds,
        "gate_shapes_checked": total,
        "outward_canonical_gates": len(outward),
        "outward_canonical_links": sum(len(targets) for targets in edges.values()),
        "maximum_linked_gate_count": depth[first],
        "witness": {
            "gate_shapes": [asdict(GateShape.of(gate)) for gate in chain],
            "payloads": [
                {
                    "input": gate.input_payload_base,
                    "plus": gate.plus_payload_base,
                    "output": gate.output_payload_base,
                }
                for gate in chain
            ],
            "seed": first_start,
            "middle": first_endpoint,
            "endpoint": second_endpoint,
            "valuations": first_word + second_word,
            "all_gates_outward": first_start < first_endpoint < second_endpoint,
            "continuation": continuation(first_start),
        },
        "next_target_audit": next_target_bounds
        | {"matching_canonical_gates": next_target_count},
    }


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported artifact schema")
    expected = bounded_audit()
    if data != expected:
        raise ValueError("transducer artifact failed exact reconstruction")


def selftest() -> None:
    standard_source = two_rail_gate(4, 1, 1, 1, 6)
    standard_target = two_rail_gate(5, 1, 1, 1, 7)
    standard = index_instruction(standard_source, standard_target)
    assert standard.address_bits == 13
    verify_instruction(standard, tails=32)

    source = two_rail_gate(4, 0, 1, 1, 7)
    target = two_rail_gate(6, 1, 1, 1, 4)
    canonical = index_instruction(source, target)
    assert canonical.source_index_base == 0
    assert canonical.target_index_base == 0
    assert universally_outward_on_instruction(canonical)
    verify_instruction(canonical, tails=32)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    describe = subparsers.add_parser("describe-standard")
    describe.add_argument("--amp-ticks", type=int, default=4)
    build = subparsers.add_parser("build-audit")
    build.add_argument("output", type=Path)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("two_rail_transducer selftest: PASS")
    elif args.command == "describe-standard":
        source = two_rail_gate(args.amp_ticks, 1, 1, 1, args.amp_ticks + 2)
        target = two_rail_gate(
            args.amp_ticks + 1, 1, 1, 1, args.amp_ticks + 3
        )
        print(json.dumps(asdict(index_instruction(source, target)), indent=2))
    elif args.command == "build-audit":
        data = bounded_audit()
        args.output.write_text(json.dumps(data, indent=2) + "\n")
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("two_rail_transducer artifact: PASS")


if __name__ == "__main__":
    main()
