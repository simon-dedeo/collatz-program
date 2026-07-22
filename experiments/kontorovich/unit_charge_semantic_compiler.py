#!/usr/bin/env python3
"""Descend the normalized charge bouncer to literal Collatz words.

The charge bouncer lives several exact affine coordinate changes above the
ordinary odd Collatz state.  In particular, the field called
``ordinary_start`` by ``breakoff_ether_glider`` is still the intermediate
breakoff coordinate ``k``.  The final conversion is performed by
``router_breakoff.literal_step(k)``.

This worker makes every layer explicit:

    public y -> charge packet -> unit packet -> level-two parent packet
      -> level-one glider packet -> breakoff k -> odd Collatz state.

It also expands a bouncer block by the symbolic substitutions

    charge cell N       -> unit cells [N, 1],
    level-two cell N    -> level-one gliders [1, 2] + [1]^N,
    level-one glider N  -> breakoff gates [E, H] + [E]^N,

and finally concatenates the literal accelerated valuation words returned by
the breakoff router.  Every emitted word is independently replayed by direct
``3*x+1`` arithmetic.  The default artifact covers all 27 public branches
with ``1 <= m,h,m' <= 3`` and two members per branch.

This is a bounded research-side semantic regression, not a universal Lean
compiler and not an infinite orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

from breakoff_delay_gate import DelayGate, v2
from breakoff_ether_glider import (
    components as glider_components,
    glider_macro,
    machines as glider_machines,
)
from breakoff_renormalization import (
    construct_hierarchy,
    expand_to_level_one,
    parent_input_tail,
)
from breakoff_unit_slice import UnitBranch, unit_branch, unit_isa
from router_breakoff import literal_step
from unit_charge_bouncer import (
    BouncerTransition,
    bouncer_step,
    packet_to_y,
    reverse_bouncer_step,
    transition_family,
)
from unit_charge_discharge import (
    ChargeBranch,
    construct_isa,
    direct_branch,
)


SCHEMA = "collatz-unit-charge-semantic-compiler-v1"


@dataclass(frozen=True)
class BoundaryEncoding:
    charge_packet: int
    unit_packet: int
    level_two_packet: int
    level_one_macro_tail: int
    level_one_packet: int
    breakoff_tail: int
    breakoff_state: int
    router_rail_length: int
    collatz_state: int


@dataclass(frozen=True)
class LiteralTrace:
    word: tuple[int, ...]
    start: int
    endpoint: int
    glider_macros: int
    breakoff_macros: int


def decimal_sha256(value: int) -> str:
    return hashlib.sha256(str(value).encode()).hexdigest()


def word_sha256(word: tuple[int, ...]) -> str:
    payload = ",".join(map(str, word)).encode()
    return hashlib.sha256(payload).hexdigest()


def locate_charge_tail(branch: ChargeBranch, packet: int) -> int:
    difference = packet - branch.input_packet_base
    stride = 1 << branch.input_packet_stride_exponent
    if difference < 0 or difference % stride:
        raise AssertionError("packet missed its charge branch")
    return difference // stride


def locate_unit_tail(branch: UnitBranch, packet: int) -> int:
    difference = packet - branch.input_packet_base
    stride = 1 << branch.input_packet_stride_exponent
    if difference < 0 or difference % stride:
        raise AssertionError("packet missed its unit branch")
    return difference // stride


def append_trace(first: LiteralTrace | None, second: LiteralTrace) -> LiteralTrace:
    if first is None:
        return second
    if first.endpoint != second.start:
        raise AssertionError("literal trace segments do not link")
    return LiteralTrace(
        word=first.word + second.word,
        start=first.start,
        endpoint=second.endpoint,
        glider_macros=first.glider_macros + second.glider_macros,
        breakoff_macros=first.breakoff_macros + second.breakoff_macros,
    )


def replay_accelerated(start: int, word: tuple[int, ...]) -> int:
    """Replay an emitted word without using any hierarchy helper."""
    state = start
    for index, claimed in enumerate(word):
        if state <= 0 or state % 2 != 1:
            raise AssertionError(f"word state {index} is not positive odd")
        numerator = 3 * state + 1
        actual = v2(numerator)
        if actual != claimed:
            raise AssertionError(
                f"literal valuation mismatch at {index}: {actual} != {claimed}"
            )
        state = numerator >> actual
    return state


def breakoff_affine_constants() -> tuple[int, int]:
    """Return ``slope,intercept`` for level-two packet -> breakoff ``k``."""
    one = encode_level_two_packet(1).breakoff_state
    two = encode_level_two_packet(2).breakoff_state
    slope = two - one
    intercept = one - slope
    if slope <= 0:
        raise AssertionError("breakoff embedding lost positive slope")
    return slope, intercept


def encode_level_two_packet(packet: int) -> BoundaryEncoding:
    """Descend one positive level-two parent packet to literal Collatz state."""
    if packet < 1:
        raise ValueError("level-two packet must be positive")
    hierarchy, steps = construct_hierarchy(6)
    step = steps[0]
    tail = parent_input_tail(step, packet)
    level_one = glider_macro(1).member(tail)[0]
    encoded = encode_level_one_packet(level_one)
    return BoundaryEncoding(
        charge_packet=-1,
        unit_packet=-1,
        level_two_packet=packet,
        level_one_macro_tail=tail,
        level_one_packet=level_one,
        breakoff_tail=encoded.breakoff_tail,
        breakoff_state=encoded.breakoff_state,
        router_rail_length=encoded.router_rail_length,
        collatz_state=encoded.collatz_state,
    )


def encode_level_one_packet(packet: int) -> BoundaryEncoding:
    """Decode a global level-one packet, independently of its next opcode."""
    if packet < 0:
        raise ValueError("level-one packet must be nonnegative")
    data = glider_components()
    breakoff_tail = data.defect_input_constant + (
        (1 << data.defect_input_stride_exponent) * packet
    )
    ether = glider_machines()[0]
    breakoff = ether.member(breakoff_tail)[3]
    routed = literal_step(breakoff)
    if routed is None:
        raise AssertionError("canonical breakoff boundary failed router decoding")
    return BoundaryEncoding(
        charge_packet=-1,
        unit_packet=-1,
        level_two_packet=-1,
        level_one_macro_tail=-1,
        level_one_packet=packet,
        breakoff_tail=breakoff_tail,
        breakoff_state=breakoff,
        router_rail_length=routed.rail_length,
        collatz_state=routed.collatz_start,
    )


def encode_charge_packet(packet: int) -> BoundaryEncoding:
    """Apply both invariant slices, then descend to the literal odd state."""
    if packet < 0:
        raise ValueError("charge packet must be nonnegative")
    charge = construct_isa()
    hierarchy, _ = construct_hierarchy(6)
    parent = hierarchy[1]
    unit = unit_isa(parent)
    unit_packet = (
        charge.packet_residue_mod_divisor
        + charge.removed_divisor * packet
    )
    level_two = unit.parent_packet_residue_mod_17 + 17 * unit_packet
    encoded = encode_level_two_packet(level_two)
    return BoundaryEncoding(
        charge_packet=packet,
        unit_packet=unit_packet,
        level_two_packet=level_two,
        level_one_macro_tail=encoded.level_one_macro_tail,
        level_one_packet=encoded.level_one_packet,
        breakoff_tail=encoded.breakoff_tail,
        breakoff_state=encoded.breakoff_state,
        router_rail_length=encoded.router_rail_length,
        collatz_state=encoded.collatz_state,
    )


def trace_delay_gate(candidate: DelayGate, tail: int) -> LiteralTrace:
    """Expand one delay gate through its consecutive breakoff steps."""
    _, _, _, breakoff, _, expected_breakoff = candidate.member(tail)
    word: tuple[int, ...] = ()
    start: int | None = None
    endpoint: int | None = None
    for _ in range(candidate.delay + 1):
        routed = literal_step(breakoff)
        if routed is None:
            raise AssertionError("delay gate emitted an illegal router step")
        if endpoint is not None and endpoint != routed.collatz_start:
            raise AssertionError("consecutive router steps do not link")
        if start is None:
            start = routed.collatz_start
        word += tuple(routed.valuation_word)
        endpoint = routed.collatz_endpoint
        breakoff = routed.next_k
    if breakoff != expected_breakoff or start is None or endpoint is None:
        raise AssertionError("delay gate missed its breakoff endpoint")
    if replay_accelerated(start, word) != endpoint:
        raise AssertionError("delay-gate word failed independent replay")
    return LiteralTrace(
        word=word,
        start=start,
        endpoint=endpoint,
        glider_macros=0,
        breakoff_macros=candidate.delay + 1,
    )


def glider_gate_sequence(cells: int, tail: int) -> list[tuple[DelayGate, int]]:
    """Return the nonduplicated gate execution ``E,H,E^cells``."""
    candidate = glider_macro(cells)
    data = glider_components()
    ether, defect, into_defect, from_defect, self_link = glider_machines()
    input_packet, _ = candidate.member(tail)
    u = (1 << data.inherited_ether_bits) * input_packet - 1
    v = data.bridge_residual_base + 256 * u
    first, defect_tail = into_defect.member(v)
    w = data.bridge_tail_base + 729 * u
    checked, current = from_defect.member(w)
    if checked != defect_tail:
        raise AssertionError("glider defect tails disagree")
    sequence = [(ether, first), (defect, defect_tail)]
    for _ in range(cells):
        sequence.append((ether, current))
        difference = current - self_link.first_tail_base
        if difference < 0 or difference % self_link.first_tail_stride:
            raise AssertionError("glider ether missed its self-link")
        current = self_link.member(
            difference // self_link.first_tail_stride
        )[1]
    final_breakoff = ether.member(current)[3]
    final_router = literal_step(final_breakoff)
    if final_router is None:
        raise AssertionError("glider endpoint failed router decoding")
    return sequence


def trace_glider(cells: int, tail: int) -> LiteralTrace:
    trace: LiteralTrace | None = None
    for candidate, gate_tail in glider_gate_sequence(cells, tail):
        trace = append_trace(trace, trace_delay_gate(candidate, gate_tail))
    if trace is None:
        raise AssertionError("glider emitted no gates")
    output_packet = glider_macro(cells).member(tail)[1]
    # A level-one packet has an opcode-independent boundary encoding; the
    # following macro restriction determines only which word executes next.
    next_breakoff = encode_level_one_packet(output_packet)
    if trace.endpoint != next_breakoff.collatz_state:
        raise AssertionError("glider literal endpoint missed its packet output")
    return LiteralTrace(
        word=trace.word,
        start=trace.start,
        endpoint=trace.endpoint,
        glider_macros=1,
        breakoff_macros=trace.breakoff_macros,
    )


def encode_level_one_tail(tail: int) -> BoundaryEncoding:
    """Decode the source of a one-cell level-one glider macro."""
    if tail < 0:
        raise ValueError("level-one tail must be nonnegative")
    level_one = glider_macro(1).member(tail)[0]
    encoded = encode_level_one_packet(level_one)
    return BoundaryEncoding(
        charge_packet=-1,
        unit_packet=-1,
        level_two_packet=-1,
        level_one_macro_tail=tail,
        level_one_packet=level_one,
        breakoff_tail=encoded.breakoff_tail,
        breakoff_state=encoded.breakoff_state,
        router_rail_length=encoded.router_rail_length,
        collatz_state=encoded.collatz_state,
    )


def trace_level_two(cells: int, tail: int) -> LiteralTrace:
    hierarchy, steps = construct_hierarchy(6)
    if hierarchy[1].level != 2:
        raise AssertionError("semantic compiler requires hierarchy level two")
    trace: LiteralTrace | None = None
    leaves = expand_to_level_one(steps, 2, cells, tail)
    expected_cells = [1, 2] + [1] * cells
    if [leaf_cells for leaf_cells, _ in leaves] != expected_cells:
        raise AssertionError("level-two symbolic expansion changed")
    for leaf_cells, leaf_tail in leaves:
        trace = append_trace(trace, trace_glider(leaf_cells, leaf_tail))
    if trace is None:
        raise AssertionError("level-two macro emitted no gliders")
    return trace


def trace_unit_branch(candidate: UnitBranch, tail: int) -> LiteralTrace:
    parent_tail = (
        candidate.parent_macro_tail_base
        + candidate.parent_macro_tail_stride * tail
    )
    return trace_level_two(candidate.cells, parent_tail)


def trace_charge_branch(candidate: ChargeBranch, tail: int) -> LiteralTrace:
    hierarchy, _ = construct_hierarchy(6)
    parent = hierarchy[1]
    charge = construct_isa()
    source, target = candidate.member(tail)
    unit_source = (
        charge.packet_residue_mod_divisor
        + charge.removed_divisor * source
    )
    unit_target = (
        charge.packet_residue_mod_divisor
        + charge.removed_divisor * target
    )
    first = unit_branch(parent, candidate.cells)
    second = unit_branch(parent, 1)
    first_tail = locate_unit_tail(first, unit_source)
    _, intermediate = first.member(first_tail)
    second_tail = locate_unit_tail(second, intermediate)
    _, checked_target = second.member(second_tail)
    if checked_target != unit_target:
        raise AssertionError("charge-to-unit endpoint conversion failed")
    trace = append_trace(
        trace_unit_branch(first, first_tail),
        trace_unit_branch(second, second_tail),
    )
    if (
        trace.start != encode_charge_packet(source).collatz_state
        or trace.endpoint != encode_charge_packet(target).collatz_state
    ):
        raise AssertionError("charge branch missed its literal encoding")
    return trace


def trace_bouncer(candidate: BouncerTransition, tail: int) -> LiteralTrace:
    charge = construct_isa()
    source, target = candidate.member(tail)
    state = source
    trace: LiteralTrace | None = None
    charge_cells = [candidate.input_defect_cells] + (
        [1] * candidate.background_cells
    )
    for cells in charge_cells:
        branch = direct_branch(charge, cells)
        branch_tail = locate_charge_tail(branch, state)
        segment = trace_charge_branch(branch, branch_tail)
        trace = append_trace(trace, segment)
        state = branch.member(branch_tail)[1]
    if trace is None or state != target:
        raise AssertionError("bouncer block missed its charge endpoint")
    input_y = packet_to_y(source)
    output_y = packet_to_y(target)
    arithmetic = bouncer_step(input_y)
    reverse = reverse_bouncer_step(output_y)
    if arithmetic.output_y != output_y or reverse.input_y != input_y:
        raise AssertionError("literal trace disagrees with arithmetic bouncer")
    if replay_accelerated(trace.start, trace.word) != trace.endpoint:
        raise AssertionError("bouncer word failed independent direct replay")
    if trace.endpoint <= trace.start:
        raise AssertionError("bounded literal bouncer member is not outward")
    return trace


def replay_record(
    m: int, h: int, next_m: int, tail: int
) -> dict[str, object]:
    family = transition_family(m + 1, h - 1, next_m + 1)
    source_packet, target_packet = family.member(tail)
    source = encode_charge_packet(source_packet)
    target = encode_charge_packet(target_packet)
    trace = trace_bouncer(family, tail)
    input_y = packet_to_y(source_packet)
    output_y = packet_to_y(target_packet)
    if trace.start != source.collatz_state or trace.endpoint != target.collatz_state:
        raise AssertionError("replay record lost its canonical endpoints")
    return {
        "m": m,
        "h": h,
        "next_m": next_m,
        "tail": tail,
        "input_y_bits": input_y.bit_length(),
        "output_y_bits": output_y.bit_length(),
        "input_y_decimal_sha256": decimal_sha256(input_y),
        "output_y_decimal_sha256": decimal_sha256(output_y),
        "input_breakoff_bits": source.breakoff_state.bit_length(),
        "output_breakoff_bits": target.breakoff_state.bit_length(),
        "input_breakoff_decimal_sha256": decimal_sha256(source.breakoff_state),
        "output_breakoff_decimal_sha256": decimal_sha256(target.breakoff_state),
        "input_router_rail_length": source.router_rail_length,
        "output_router_rail_length": target.router_rail_length,
        "input_collatz_bits": trace.start.bit_length(),
        "output_collatz_bits": trace.endpoint.bit_length(),
        "input_collatz_decimal_sha256": decimal_sha256(trace.start),
        "output_collatz_decimal_sha256": decimal_sha256(trace.endpoint),
        "valuation_word_length": len(trace.word),
        "valuation_sum": sum(trace.word),
        "ordinary_collatz_duration": sum(value + 1 for value in trace.word),
        "valuation_word_sha256": word_sha256(trace.word),
        "level_one_glider_macros": trace.glider_macros,
        "literal_breakoff_macros": trace.breakoff_macros,
        "direct_accelerated_replay_checked": True,
        "literal_endpoint_checked": True,
        "literal_strict_outwardness_checked": True,
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("unit_charge_bouncer.py"),
        Path(__file__).with_name("unit_charge_discharge.py"),
        Path(__file__).with_name("breakoff_unit_slice.py"),
        Path(__file__).with_name("breakoff_renormalization.py"),
        Path(__file__).with_name("breakoff_ether_glider.py"),
        Path(__file__).with_name("breakoff_delay_gate.py"),
        Path(__file__).with_name("router_breakoff.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def build_certificate(opcode_bound: int = 3, tails: int = 2) -> dict[str, object]:
    if min(opcode_bound, tails) < 1:
        raise ValueError("semantic compiler bounds must be positive")
    slope, intercept = breakoff_affine_constants()
    # SE1 is exact for the intermediate breakoff coordinate, not for the
    # literal Collatz state after the final router decode.
    for packet in (1, 2, 3, 17, 12345):
        if encode_level_two_packet(packet).breakoff_state != slope * packet + intercept:
            raise AssertionError("level-two breakoff affine identity failed")
    replays = [
        replay_record(m, h, next_m, tail)
        for m in range(1, opcode_bound + 1)
        for h in range(1, opcode_bound + 1)
        for next_m in range(1, opcode_bound + 1)
        for tail in range(tails)
    ]
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "bounded exact descent from normalized public bouncer states to "
            "literal odd Collatz states and valuation words, independently "
            "replayed by direct accelerated arithmetic; no universal Lean "
            "compiler or infinite orbit is claimed"
        ),
        "coordinate_chain": (
            "public y -> charge packet -> unit packet -> level-two packet -> "
            "level-one glider packet -> breakoff k -> literal Collatz state"
        ),
        "symbolic_substitutions": {
            "charge_cell_N": "unit cells [N,1]",
            "level_two_cell_N": "level-one gliders [1,2]+[1]^N",
            "level_one_glider_N": "breakoff gates [E,H]+[E]^N",
            "breakoff_gate": "concatenate router literal_step valuation words",
        },
        "breakoff_affine_encoding": {
            "variable": "level-two parent packet K",
            "slope": slope,
            "intercept": intercept,
            "identity": "breakoff_k=slope*K+intercept",
            "scope_warning": (
                "breakoff_k is not the literal Collatz state; the final "
                "router rail length varies"
            ),
        },
        "bounds": {
            "m": [1, opcode_bound],
            "h": [1, opcode_bound],
            "next_m": [1, opcode_bound],
            "members_per_branch": tails,
            "branches": opcode_bound**3,
            "members": len(replays),
            "direct_literal_replays": len(replays),
            "level_one_glider_macros": sum(
                int(row["level_one_glider_macros"]) for row in replays
            ),
            "literal_breakoff_macros": sum(
                int(row["literal_breakoff_macros"]) for row in replays
            ),
            "accelerated_instructions": sum(
                int(row["valuation_word_length"]) for row in replays
            ),
        },
        "replays": replays,
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported semantic compiler schema")
    bounds = data["bounds"]
    expected = build_certificate(
        int(bounds["m"][1]), int(bounds["members_per_branch"])
    )
    if data != expected:
        raise ValueError("semantic compiler artifact failed reconstruction")


def selftest() -> None:
    slope, intercept = breakoff_affine_constants()
    for packet in (1, 2, 3, 17):
        encoded = encode_level_two_packet(packet)
        if encoded.breakoff_state != slope * packet + intercept:
            raise AssertionError("breakoff encoding selftest failed")
    for m, h, next_m in ((1, 1, 1), (1, 2, 2), (2, 1, 2)):
        trace = trace_bouncer(
            transition_family(m + 1, h - 1, next_m + 1), 0
        )
        if replay_accelerated(trace.start, trace.word) != trace.endpoint:
            raise AssertionError("semantic trace selftest failed")


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(500_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--opcode-bound", type=int, default=3)
    build.add_argument("--tails", type=int, default=2)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()
    if args.command == "selftest":
        selftest()
        print("unit charge semantic compiler selftest: PASS")
    elif args.command == "build":
        data = build_certificate(args.opcode_bound, args.tails)
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit charge semantic compiler artifact: PASS")


if __name__ == "__main__":
    main()
