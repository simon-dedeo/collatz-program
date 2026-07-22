#!/usr/bin/env python3
"""Exact canonical-address audit of three aperiodic charge-bouncer clocks.

The fixed-form bouncer transition is coded by an opcode pair ``(m,h)``:
one defect of length ``m+1`` followed by ``h-1`` background cells.  This
worker maps the symbols 0 and 1 injectively to pairs in ``{1,...,4}^2`` and
reads three standard aperiodic binary words:

* Thue--Morse;
* period doubling;
* the Fibonacci substitution fixed word, ``0 -> 01, 1 -> 0``.

For every coding and every prefix through 48 transitions it compiles the
complete charge-macro word, links its endpoint to the next defect opcode,
and computes the least positive fixed-form state ``y``.  An ordinary infinite
realization would require these canonical addresses eventually to stabilize.

The audit is deliberately a low-description program search, not a seed range
or a theorem about arbitrary morphic/aperiodic schedules.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from functools import cache
from pathlib import Path

from breakoff_delay_gate import v2
from breakoff_superether import AffineMacro, link_macros
from unit_charge_bouncer import F, TWO_26, as_macro, compose
from unit_charge_discharge import construct_isa, direct_branch


SCHEMA = "collatz-unit-charge-morphic-v1"


@cache
def charge_isa():
    return construct_isa()


@dataclass(frozen=True)
class ClosestEvent:
    sequence: str
    zero_opcode: tuple[int, int]
    one_opcode: tuple[int, int]
    prefix_depth: int
    shared_low_bits: int
    previous_address_bits: int
    current_address_bits: int


def words(length: int) -> dict[str, list[int]]:
    if length < 2:
        raise ValueError("morphic audit needs at least two symbols")
    thue = [index.bit_count() & 1 for index in range(length)]
    period = [v2(index + 1) & 1 for index in range(length)]
    fibonacci = "0"
    while len(fibonacci) < length:
        fibonacci = "".join("01" if symbol == "0" else "0" for symbol in fibonacci)
    return {
        "thue_morse": thue,
        "period_doubling": period,
        "fibonacci": [int(symbol) for symbol in fibonacci[:length]],
    }


def opcode_blocks(bound: int) -> tuple[dict[tuple[int, int], AffineMacro], dict[int, AffineMacro]]:
    if bound < 1:
        raise ValueError("opcode bound must be positive")
    isa = charge_isa()
    branches = {
        cells: as_macro(direct_branch(isa, cells))
        for cells in range(1, bound + 2)
    }
    blocks: dict[tuple[int, int], AffineMacro] = {}
    for m in range(1, bound + 1):
        for h in range(1, bound + 1):
            block = branches[m + 1]
            for _ in range(h - 1):
                block = compose(block, branches[1])
            blocks[m, h] = block
    return blocks, branches


def canonical_y(executed: AffineMacro, next_m: int, branches: dict[int, AffineMacro]) -> int:
    isa = charge_isa()
    following = branches[next_m + 1]
    source_tail, _ = link_macros(executed, following)
    packet = (
        executed.input_packet_base
        + (1 << executed.input_packet_stride_exponent) * source_tail
    )
    numerator = F * (
        isa.register_offset + isa.register_stride * packet
    ) - TWO_26
    if numerator % TWO_26:
        raise AssertionError("canonical morphic address missed defect phase")
    result = numerator // TWO_26
    if result <= 0:
        raise AssertionError("canonical morphic address is not positive")
    return result


def event_key(event: ClosestEvent | None) -> tuple[int, int, int]:
    if event is None:
        return (-1, -1, -1)
    return (
        event.shared_low_bits,
        event.prefix_depth,
        -event.current_address_bits,
    )


def audit(opcode_bound: int = 4, prefix_depth: int = 48) -> dict[str, object]:
    if prefix_depth < 2:
        raise ValueError("morphic prefix depth must be at least two")
    blocks, branches = opcode_blocks(opcode_bound)
    opcodes = sorted(blocks)
    sequence_rows = words(prefix_depth + 1)
    prefixes = 0
    stabilizations = 0
    best: ClosestEvent | None = None
    maximum_address_bits = 0
    for name, sequence in sequence_rows.items():
        for zero in opcodes:
            for one in opcodes:
                if one == zero:
                    continue
                coding = (zero, one)
                executed: AffineMacro | None = None
                previous: int | None = None
                for depth in range(1, prefix_depth + 1):
                    block = blocks[coding[sequence[depth - 1]]]
                    executed = block if executed is None else compose(executed, block)
                    current = canonical_y(
                        executed, coding[sequence[depth]][0], branches
                    )
                    prefixes += 1
                    maximum_address_bits = max(maximum_address_bits, current.bit_length())
                    if previous is not None:
                        if current == previous:
                            stabilizations += 1
                        else:
                            shared = v2(current - previous)
                            event = ClosestEvent(
                                sequence=name,
                                zero_opcode=zero,
                                one_opcode=one,
                                prefix_depth=depth,
                                shared_low_bits=shared,
                                previous_address_bits=previous.bit_length(),
                                current_address_bits=current.bit_length(),
                            )
                            if event_key(event) > event_key(best):
                                best = event
                    previous = current
    best_row = asdict(best) if best else None
    if best_row is not None:
        best_row["zero_opcode"] = list(best.zero_opcode)
        best_row["one_opcode"] = list(best.one_opcode)
    return {
        "schema": SCHEMA,
        "claim_scope": (
            "exact canonical-address audit of three named aperiodic binary "
            "clocks, all two-symbol codings by bounded (m,h) opcodes, and "
            "finite prefix depth; not a seed range or an all-morphic theorem"
        ),
        "bounds": {
            "opcode_m_min": 1,
            "opcode_m_max": opcode_bound,
            "opcode_h_min": 1,
            "opcode_h_max": opcode_bound,
            "opcodes": len(opcodes),
            "ordered_injective_two_symbol_codings": (
                len(opcodes) * (len(opcodes) - 1)
            ),
            "sequences": sorted(sequence_rows),
            "prefix_depth": prefix_depth,
            "compiled_prefixes": prefixes,
        },
        "canonical_address_stabilizations": stabilizations,
        "closest_nonstabilizing_event": best_row,
        "maximum_canonical_address_bits": maximum_address_bits,
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("unit_charge_bouncer.py"),
        Path(__file__).with_name("unit_charge_discharge.py"),
        Path(__file__).with_name("breakoff_unit_slice.py"),
        Path(__file__).with_name("breakoff_renormalization.py"),
        Path(__file__).with_name("breakoff_superether.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def build_certificate(opcode_bound: int = 4, prefix_depth: int = 48) -> dict[str, object]:
    result = audit(opcode_bound, prefix_depth)
    result["verifier_sha256"] = source_sha256()
    return result


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported charge morphic schema")
    bounds = data["bounds"]
    expected = build_certificate(
        int(bounds["opcode_m_max"]), int(bounds["prefix_depth"])
    )
    if data != expected:
        raise ValueError("charge morphic artifact failed reconstruction")


def selftest() -> None:
    sample = words(10)
    assert sample["thue_morse"][:8] == [0, 1, 1, 0, 1, 0, 0, 1]
    assert sample["period_doubling"][:8] == [0, 1, 0, 0, 0, 1, 0, 1]
    assert sample["fibonacci"][:8] == [0, 1, 0, 0, 1, 0, 1, 0]
    tiny = audit(2, 4)
    assert tiny["bounds"]["compiled_prefixes"] == 3 * 12 * 4


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(500_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--opcode-bound", type=int, default=4)
    build.add_argument("--prefix-depth", type=int, default=48)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("unit charge morphic selftest: PASS")
    elif args.command == "build":
        data = build_certificate(args.opcode_bound, args.prefix_depth)
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit charge morphic artifact: PASS")


if __name__ == "__main__":
    main()
