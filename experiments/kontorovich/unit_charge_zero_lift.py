#!/usr/bin/env python3
"""Exact bounded audit of zero extension lifts in the charge bouncer.

For an affine compiled prefix

    K=R+2^P*t -> K'=S+3^Q*t,

linking one more block normally restricts the original tail to

    t=rho+2^E*u.

The decisive ``rho=0`` case occurs exactly when the canonical output ``S``
is already a member of the next block's input progression.  Then the same
least ordinary address executes one more block and the canonical address
stabilizes for that extension.

This worker exhausts every word of bounded depth over bounded bouncer opcodes
``(m,h)`` and tests every bounded next block.  It is a finite grammar audit,
not an all-depth positive-lift theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

from breakoff_delay_gate import v2
from breakoff_superether import AffineMacro
from unit_charge_bouncer import as_macro, compose
from unit_charge_discharge import construct_isa, direct_branch


SCHEMA = "collatz-unit-charge-zero-lift-v1"


@dataclass(frozen=True)
class DyadicNearMiss:
    prefix_word: tuple[tuple[int, int], ...]
    next_opcode: tuple[int, int]
    shared_low_bits: int
    required_input_bits: int
    terminal_public_valuation: int


def opcode_blocks(bound: int) -> dict[tuple[int, int], AffineMacro]:
    if bound < 1:
        raise ValueError("zero-lift opcode bound must be positive")
    isa = construct_isa()
    branches = {
        cells: as_macro(direct_branch(isa, cells))
        for cells in range(1, bound + 2)
    }
    blocks = {}
    for m in range(1, bound + 1):
        for h in range(1, bound + 1):
            block = branches[m + 1]
            for _ in range(h - 1):
                block = compose(block, branches[1])
            blocks[m, h] = block
    return blocks


def near_key(event: DyadicNearMiss | None) -> tuple[int, int, int]:
    if event is None:
        return (-1, -1, -1)
    return (
        event.shared_low_bits,
        len(event.prefix_word),
        -event.required_input_bits,
    )


def audit(opcode_bound: int = 4, word_depth: int = 4) -> dict[str, object]:
    if word_depth < 1:
        raise ValueError("zero-lift word depth must be positive")
    isa = construct_isa()
    blocks = opcode_blocks(opcode_bound)
    ordered = sorted(blocks.items())
    zero_lifts = []
    best: DyadicNearMiss | None = None
    prefixes_by_depth = []
    extension_tests_by_depth = []
    maximum_terminal_valuation_by_depth = []
    frontier: list[tuple[tuple[tuple[int, int], ...], AffineMacro | None]] = [
        ((), None)
    ]
    for depth in range(1, word_depth + 1):
        following_frontier = []
        depth_tests = 0
        maximum_valuation = 0
        for word, current in frontier:
            for opcode, block in ordered:
                compiled = block if current is None else compose(current, block)
                next_word = word + (opcode,)
                terminal_packet = compiled.output_packet_base
                terminal_register = (
                    isa.register_offset + isa.register_stride * terminal_packet
                )
                terminal_valuation = v2(terminal_register)
                maximum_valuation = max(maximum_valuation, terminal_valuation)
                for next_opcode, next_block in ordered:
                    difference = terminal_packet - next_block.input_packet_base
                    required = next_block.input_packet_stride_exponent
                    depth_tests += 1
                    if difference >= 0 and difference % (1 << required) == 0:
                        zero_lifts.append(
                            {
                                "prefix_word": [list(pair) for pair in next_word],
                                "next_opcode": list(next_opcode),
                                "terminal_public_valuation": terminal_valuation,
                                "next_input_tail": difference >> required,
                            }
                        )
                    elif difference != 0:
                        shared = v2(abs(difference))
                        event = DyadicNearMiss(
                            prefix_word=next_word,
                            next_opcode=next_opcode,
                            shared_low_bits=shared,
                            required_input_bits=required,
                            terminal_public_valuation=terminal_valuation,
                        )
                        if near_key(event) > near_key(best):
                            best = event
                following_frontier.append((next_word, compiled))
        prefixes_by_depth.append(len(following_frontier))
        extension_tests_by_depth.append(depth_tests)
        maximum_terminal_valuation_by_depth.append(maximum_valuation)
        frontier = following_frontier

    best_row = asdict(best) if best else None
    if best_row is not None:
        best_row["prefix_word"] = [list(pair) for pair in best.prefix_word]
        best_row["next_opcode"] = list(best.next_opcode)
    return {
        "schema": SCHEMA,
        "claim_scope": (
            "exact exhaustive zero-extension test for all bouncer words and "
            "next blocks inside stated opcode/depth bounds; not an all-depth "
            "positive-lift theorem"
        ),
        "bounds": {
            "opcode_m_min": 1,
            "opcode_m_max": opcode_bound,
            "opcode_h_min": 1,
            "opcode_h_max": opcode_bound,
            "opcodes": len(blocks),
            "word_depth": word_depth,
            "prefixes_by_depth": prefixes_by_depth,
            "extension_tests_by_depth": extension_tests_by_depth,
            "total_prefixes": sum(prefixes_by_depth),
            "total_extension_tests": sum(extension_tests_by_depth),
        },
        "zero_extension_lifts": zero_lifts,
        "zero_extension_lift_count": len(zero_lifts),
        "closest_dyadic_nonlift": best_row,
        "maximum_terminal_public_valuation_by_depth": (
            maximum_terminal_valuation_by_depth
        ),
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


def build_certificate(opcode_bound: int = 4, word_depth: int = 4) -> dict[str, object]:
    result = audit(opcode_bound, word_depth)
    result["verifier_sha256"] = source_sha256()
    return result


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported charge zero-lift schema")
    bounds = data["bounds"]
    expected = build_certificate(
        int(bounds["opcode_m_max"]), int(bounds["word_depth"])
    )
    if data != expected:
        raise ValueError("charge zero-lift artifact failed reconstruction")


def selftest() -> None:
    tiny = audit(2, 2)
    assert tiny["bounds"]["prefixes_by_depth"] == [4, 16]
    assert tiny["bounds"]["extension_tests_by_depth"] == [16, 64]


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(500_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--opcode-bound", type=int, default=4)
    build.add_argument("--word-depth", type=int, default=4)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("unit charge zero-lift selftest: PASS")
    elif args.command == "build":
        data = build_certificate(args.opcode_bound, args.word_depth)
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit charge zero-lift artifact: PASS")


if __name__ == "__main__":
    main()
