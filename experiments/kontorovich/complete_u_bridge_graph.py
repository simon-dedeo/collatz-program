#!/usr/bin/env python3
"""Exact bounded saturated-map bridge graph for the complete splash ISA.

This search works over *gate shapes*, not ordinary seed intervals.  A source
splash with ``N`` accelerated odd steps can compile ``U^N`` only when the
target prefix deletes exactly ``N`` address bits.  That condition makes the
target-shape list finite for each source.  Every surviving edge is checked
coefficientwise on its complete affine cylinder.

The artifact also asks whether an outward target is itself the source of a
second saturated bridge.  A negative answer is scoped to the source-shape box
used for the first edge; the second-edge target list is complete once that
first target is fixed.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterator

from complete_splash_isa import (
    CompleteSplashGate,
    affine_saturated_block,
    decode_payload,
    even_cleanup_gate,
    link_instruction,
    odd_gap_catcher,
    ordinary_continuation,
    universally_outward,
    verify_member,
)


SCHEMA = "collatz-complete-u-bridge-graph-v1"


@dataclass(frozen=True)
class Shape:
    branch: str
    amp_ticks: int
    clean_ticks: int
    to_plus_extra: int
    terminal_extra: int | None
    output_gap: int

    @classmethod
    def of(cls, gate: CompleteSplashGate) -> "Shape":
        return cls(
            branch=gate.branch,
            amp_ticks=gate.amp_ticks,
            clean_ticks=gate.clean_ticks,
            to_plus_extra=gate.to_plus_extra,
            terminal_extra=gate.terminal_extra,
            output_gap=gate.output_gap,
        )

    def build(self) -> CompleteSplashGate:
        if self.branch == "odd_catcher":
            if self.terminal_extra is not None:
                raise ValueError("odd catcher cannot have a terminal extra")
            return odd_gap_catcher(
                self.amp_ticks,
                self.clean_ticks,
                self.to_plus_extra,
                self.output_gap,
            )
        if self.branch == "even_cleanup":
            if self.terminal_extra is None:
                raise ValueError("even cleanup requires a terminal extra")
            return even_cleanup_gate(
                self.amp_ticks,
                self.clean_ticks,
                self.to_plus_extra,
                self.terminal_extra,
                self.output_gap,
            )
        raise ValueError("unknown splash branch")


BOUNDS = {
    "source_amp_ticks": "0..15",
    "source_clean_ticks": "0..4",
    "source_to_plus_extra": "1..4",
    "source_even_terminal_extra": "1..4",
    "source_output_gap": "1..16",
    "source_branches": ["odd_catcher", "even_cleanup"],
    "target_shapes": (
        "all positive-parameter shapes with target input gap equal to the "
        "source output gap and target prefix address length equal to the "
        "source odd-step count"
    ),
}


def source_shapes() -> Iterator[CompleteSplashGate]:
    for r in range(16):
        for s in range(5):
            for a in range(1, 5):
                for output_gap in range(1, 17):
                    yield odd_gap_catcher(r, s, a, output_gap)
                for b in range(1, 5):
                    for output_gap in range(1, 17):
                        yield even_cleanup_gate(r, s, a, b, output_gap)


def compatible_targets(source: CompleteSplashGate) -> list[CompleteSplashGate]:
    """Enumerate the complete coefficient-compatible target-shape list."""
    address_bits = source.amp_ticks + source.clean_ticks + 2
    target_r = source.output_gap - 1
    target_code_exponent = address_bits + 1
    targets: list[CompleteSplashGate] = []
    for s in range(target_code_exponent // 2 + 1):
        for a in range(1, target_code_exponent + 1):
            for output_gap in range(1, target_code_exponent + 1):
                odd_exponent = a + 2 * s + output_gap + 2
                if odd_exponent == target_code_exponent:
                    targets.append(
                        odd_gap_catcher(target_r, s, a, output_gap)
                    )
                for b in range(1, target_code_exponent + 1):
                    even_exponent = a + b + 2 * s + output_gap + 3
                    if even_exponent == target_code_exponent:
                        targets.append(
                            even_cleanup_gate(
                                target_r, s, a, b, output_gap
                            )
                        )
    return targets


def bridge_record(
    source: CompleteSplashGate, target: CompleteSplashGate
) -> dict[str, object] | None:
    address_bits = source.amp_ticks + source.clean_ticks + 2
    link = link_instruction(source, target)
    if link.address_bits != address_bits:
        raise AssertionError("target address length is not the source write length")
    source_index, target_index = link.indices(0)
    u_base, u_stride, digits = affine_saturated_block(
        source_index, 1 << address_bits, address_bits
    )
    if u_stride != pow(3, address_bits):
        raise AssertionError("saturated cylinder slope changed")
    if u_base != target_index:
        return None
    source_outward = universally_outward(
        source, source_index, 1 << address_bits
    )
    target_outward = universally_outward(
        target, target_index, pow(3, address_bits)
    )
    return {
        "source_shape": asdict(Shape.of(source)),
        "target_shape": asdict(Shape.of(target)),
        "address_bits": address_bits,
        "source_index_base": source_index,
        "source_index_stride": 1 << address_bits,
        "target_index_base": target_index,
        "target_index_stride": pow(3, address_bits),
        "U_digits": digits,
        "source_selected_family_universally_outward": source_outward,
        "target_selected_family_universally_outward": target_outward,
    }


def find_first_edges() -> tuple[dict[str, int], list[dict[str, object]]]:
    counts = {
        "source_shapes": 0,
        "outward_source_shapes": 0,
        "candidate_links_checked": 0,
    }
    hits: list[dict[str, object]] = []
    for source in source_shapes():
        counts["source_shapes"] += 1
        if not universally_outward(source, 0, 1):
            continue
        counts["outward_source_shapes"] += 1
        for target in compatible_targets(source):
            counts["candidate_links_checked"] += 1
            record = bridge_record(source, target)
            if record is not None:
                if not record["source_selected_family_universally_outward"]:
                    raise AssertionError(
                        "globally outward source lost outwardness on its bridge"
                    )
                hits.append(record)
    return counts, hits


def audit_second_edges(
    hits: list[dict[str, object]],
) -> dict[str, object]:
    outward_targets = [
        hit
        for hit in hits
        if hit["target_selected_family_universally_outward"]
    ]
    unique_targets: dict[Shape, CompleteSplashGate] = {}
    for hit in outward_targets:
        shape = Shape(**hit["target_shape"])
        unique_targets[shape] = shape.build()

    checked = 0
    continuations: list[dict[str, object]] = []
    for source_shape, source in unique_targets.items():
        for target in compatible_targets(source):
            checked += 1
            record = bridge_record(source, target)
            if record is not None:
                continuations.append(
                    {
                        "source_shape": asdict(source_shape),
                        "edge": record,
                    }
                )
    return {
        "outward_first_edges": len(outward_targets),
        "distinct_outward_first_targets": len(unique_targets),
        "complete_second_edge_candidates_checked": checked,
        "renewing_second_edges": len(continuations),
        "continuations": continuations,
    }


def three_gate_u12_cascade() -> dict[str, object]:
    """Certify an unbounded three-gate outward subcylinder of the U^12 edge."""
    source = even_cleanup_gate(10, 0, 4, 2, 11)
    target = even_cleanup_gate(10, 2, 1, 3, 2)
    catcher = odd_gap_catcher(1, 0, 1, 2)
    source_indices: list[int] = []
    target_indices: list[int] = []
    catcher_indices: list[int] = []
    state_rows: list[list[int]] = []

    for u in (0, 1):
        saturated_tail = 16 * u
        source_index = 1023 + 4096 * saturated_tail
        target_index = 132860 + 531441 * saturated_tail
        source_start, source_endpoint = verify_member(source, source_index)
        target_start, target_endpoint = verify_member(target, target_index)
        if source_endpoint != target_start:
            raise AssertionError("U^12 source and target gates do not link")

        target_output_payload = target.payloads(target_index)[2]
        decoded = decode_payload(1, target_output_payload)
        if decoded is None or Shape.of(decoded[0]) != Shape.of(catcher):
            raise AssertionError("U^12 tail subcylinder missed its catcher")
        decoded_catcher, catcher_index = decoded
        catcher_start, catcher_endpoint = verify_member(
            decoded_catcher, catcher_index
        )
        if target_endpoint != catcher_start:
            raise AssertionError("U^12 target and catcher do not link")
        if not source_start < source_endpoint < target_endpoint < catcher_endpoint:
            raise AssertionError("U^12 three-gate cascade is not outward")

        source_indices.append(source_index)
        target_indices.append(target_index)
        catcher_indices.append(catcher_index)
        state_rows.append(
            [source_start, source_endpoint, target_endpoint, catcher_endpoint]
        )

    expected = {
        "source_index": [1023, 65536],
        "target_index": [132860, 8503056],
        "catcher_index": [39716626454, pow(3, 26)],
    }
    actual = {
        "source_index": [source_indices[0], source_indices[1] - source_indices[0]],
        "target_index": [target_indices[0], target_indices[1] - target_indices[0]],
        "catcher_index": [
            catcher_indices[0],
            catcher_indices[1] - catcher_indices[0],
        ],
    }
    if actual != expected:
        raise AssertionError("U^12 three-gate affine indices changed")

    state_affine = {
        name: {
            "base": state_rows[0][index],
            "stride": state_rows[1][index] - state_rows[0][index],
        }
        for index, name in enumerate(
            ["source_start", "after_source", "after_target", "after_catcher"]
        )
    }
    strides = [state_affine[name]["stride"] for name in state_affine]
    bases = [state_affine[name]["base"] for name in state_affine]
    if not all(left < right for left, right in zip(bases, bases[1:])):
        raise AssertionError("U^12 cascade base is not strictly outward")
    if not all(left <= right for left, right in zip(strides, strides[1:])):
        raise AssertionError("U^12 cascade slopes do not preserve outwardness")

    return {
        "scope": (
            "universal three-gate outward affine family; finite prefix only"
        ),
        "saturated_tail": "t=16*u",
        "source_shape": asdict(Shape.of(source)),
        "target_shape": asdict(Shape.of(target)),
        "catcher_shape": asdict(Shape.of(catcher)),
        "source_index": "1023+65536*u",
        "target_index": "132860+8503056*u",
        "catcher_index": f"39716626454+{pow(3, 26)}*u",
        "state_affine_formulas": state_affine,
        "all_three_gates_universally_outward": True,
        "canonical_u0_continuation": ordinary_continuation(bases[0]),
    }


def build_certificate() -> dict[str, object]:
    counts, hits = find_first_edges()
    if counts != {
        "source_shapes": 25_600,
        "outward_source_shapes": 11_312,
        "candidate_links_checked": 2_751_680,
    }:
        raise AssertionError("complete U-bridge search counts changed")
    if len(hits) != 18:
        raise AssertionError("complete U-bridge hit count changed")
    if sum(
        bool(hit["target_selected_family_universally_outward"])
        for hit in hits
    ) != 11:
        raise AssertionError("two-outward-edge count changed")

    second_edges = audit_second_edges(hits)
    if second_edges["renewing_second_edges"] != 0:
        raise AssertionError("bounded bridge graph unexpectedly renewed")

    branch_counts = {
        "odd_catcher_sources": sum(
            hit["source_shape"]["branch"] == "odd_catcher" for hit in hits
        ),
        "even_cleanup_sources": sum(
            hit["source_shape"]["branch"] == "even_cleanup" for hit in hits
        ),
    }
    if branch_counts != {"odd_catcher_sources": 14, "even_cleanup_sources": 4}:
        raise AssertionError("bridge source-branch counts changed")

    return {
        "schema": SCHEMA,
        "claim_scope": (
            "exact exhaustive source-shape search within stated bounds, with "
            "complete coefficient-compatible target lists and complete "
            "one-step renewal audits for every outward hit target; not a seed "
            "range search or an all-shape exclusion"
        ),
        "bounds": BOUNDS,
        "counts": counts
        | {
            "exact_saturated_bridges": len(hits),
            "source_branch_hits": branch_counts,
        },
        "hits": hits,
        "renewal_audit": second_edges,
        "three_gate_U12_cascade": three_gate_u12_cascade(),
    }


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported artifact schema")
    if data != build_certificate():
        raise ValueError("complete U-bridge graph artifact failed reconstruction")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        build_certificate()
        print("complete_u_bridge_graph selftest: PASS")
    elif args.command == "build":
        args.output.write_text(json.dumps(build_certificate(), indent=2) + "\n")
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("complete_u_bridge_graph artifact: PASS")


if __name__ == "__main__":
    main()
