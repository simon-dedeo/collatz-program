#!/usr/bin/env python3
"""Exact low-carry lifts of a failed outward first-passage prefix.

The record source 270271 completes 36 canonical outward first-passage blocks.
At its last boundary the accumulated parity length is 124, and its literal
zero-carry continuation reaches the terminal Collatz cycle without a 37th
block.  Every ordinary source preserving those 36 blocks is therefore

    x_ell = 270271 + 2^124 * ell,    ell >= 0.

This worker searches the smallest positive carries ``ell``.  It is not a
generic seed sweep: every candidate is in the exact next cylinder above one
machine-certified prefix.  Every candidate is followed all the way to the
1--2 cycle, and finite block records are reported honestly as finite.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import multiprocessing as mp
from collections import Counter
from pathlib import Path
from typing import Any, Sequence

try:
    from .outward_first_passage import (
        accelerated_odd_step,
        canonical_json,
        source_profile,
    )
except ImportError:
    from outward_first_passage import (
        accelerated_odd_step,
        canonical_json,
        source_profile,
    )


SCHEMA = "collatz-outward-carry-lift-v1"
BASE_SOURCE = 270_271
BASE_BLOCKS = 36
BASE_LENGTH = 124


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def candidate_source(carry: int) -> int:
    if carry < 0:
        raise ValueError("carry must be nonnegative")
    return BASE_SOURCE + 2**BASE_LENGTH * carry


def scan_chunk(arguments: tuple[int, int, int]) -> dict[str, Any]:
    lower, upper, maximum_shortcut_steps = arguments
    local_record = -1
    record_rows: list[dict[str, int]] = []
    champion_rows: list[dict[str, int]] = []
    histogram: Counter[int] = Counter()
    maximum_steps = 0
    for carry in range(lower, upper):
        profile = source_profile(candidate_source(carry), maximum_shortcut_steps)
        blocks = int(profile["first_passage_blocks"])
        if blocks < BASE_BLOCKS:
            raise AssertionError("a cylinder lift lost the certified base prefix")
        histogram[blocks] += 1
        maximum_steps = max(
            maximum_steps, int(profile["shortcut_steps_to_terminal_cycle"])
        )
        row = {
            "carry": carry,
            "first_passage_blocks": blocks,
            "shortcut_steps_to_terminal_cycle": int(
                profile["shortcut_steps_to_terminal_cycle"]
            ),
            "accelerated_steps_to_terminal_cycle": int(
                profile["accelerated_steps_to_terminal_cycle"]
            ),
        }
        if blocks > local_record:
            record_rows.append(row)
            champion_rows = [row]
            local_record = blocks
        elif blocks == local_record:
            champion_rows.append(row)
    return {
        "record_rows": record_rows,
        "champion_rows": champion_rows,
        "histogram": dict(histogram),
        "maximum_shortcut_steps_observed": maximum_steps,
    }


def exact_scan(
    maximum_carry: int,
    maximum_shortcut_steps: int,
    processes: int = 1,
    chunk_size: int = 500,
) -> dict[str, Any]:
    if maximum_carry < 1:
        raise ValueError("maximum carry must be positive")
    if maximum_shortcut_steps < 1:
        raise ValueError("shortcut step limit must be positive")
    if processes < 1 or chunk_size < 1:
        raise ValueError("process and chunk counts must be positive")

    chunks = [
        (lower, min(lower + chunk_size, maximum_carry + 1), maximum_shortcut_steps)
        for lower in range(1, maximum_carry + 1, chunk_size)
    ]
    if processes == 1:
        pieces = [scan_chunk(chunk) for chunk in chunks]
    else:
        with mp.Pool(processes) as pool:
            pieces = pool.map(scan_chunk, chunks)

    candidates = sorted(
        (
            row
            for piece in pieces
            for row in piece["record_rows"]
        ),
        key=lambda row: int(row["carry"]),
    )
    record_rows: list[dict[str, Any]] = []
    record_depth = BASE_BLOCKS
    for row in candidates:
        blocks = int(row["first_passage_blocks"])
        if blocks <= record_depth:
            continue
        carry = int(row["carry"])
        record_rows.append(
            {
                **row,
                "source": str(candidate_source(carry)),
                "additional_blocks_after_base_prefix": blocks - BASE_BLOCKS,
            }
        )
        record_depth = blocks

    histogram: Counter[int] = Counter()
    maximum_steps_observed = 0
    for piece in pieces:
        histogram.update(
            {int(depth): int(count) for depth, count in piece["histogram"].items()}
        )
        maximum_steps_observed = max(
            maximum_steps_observed,
            int(piece["maximum_shortcut_steps_observed"]),
        )
    if sum(histogram.values()) != maximum_carry:
        raise AssertionError("carry scan did not cover its advertised range")

    champion = record_rows[-1]
    champion_ties = sorted(
        (
            {
                **row,
                "source": str(candidate_source(int(row["carry"]))),
                "additional_blocks_after_base_prefix": (
                    int(row["first_passage_blocks"]) - BASE_BLOCKS
                ),
            }
            for piece in pieces
            for row in piece["champion_rows"]
            if int(row["first_passage_blocks"]) == record_depth
        ),
        key=lambda row: int(row["carry"]),
    )
    if not champion_ties or int(champion_ties[0]["carry"]) != int(
        champion["carry"]
    ):
        raise AssertionError("global carry champion tie reconstruction failed")
    champion_carry = int(champion["carry"])
    champion_source = candidate_source(champion_carry)
    base = source_profile(BASE_SOURCE, maximum_shortcut_steps, True)
    lifted = source_profile(champion_source, maximum_shortcut_steps, True)
    base_words = [str(row["word"]) for row in base["boundaries"]]
    lifted_words = [str(row["word"]) for row in lifted["boundaries"]]
    if len(base_words) != BASE_BLOCKS or lifted_words[:BASE_BLOCKS] != base_words:
        raise AssertionError("champion does not preserve the literal base prefix")
    if int(base["boundaries"][-1]["shortcut_steps"]) != BASE_LENGTH:
        raise AssertionError("base prefix length changed")

    post_base_odd = [
        row
        for row in lifted["boundaries"]
        if int(row["block_depth"]) > BASE_BLOCKS and int(row["state"]) % 2 == 1
    ]
    visualizer: dict[str, Any] | None = None
    post_address_visualizer: dict[str, Any] | None = None
    if post_base_odd:
        visual = post_base_odd[-1]
        replay = champion_source
        for _ in range(int(visual["accelerated_steps"])):
            replay = accelerated_odd_step(replay)
        if replay != int(visual["state"]):
            raise AssertionError("carry-lift visualizer prefix failed replay")
        visualizer = {
            "collatz_source": str(champion_source),
            "collatz_target": str(visual["state"]),
            "accelerated_steps": int(visual["accelerated_steps"]),
            "first_passage_blocks": int(visual["block_depth"]),
            "scope": (
                "exact finite prefix of the best low-carry lift; its complete "
                "ordinary orbit reaches the 1--2 cycle"
            ),
        }
        stabilization = lifted["address_stabilization"]
        if stabilization is None:
            raise AssertionError("carry-lift champion never stabilized its address")
        post_address_start = stabilization
        if int(post_address_start["state"]) % 2 == 0:
            post_address_start = next(
                row
                for row in lifted["boundaries"]
                if int(row["block_depth"]) > int(stabilization["block_depth"])
                and int(row["state"]) % 2 == 1
            )
        post_address_accelerated_steps = int(visual["accelerated_steps"]) - int(
            post_address_start["accelerated_steps"]
        )
        replay = int(post_address_start["state"])
        for _ in range(post_address_accelerated_steps):
            replay = accelerated_odd_step(replay)
        if replay != int(visual["state"]):
            raise AssertionError("post-address carry-lift prefix failed replay")
        post_address_visualizer = {
            "collatz_source": str(post_address_start["state"]),
            "collatz_target": str(visual["state"]),
            "accelerated_steps": post_address_accelerated_steps,
            "first_passage_extensions": int(visual["block_depth"])
            - int(post_address_start["block_depth"]),
            "scope": (
                "exact finite prefix beginning only after the lifted source "
                "address stabilizes; the complete ordinary orbit reaches 1"
            ),
        }

    return {
        "meaning": (
            "directed exact search of the least positive dyadic carries above "
            "the failed 36-block canonical prefix of source 270271"
        ),
        "base_prefix": {
            "source": BASE_SOURCE,
            "first_passage_blocks": BASE_BLOCKS,
            "cumulative_shortcut_length": BASE_LENGTH,
            "lift_formula": "source=270271+2^124*carry",
            "zero_carry_reaches_terminal_cycle": True,
        },
        "maximum_carry": maximum_carry,
        "maximum_shortcut_steps_per_candidate": maximum_shortcut_steps,
        "all_candidates_reached_terminal_cycle": True,
        "maximum_shortcut_steps_observed": maximum_steps_observed,
        "block_count_histogram": {
            str(depth): count for depth, count in sorted(histogram.items())
        },
        "record_rows": record_rows,
        "champion_ties": champion_ties,
        "champion": {
            **champion,
            "address_stabilization": lifted["address_stabilization"],
            "post_address_first_passage_extensions": int(
                lifted["post_address_first_passage_extensions"]
            ),
        },
        "visualizer_prefix": visualizer,
        "visualizer_post_address_prefix": post_address_visualizer,
        "claim_scope": (
            "exhaustive only for the displayed carry interval above one fixed "
            "prefix; finite records are not an infinite orbit"
        ),
        "counterexample": None,
    }


def build_artifact(
    maximum_carry: int,
    maximum_shortcut_steps: int,
    processes: int,
    chunk_size: int,
) -> dict[str, Any]:
    data = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "audit": exact_scan(
            maximum_carry,
            maximum_shortcut_steps,
            processes,
            chunk_size,
        ),
    }
    data["artifact_sha256"] = hashlib.sha256(canonical_json(data)).hexdigest()
    return data


def verify_artifact(path: Path, processes: int, chunk_size: int) -> dict[str, Any]:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unexpected outward carry-lift schema")
    if expected.get("worker_sha256") != source_sha256():
        raise ValueError("worker hash mismatch")
    payload = dict(expected)
    advertised = payload.pop("artifact_sha256")
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("artifact self-hash mismatch")
    audit = expected["audit"]
    actual = build_artifact(
        int(audit["maximum_carry"]),
        int(audit["maximum_shortcut_steps_per_candidate"]),
        processes,
        chunk_size,
    )
    if actual != expected:
        raise AssertionError("artifact differs from exact recomputation")
    if audit["counterexample"] is not None:
        raise AssertionError("carry-lift artifact claims a counterexample")
    return {
        "artifact_sha256": advertised,
        "worker_sha256": expected["worker_sha256"],
        "maximum_carry": audit["maximum_carry"],
        "champion_carry": audit["champion"]["carry"],
        "champion_blocks": audit["champion"]["first_passage_blocks"],
        "counterexample": None,
    }


def selftest() -> None:
    result = exact_scan(1_000, 100_000, 1, 100)
    champion = result["champion"]
    if int(champion["carry"]) != 194:
        raise AssertionError("tiny carry-lift champion changed")
    if int(champion["first_passage_blocks"]) != 61:
        raise AssertionError("tiny carry-lift block record changed")
    if int(result["block_count_histogram"]["61"]) != 2:
        raise AssertionError("tiny carry-lift histogram changed")
    if len(result["champion_ties"]) != 2:
        raise AssertionError("tiny carry-lift champion ties changed")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--processes", type=int, default=1)
    parser.add_argument("--chunk-size", type=int, default=500)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--maximum-carry", type=int, default=100_000)
    build.add_argument("--maximum-shortcut-steps", type=int, default=100_000)
    probe = subparsers.add_parser("probe")
    probe.add_argument("--maximum-carry", type=int, default=1_000_000)
    probe.add_argument("--maximum-shortcut-steps", type=int, default=100_000)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print("outward carry-lift selftest: PASS")
        return 0
    if args.command == "build":
        artifact = build_artifact(
            args.maximum_carry,
            args.maximum_shortcut_steps,
            args.processes,
            args.chunk_size,
        )
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(
            json.dumps(
                verify_artifact(args.output, args.processes, args.chunk_size),
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    if args.command == "probe":
        audit = exact_scan(
            args.maximum_carry,
            args.maximum_shortcut_steps,
            args.processes,
            args.chunk_size,
        )
        print(
            json.dumps(
                {
                    "maximum_carry": audit["maximum_carry"],
                    "champion": audit["champion"],
                    "champion_ties": audit["champion_ties"],
                    "maximum_shortcut_steps_observed": audit[
                        "maximum_shortcut_steps_observed"
                    ],
                    "counterexample": None,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    if args.command == "verify":
        print(
            json.dumps(
                verify_artifact(args.artifact, args.processes, args.chunk_size),
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    raise AssertionError("unreachable command")


if __name__ == "__main__":
    raise SystemExit(main())
