#!/usr/bin/env python3
"""Exact sharded census of the deterministic odd-charge recharge map.

This is a theorem-driven probe of ``canonicalRechargeMap``, not a generic
Collatz seed scan.  Every tested input is a positive odd multiple of three,
every reported edge is replayed by ``exact_recharge``, and every finite orbit
ends with its exact undefined status.  Long survival is never promoted to an
infinite orbit; artifacts always record ``counterexample: null``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Sequence

try:
    from .outward_charge_invariant_cegis import (
        canonical_json,
        exact_recharge,
        valuation,
    )
except ImportError:
    from outward_charge_invariant_cegis import (
        canonical_json,
        exact_recharge,
        valuation,
    )


SCHEMA = "collatz-outward-charge-orbit-census-v1"


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def trace_digest(trace: list[dict[str, Any]]) -> str:
    return hashlib.sha256(canonical_json(trace)).hexdigest()


def artifact_digest(payload: dict[str, Any]) -> str:
    unsigned = dict(payload)
    unsigned.pop("artifact_sha256", None)
    return hashlib.sha256(canonical_json(unsigned)).hexdigest()


def first_charge_at_or_above(lower: int) -> int:
    candidate = max(3, lower)
    return candidate + ((3 - candidate) % 6)


def orbit_row(
    initial: int, maximum_recharges: int, maximum_shortcut_steps: int
) -> dict[str, Any]:
    charge = initial
    trace: list[dict[str, Any]] = []
    seen: set[int] = set()
    for _ in range(maximum_recharges):
        if charge in seen:
            terminal = {"status": "cycle", "input": str(charge)}
            break
        seen.add(charge)
        transition = exact_recharge(charge, maximum_shortcut_steps)
        if transition["status"] != "defined":
            terminal = {
                key: str(value) if isinstance(value, int) else value
                for key, value in transition.items()
            }
            break
        output = int(transition["output"])
        input_v3, input_unit = valuation(charge, 3)
        trace.append(
            {
                "input": str(charge),
                "input_v3": input_v3,
                "input_unit_mod_243": input_unit % 243,
                "word": str(transition["word"]),
                "forced_one_blocks": int(transition["forced_one_blocks"]),
                "output": str(output),
                "output_v3": int(transition["output_v3"]),
            }
        )
        charge = output
    else:
        terminal = {"status": "recharge_depth_cap", "input": str(charge)}

    return {
        "initial_charge": str(initial),
        "defined_recharges": len(trace),
        "terminal": terminal,
        "maximum_charge_bits": max(
            [initial.bit_length()]
            + [int(step["output"]).bit_length() for step in trace]
        ),
        "trace_sha256": trace_digest(trace),
        "trace": trace,
    }


def scan(args: argparse.Namespace) -> dict[str, Any]:
    if args.lower < 1 or args.upper < args.lower:
        raise ValueError("invalid charge interval")
    if not 0 <= args.shard_index < args.shard_count:
        raise ValueError("invalid shard")
    if args.maximum_recharges < 1 or args.maximum_shortcut_steps < 1:
        raise ValueError("invalid execution bound")

    first = first_charge_at_or_above(args.lower)
    tested = 0
    status_counts: dict[str, int] = {}
    local_records: list[dict[str, Any]] = []
    local_best = -1
    for ordinal, charge in enumerate(range(first, args.upper + 1, 6)):
        if ordinal % args.shard_count != args.shard_index:
            continue
        tested += 1
        row = orbit_row(
            charge, args.maximum_recharges, args.maximum_shortcut_steps
        )
        status = str(row["terminal"]["status"])
        status_counts[status] = status_counts.get(status, 0) + 1
        depth = int(row["defined_recharges"])
        if depth > local_best:
            local_records.append(row)
            local_best = depth

    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "kind": "shard",
        "worker_sha256": source_sha256(),
        "bounds": {
            "lower_charge": args.lower,
            "upper_charge": args.upper,
            "maximum_recharges": args.maximum_recharges,
            "maximum_shortcut_steps": args.maximum_shortcut_steps,
            "shard_index": args.shard_index,
            "shard_count": args.shard_count,
        },
        "tested_positive_odd_multiples_of_three": tested,
        "terminal_status_counts": status_counts,
        "local_record_rows": local_records,
        "claim_scope": "bounded exact deterministic recharge-map census",
        "counterexample": None,
    }
    payload["artifact_sha256"] = artifact_digest(payload)
    return payload


def merge(args: argparse.Namespace) -> dict[str, Any]:
    shards = [json.loads(Path(path).read_text()) for path in args.inputs]
    if not shards:
        raise ValueError("merge needs at least one shard")
    for shard in shards:
        if shard.get("schema") != SCHEMA or shard.get("kind") != "shard":
            raise ValueError("unexpected shard schema")
        if shard.get("artifact_sha256") != artifact_digest(shard):
            raise ValueError("shard digest mismatch")

    common = dict(shards[0]["bounds"])
    expected_count = int(common["shard_count"])
    indices = sorted(int(shard["bounds"]["shard_index"]) for shard in shards)
    if indices != list(range(expected_count)):
        raise ValueError("merge does not contain each shard exactly once")
    for shard in shards[1:]:
        bounds = dict(shard["bounds"])
        for key in (
            "lower_charge",
            "upper_charge",
            "maximum_recharges",
            "maximum_shortcut_steps",
            "shard_count",
        ):
            if bounds[key] != common[key]:
                raise ValueError("incompatible shard bounds")

    candidates = [
        row for shard in shards for row in shard["local_record_rows"]
    ]
    candidates.sort(key=lambda row: int(row["initial_charge"]))
    global_records: list[dict[str, Any]] = []
    best = -1
    for row in candidates:
        depth = int(row["defined_recharges"])
        if depth > best:
            global_records.append(row)
            best = depth

    statuses: dict[str, int] = {}
    for shard in shards:
        for status, count in shard["terminal_status_counts"].items():
            statuses[status] = statuses.get(status, 0) + int(count)
    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "kind": "merged_census",
        "worker_sha256": source_sha256(),
        "bounds": {key: value for key, value in common.items() if key != "shard_index"},
        "tested_positive_odd_multiples_of_three": sum(
            int(shard["tested_positive_odd_multiples_of_three"])
            for shard in shards
        ),
        "terminal_status_counts": statuses,
        "greatest_defined_recharge_depth": best,
        "record_rows": global_records,
        "shard_artifact_sha256": sorted(
            str(shard["artifact_sha256"]) for shard in shards
        ),
        "claim_scope": (
            "bounded exact deterministic recharge-map census; finite survival "
            "does not imply an infinite orbit"
        ),
        "counterexample": None,
    }
    payload["artifact_sha256"] = artifact_digest(payload)
    return payload


def write_payload(payload: dict[str, Any], output: Path) -> None:
    output.write_bytes(canonical_json(payload) + b"\n")


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser()
    sub = result.add_subparsers(dest="command", required=True)
    scan_parser = sub.add_parser("scan")
    scan_parser.add_argument("--lower", type=int, required=True)
    scan_parser.add_argument("--upper", type=int, required=True)
    scan_parser.add_argument("--shard-index", type=int, required=True)
    scan_parser.add_argument("--shard-count", type=int, required=True)
    scan_parser.add_argument("--maximum-recharges", type=int, default=1000)
    scan_parser.add_argument("--maximum-shortcut-steps", type=int, default=250000)
    scan_parser.add_argument("--output", type=Path, required=True)
    merge_parser = sub.add_parser("merge")
    merge_parser.add_argument("inputs", nargs="+")
    merge_parser.add_argument("--output", type=Path, required=True)
    return result


def main(argv: Sequence[str] | None = None) -> None:
    args = parser().parse_args(argv)
    payload = scan(args) if args.command == "scan" else merge(args)
    write_payload(payload, args.output)


if __name__ == "__main__":
    main()
