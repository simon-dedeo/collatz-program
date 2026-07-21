#!/usr/bin/env python3
"""Verify and merge every shard from search_nonuniform.py."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from path_compiler import verify_cycle_certificate
from search_nonuniform import bounded_fate, event_key, morphism_count


SUM_KEYS = (
    "morphisms_searched",
    "coding_templates",
    "depth_instances",
    "positive_multiplier_instances",
    "exact_cycle_instances",
    "trivial_cycle_instances",
    "nontrivial_cycle_instances",
    "seed_stabilization_events",
    "nontrivial_seed_stabilization_events",
    "one_avoiding_seed_stabilization_events",
)
EVENT_KEYS = (
    "longest_seed_stabilization",
    "longest_nontrivial_seed_stabilization",
    "longest_one_avoiding_seed_stabilization",
)


def merge(paths: list[Path], expect_shards: int | None = None) -> dict[str, object]:
    if not paths:
        raise ValueError("no shard files supplied")
    rows = [json.loads(path.read_text()) for path in paths]
    first = rows[0]
    if first.get("schema") != "collatz-nonuniform-morphic-search-shard-v1":
        raise ValueError("unsupported shard schema")
    shards = int(first["shards"])
    if expect_shards is not None and shards != expect_shards:
        raise ValueError(f"artifact says {shards} shards, expected {expect_shards}")
    indices = set()
    for row in rows:
        for key in ("schema", "arithmetic", "source_sha256", "bounds", "shards"):
            if row[key] != first[key]:
                raise ValueError(f"inconsistent shard field {key}")
        index = int(row["shard_index"])
        if index in indices:
            raise ValueError(f"duplicate shard {index}")
        indices.add(index)
    wanted = set(range(shards))
    if indices != wanted:
        missing = sorted(wanted - indices)
        extra = sorted(indices - wanted)
        raise ValueError(f"shard coverage failure: missing={missing}, extra={extra}")

    total_morphisms = morphism_count(int(first["bounds"]["max_image_length"]))
    if any(int(row["morphisms_seen"]) != total_morphisms for row in rows):
        raise ValueError("a shard did not enumerate the complete morphism index space")

    cycles = [cycle for row in rows for cycle in row["nontrivial_cycles"]]
    for cycle in cycles:
        cert = verify_cycle_certificate(cycle)
        if cert.seed == 1:
            raise ValueError("nontrivial cycle list contains seed 1")

    merged: dict[str, object] = {
        "schema": "collatz-nonuniform-morphic-search-v1",
        "arithmetic": first["arithmetic"],
        "source_sha256": first["source_sha256"],
        "bounds": first["bounds"],
        "shards": shards,
        "total_morphisms_in_class": total_morphisms,
        "nontrivial_cycles": cycles,
    }
    for key in SUM_KEYS:
        merged[key] = sum(int(row[key]) for row in rows)
    if merged["morphisms_searched"] != total_morphisms:
        raise ValueError("merged morphism coverage is not exact")
    if merged["nontrivial_cycle_instances"] != len(cycles):
        raise ValueError("nontrivial cycle count/list mismatch")

    for key in EVENT_KEYS:
        candidates = [row[key] for row in rows if row[key] is not None]
        merged[key] = max(candidates, key=event_key) if candidates else None
    event = merged["longest_one_avoiding_seed_stabilization"]
    if event is not None:
        event = dict(event)
        event["continuation"] = bounded_fate(
            int(event["seed"]), int(first["bounds"]["continuation_steps"])
        )
        merged["longest_one_avoiding_seed_stabilization"] = event
    return merged


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shards", type=Path, nargs="+")
    parser.add_argument("--expect-shards", type=int)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = merge(args.shards, args.expect_shards)
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
        print(f"verified {len(args.shards)} shards; wrote {args.output}")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
