#!/usr/bin/env python3
"""Replay every hit in a mersenne_packet_gpu.cu result artifact."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from path_compiler import v2


def replay(initial_h: int, max_steps: int) -> tuple[list[int], list[int]]:
    h = initial_h
    extras = []
    packets = [h]
    for level in range(1, max_steps + 1):
        raw = pow(3, level) * h - 1
        extra = v2(raw)
        endpoint = raw >> extra
        if (endpoint + 1) % (1 << (level + 1)):
            break
        next_h = (endpoint + 1) >> (level + 1)
        if next_h % 2 == 0:
            break
        extras.append(extra)
        packets.append(next_h)
        h = next_h
    return extras, packets


def verify(path: Path) -> dict[str, object]:
    data = json.loads(path.read_text())
    if data.get("schema") != "collatz-mersenne-packet-gpu-search-v1":
        raise ValueError("unsupported schema")
    bounds = data["bounds"]
    h_limit = int(bounds["odd_h_less_than"])
    max_steps = int(bounds["max_steps"])
    threshold = int(bounds["threshold"])
    expected_candidates = h_limit // 2
    if int(data["odd_packets_checked"]) != expected_candidates:
        raise ValueError("candidate-count mismatch")
    if int(data["overflow_count"]) != 0:
        raise ValueError("GPU search encountered an arithmetic overflow")
    hits = data["hits"]
    if int(data["hits_at_or_above_threshold"]) != len(hits):
        raise ValueError("hit-count mismatch")
    maximum = 0
    for hit in hits:
        h = int(hit["initial_h"])
        if not (0 < h < h_limit and h % 2 == 1):
            raise ValueError("hit lies outside the searched odd-packet range")
        extras, packets = replay(h, max_steps)
        if len(extras) != int(hit["renewals"]):
            raise ValueError("reported renewal length failed exact replay")
        if extras != [int(x) for x in hit["extras"]]:
            raise ValueError("reported collision extras failed exact replay")
        if len(extras) < threshold:
            raise ValueError("stored hit is below the recording threshold")
        maximum = max(maximum, len(extras))
        hit["packets"] = [str(x) for x in packets]
        hit["seed"] = str(2 * h - 1)
    if hits and maximum != int(data["maximum_renewals"]):
        raise ValueError("maximum renewal length mismatch")
    if not hits and int(data["maximum_renewals"]) >= threshold:
        raise ValueError("missing hits at the reported maximum")
    return data


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifact", type=Path)
    args = parser.parse_args()
    data = verify(args.artifact)
    print(
        "verified",
        data["hits_at_or_above_threshold"],
        "hits; maximum renewals =",
        data["maximum_renewals"],
    )


if __name__ == "__main__":
    main()
