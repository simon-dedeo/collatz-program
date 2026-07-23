#!/usr/bin/env python3
"""Render exact accelerated odd-Collatz trajectories as binary PNGs.

Every output row is one positive odd integer.  Integers are written in base
two, right aligned, with the least significant bit at the right edge.  A one
is black and a zero (including left padding) is white.  The PNG contains one
image pixel per mathematical bit and one image row per accelerated iterate.

This is deliberately dependency-free.  PNG scanlines are emitted directly
with only Python's standard-library ``struct`` and ``zlib`` modules.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import struct
import zlib
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
DEFAULT_SPECS = HERE / "constructions.json"


def v2(value: int) -> int:
    if value == 0:
        raise ValueError("v2(0) is undefined")
    value = abs(value)
    return (value & -value).bit_length() - 1


def accelerated_step(value: int) -> tuple[int, int]:
    if value <= 0 or value % 2 == 0:
        raise ValueError("the accelerated odd map requires a positive odd integer")
    numerator = 3 * value + 1
    valuation = v2(numerator)
    return numerator >> valuation, valuation


def exact_trace(
    seed: int,
    stop_at: int,
    max_steps: int,
    expected_steps: int | None = None,
) -> tuple[list[int], list[int]]:
    if seed <= 0 or seed % 2 == 0:
        raise ValueError("seed must be a positive odd integer")
    if stop_at <= 0 or stop_at % 2 == 0:
        raise ValueError("stop_at must be a positive odd integer")
    states = [seed]
    valuations: list[int] = []
    seen = {seed}
    while states[-1] != stop_at and len(valuations) < max_steps:
        following, valuation = accelerated_step(states[-1])
        states.append(following)
        valuations.append(valuation)
        if following in seen and following != stop_at:
            raise ValueError(
                f"cycle encountered at {following} before target {stop_at}"
            )
        seen.add(following)
    if states[-1] != stop_at:
        raise ValueError(
            f"target {stop_at} not reached from {seed} within {max_steps} steps"
        )
    if expected_steps is not None and len(valuations) != expected_steps:
        raise ValueError(
            f"expected {expected_steps} steps but exact replay used "
            f"{len(valuations)}"
        )
    return states, valuations


def png_chunk(kind: bytes, payload: bytes) -> bytes:
    body = kind + payload
    return (
        struct.pack(">I", len(payload))
        + body
        + struct.pack(">I", zlib.crc32(body) & 0xFFFFFFFF)
    )


def pixel_rows(
    states: list[int], low_bits: int | None = None
) -> tuple[int, list[bytes]]:
    if low_bits is not None and low_bits <= 0:
        raise ValueError("low_bits must be positive")
    width = low_bits or max(value.bit_length() for value in states)
    rows: list[bytes] = []
    for value in states:
        # Right alignment follows ordinary place value: bit 0 is always the
        # rightmost black pixel because accelerated states are odd.
        if low_bits is None:
            padding = width - value.bit_length()
            bits = "0" * padding + f"{value:b}"
        else:
            bits = f"{value & ((1 << width) - 1):0{width}b}"
        row = bytearray(0 if bit == "1" else 255 for bit in bits)
        if len(row) != width or row[-1] != 0:
            raise AssertionError("binary rasterization invariant failed")
        rows.append(bytes(row))
    return width, rows


def write_png(
    path: Path, states: list[int], low_bits: int | None = None
) -> tuple[int, int, str]:
    width, rows = pixel_rows(states, low_bits=low_bits)
    height = len(rows)
    raw = b"".join(b"\x00" + row for row in rows)  # filter type 0
    header = struct.pack(">IIBBBBB", width, height, 8, 0, 0, 0, 0)
    payload = (
        b"\x89PNG\r\n\x1a\n"
        + png_chunk(b"IHDR", header)
        + png_chunk(b"IDAT", zlib.compress(raw, level=9))
        + png_chunk(b"IEND", b"")
    )
    path.write_bytes(payload)
    return width, height, hashlib.sha256(payload).hexdigest()


def ratio_record(value: Fraction) -> dict[str, str]:
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def analyze(states: list[int], valuations: list[int]) -> dict[str, Any]:
    width, rows = pixel_rows(states)
    peak = max(states)
    peak_at = states.index(peak)
    start = states[0]
    first_below = next((i for i, value in enumerate(states[1:], 1) if value < start), None)
    record_steps: list[int] = []
    record = 0
    for index, value in enumerate(states):
        if value > record:
            record = value
            record_steps.append(index)
    black = sum(value.bit_count() for value in states)
    total_pixels = width * len(states)
    xor_counts = [
        (states[index] ^ states[index + 1]).bit_count()
        for index in range(len(states) - 1)
    ]
    histogram = Counter(valuations)
    return {
        "rows": len(states),
        "accelerated_steps": len(valuations),
        "width_bits": width,
        "seed": str(start),
        "endpoint": str(states[-1]),
        "peak": str(peak),
        "peak_at_step": peak_at,
        "peak_over_seed": ratio_record(Fraction(peak, start)),
        "first_step_below_seed": first_below,
        "record_high_steps": record_steps,
        "start_bit_length": start.bit_length(),
        "end_bit_length": states[-1].bit_length(),
        "peak_bit_length": peak.bit_length(),
        "valuation_sum": sum(valuations),
        "mean_valuation": ratio_record(Fraction(sum(valuations), len(valuations))),
        "valuation_histogram": {str(key): histogram[key] for key in sorted(histogram)},
        "black_pixels": black,
        "total_pixels": total_pixels,
        "black_density": ratio_record(Fraction(black, total_pixels)),
        "adjacent_xor_bit_count_sum": sum(xor_counts),
        "mean_adjacent_xor_bit_count": ratio_record(
            Fraction(sum(xor_counts), len(xor_counts))
        ),
    }


def render_spec(spec: dict[str, Any], output_dir: Path) -> dict[str, Any]:
    identifier = str(spec["id"])
    seed = int(spec["seed"])
    stop_at = int(spec["stop_at"])
    expected_steps = (
        None if spec.get("expected_steps") is None else int(spec["expected_steps"])
    )
    states, valuations = exact_trace(
        seed=seed,
        stop_at=stop_at,
        max_steps=int(spec.get("max_steps", 100_000)),
        expected_steps=expected_steps,
    )
    png_path = output_dir / f"{identifier}.png"
    low_bits = None if spec.get("low_bits") is None else int(spec["low_bits"])
    width, height, png_sha256 = write_png(png_path, states, low_bits=low_bits)
    record: dict[str, Any] = {
        "schema": "accelerated-odd-collatz-bitmap-v1",
        "map": "T(n)=(3*n+1)/2^v2(3*n+1)",
        "pixel_convention": {
            "row_order": "seed at top, accelerated iterates downward",
            "alignment": "right aligned; least significant bit at right",
            "black": 1,
            "white": "0 or left padding",
            "logical_pixel_scale": 1,
        },
        "raster_window": (
            "full binary expansion"
            if low_bits is None
            else f"least significant {low_bits} bits; higher bits omitted"
        ),
        "id": identifier,
        "png": png_path.name,
        "png_sha256": png_sha256,
        "width": width,
        "height": height,
        "provenance": spec.get("provenance"),
        "scope": spec.get("scope"),
        "construction_prefix_steps": spec.get("construction_prefix_steps"),
        "analysis": analyze(states, valuations),
        "states_sha256": hashlib.sha256(
            ("\n".join(str(value) for value in states) + "\n").encode()
        ).hexdigest(),
        "valuations_sha256": hashlib.sha256(
            ("\n".join(str(value) for value in valuations) + "\n").encode()
        ).hexdigest(),
    }
    metadata_path = output_dir / f"{identifier}.json"
    metadata_path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    return record


def render_specs(spec_path: Path, output_dir: Path) -> list[dict[str, Any]]:
    specs = json.loads(spec_path.read_text())
    if not isinstance(specs, list):
        raise ValueError("construction registry must be a JSON list")
    output_dir.mkdir(parents=True, exist_ok=True)
    records = [render_spec(spec, output_dir) for spec in specs]
    manifest = {
        "schema": "accelerated-odd-collatz-bitmap-manifest-v1",
        "construction_registry": str(spec_path.relative_to(output_dir.parent)),
        "images": [
            {
                "id": record["id"],
                "png": record["png"],
                "png_sha256": record["png_sha256"],
                "width": record["width"],
                "height": record["height"],
            }
            for record in records
        ],
    }
    (output_dir / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--specs", type=Path, default=DEFAULT_SPECS)
    parser.add_argument("--output-dir", type=Path, default=HERE)
    args = parser.parse_args()
    records = render_specs(args.specs.resolve(), args.output_dir.resolve())
    for record in records:
        analysis = record["analysis"]
        print(
            f"{record['png']}: {record['width']}x{record['height']}, "
            f"steps={analysis['accelerated_steps']}, "
            f"peak_bits={analysis['peak_bit_length']}"
        )


if __name__ == "__main__":
    main()
