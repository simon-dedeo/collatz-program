#!/usr/bin/env python3
"""Empirical block-entropy diagnostics for exact Collatz bit rasters.

These are finite-string diagnostics, not Shannon entropies of a proved random
source and not measures of semantically usable controller memory.  Counts are
stored exactly; decimal entropy values are derived only for visualization.
"""

from __future__ import annotations

import json
import math
from collections import Counter
from pathlib import Path
from typing import Any

from render_collatz import exact_trace, v2


HERE = Path(__file__).resolve().parent
OUTPUT = HERE / "bit_entropy_diagnostics.json"

CASES = (
    {
        "id": "mersenne_terminal",
        "seed": 265296544373759,
        "steps": 198,
        "boundaries": [0, 10, 21, 33, 46],
        "controlled_end": 46,
        "memory_kind": "v2(n+1), exact trailing-one controller memory",
    },
    {
        "id": "ec17_returning_glider_6",
        "seed": 213035522142268397688894067577,
        "steps": 286,
        "boundaries": [0, 45, 72, 76],
        "controlled_end": 45,
        "memory_kind": (
            "v2(n+1) is reported only as a local suffix statistic; the true "
            "EC17 controller memory requires the public-payload decoder"
        ),
    },
    {
        "id": "first_passage_zero_lift",
        "seed": 69385,
        "steps": 56,
        "boundaries": [0, 23, 24],
        "controlled_end": 23,
        "memory_kind": (
            "v2(n+1) is a local suffix statistic, not the full zero-lift "
            "canonical-address state"
        ),
    },
    {
        "id": "outward_first_passage_270271",
        "seed": 270271,
        "steps": 150,
        "boundaries": [0, 87, 88],
        "controlled_end": 87,
        "memory_kind": (
            "v2(n+1) is a local suffix statistic, not the full maximal "
            "outward-code canonical-address state"
        ),
    },
)


def entropy(counts: list[int]) -> float:
    total = sum(counts)
    if total == 0:
        return 0.0
    answer = 0.0
    for count in counts:
        if count:
            probability = count / total
            answer -= probability * math.log2(probability)
    return answer


def decimal(value: float) -> str:
    return f"{value:.12f}"


def block_counts(bits: str, size: int) -> dict[str, int]:
    counts = Counter(
        bits[index : index + size]
        for index in range(len(bits) - size + 1)
    )
    return {
        f"{word:0{size}b}": counts[f"{word:0{size}b}"]
        for word in range(1 << size)
    }


def string_metrics(bits: str, maximum_block: int = 4) -> dict[str, Any]:
    if not bits:
        raise ValueError("bit string must be nonempty")
    blocks: dict[str, Any] = {}
    previous_entropy = 0.0
    for size in range(1, min(maximum_block, len(bits)) + 1):
        counts = block_counts(bits, size)
        value = entropy(list(counts.values()))
        blocks[str(size)] = {
            "counts": counts,
            "sample_count": sum(counts.values()),
            "block_entropy_bits": decimal(value),
            "entropy_per_symbol": decimal(value / size),
            "incremental_block_entropy": decimal(
                value if size == 1 else value - previous_entropy
            ),
        }
        previous_entropy = value

    zeros = bits.count("0")
    ones = len(bits) - zeros
    monobit_entropy = float(blocks["1"]["block_entropy_bits"])
    pair_increment = (
        float(blocks["2"]["incremental_block_entropy"])
        if "2" in blocks
        else 0.0
    )
    pair_capacity = monobit_entropy + (len(bits) - 1) * pair_increment
    return {
        "width": len(bits),
        "zeros": zeros,
        "ones": ones,
        "one_fraction": {"numerator": ones, "denominator": len(bits)},
        "absolute_imbalance": abs(ones - zeros),
        "blocks": blocks,
        "pair_markov_capacity_bits_diagnostic": decimal(pair_capacity),
    }


def row_record(state: int, step: int, boundary: bool) -> dict[str, Any]:
    active = f"{state:b}"
    low16 = f"{state & ((1 << 16) - 1):016b}"
    maximum_block = 4 if boundary else 2
    return {
        "step": step,
        "state": str(state),
        "boundary": boundary,
        "trailing_one_depth_v2_state_plus_one": v2(state + 1),
        "active": string_metrics(active, maximum_block),
        "low16": string_metrics(low16, maximum_block),
    }


def case_record(case: dict[str, Any]) -> dict[str, Any]:
    states, _ = exact_trace(case["seed"], 1, case["steps"], case["steps"])
    boundary_set = set(case["boundaries"])
    return {
        "id": case["id"],
        "seed": str(case["seed"]),
        "reaches_one_at_step": case["steps"],
        "controlled_end": case["controlled_end"],
        "boundaries": case["boundaries"],
        "memory_kind": case["memory_kind"],
        "rows": [
            row_record(state, step, step in boundary_set)
            for step, state in enumerate(states)
        ],
    }


def main() -> None:
    artifact = {
        "schema": "collatz-visualizer-bit-entropy-v1",
        "map": "T(n)=(3*n+1)/2^v2(3*n+1)",
        "scope": (
            "exact finite one- and two-bit counts on every row, exact counts "
            "through four bits at marked boundaries, and floating entropy "
            "renderings; empirical balance/complexity diagnostics only"
        ),
        "definitions": {
            "block_entropy_bits": (
                "plug-in entropy of exact overlapping k-bit word counts"
            ),
            "entropy_per_symbol": "block_entropy_bits divided by k",
            "incremental_block_entropy": (
                "H_k-H_(k-1) using each active finite string's overlapping "
                "counts; an entropy-rate diagnostic, not a source theorem"
            ),
        },
        "warning": (
            "balanced block frequencies measure local syntactic capacity, not "
            "certified future controller memory or mutual information with a "
            "future opcode"
        ),
        "cases": [case_record(case) for case in CASES],
        "counterexample": None,
    }
    OUTPUT.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
    print(f"wrote {OUTPUT}")


if __name__ == "__main__":
    main()
