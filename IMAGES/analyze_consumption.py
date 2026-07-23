#!/usr/bin/env python3
"""Exact motif-exhaustion diagnostics for reviewed finite constructions."""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any

from render_collatz import exact_trace, v2


HERE = Path(__file__).resolve().parent


CASES = (
    {
        "id": "ec17_returning_glider_6",
        "seed": 213035522142268397688894067577,
        "steps_to_one": 286,
        "controlled_steps": 45,
        "controlled_language": "accelerated valuations in {1,2}",
    },
    {
        "id": "mersenne_terminal_staircase",
        "seed": 265296544373759,
        "steps_to_one": 198,
        "controlled_steps": 46,
        "controlled_language": "four -1-shadow bursts at address depths 10..13",
    },
    {
        "id": "first_passage_zero_lift_run",
        "seed": 69385,
        "steps_to_one": 56,
        "controlled_steps": 23,
        "controlled_language": "finite zero-lift first-passage-code prefix",
    },
)


def fraction(value: Fraction) -> dict[str, str]:
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def diagnose(case: dict[str, Any]) -> dict[str, Any]:
    states, valuations = exact_trace(
        case["seed"], 1, case["steps_to_one"], case["steps_to_one"]
    )
    boundary = case["controlled_steps"]
    endpoint = states[boundary]
    suffix = valuations[boundary:]
    first_large = next(
        (index for index, value in enumerate(suffix, boundary) if value >= 3),
        None,
    )
    peak = max(states)
    peak_at = states.index(peak)
    last_at_or_above_endpoint = max(
        index for index, value in enumerate(states) if value >= endpoint
    )
    prefix_values = valuations[:boundary]
    suffix_values = valuations[boundary:]
    return {
        "id": case["id"],
        "seed": str(case["seed"]),
        "controlled_language": case["controlled_language"],
        "controlled_steps": boundary,
        "controlled_endpoint": str(endpoint),
        "controlled_endpoint_bit_length": endpoint.bit_length(),
        "prefix_mean_valuation": fraction(
            Fraction(sum(prefix_values), len(prefix_values))
        ),
        "suffix_steps_to_one": len(suffix_values),
        "suffix_mean_valuation": fraction(
            Fraction(sum(suffix_values), len(suffix_values))
        ),
        "first_post_boundary_valuation_at_least_3_step": first_large,
        "low_valuation_runway_after_boundary": (
            None if first_large is None else first_large - boundary
        ),
        "peak": str(peak),
        "peak_at_step": peak_at,
        "peak_lag_after_boundary": peak_at - boundary,
        "irreversible_below_boundary_step": last_at_or_above_endpoint + 1,
        "irreversible_collapse_lag": last_at_or_above_endpoint + 1 - boundary,
        "reaches_one_at_step": len(valuations),
        "claim_scope": (
            "exact replay and finite first/last-passage statistics only; "
            "no inference about an infinite construction"
        ),
    }


def main() -> None:
    mersenne_states, _ = exact_trace(265296544373759, 1, 198, 198)
    memory_steps = [0, 10, 21, 33, 46]
    memory_rows = [
        {
            "step": step,
            "state": str(mersenne_states[step]),
            "trailing_one_memory_v2_state_plus_one": v2(mersenne_states[step] + 1),
        }
        for step in memory_steps
    ]
    for index, row in enumerate(memory_rows[:-1]):
        row["next_memory_delta"] = (
            memory_rows[index + 1]["trailing_one_memory_v2_state_plus_one"]
            - row["trailing_one_memory_v2_state_plus_one"]
        )
    artifact = {
        "schema": "collatz-visualizer-consumption-diagnostics-v1",
        "map": "T(n)=(3*n+1)/2^v2(3*n+1)",
        "definition": {
            "boundary": "last state of the reviewed controlled finite prefix",
            "low_valuation_runway": (
                "number of post-boundary transitions before the first valuation >=3"
            ),
            "irreversible_collapse_lag": (
                "number of post-boundary steps until the trajectory falls below "
                "the boundary value and never returns to it"
            ),
        },
        "cases": [diagnose(case) for case in CASES],
        "mersenne_retraction_memory": {
            "definition": (
                "v2(n+1), equivalently the number of trailing one-bits in n; "
                "at these -1-shadow boundaries it forces memory-1 consecutive "
                "accelerated valuations equal to one"
            ),
            "rows": memory_rows,
            "interpretation": (
                "three retractions increase certified future memory by one; "
                "the fourth resets it from 13 to 3"
            ),
        },
        "counterexample": None,
    }
    output = HERE / "consumption_diagnostics.json"
    output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
    print(f"wrote {output}")


if __name__ == "__main__":
    main()
