#!/usr/bin/env python3
"""Verify a formula-generated 11,846-digit Collatz delay line.

Colussi's order-10 repetend seed is reconstructed from its formula, never from
a decimal literal.  A ten-instruction exact header sends it to ``1+2^39348``;
the resulting separated packet then traverses a 39,348-bit delay line through
19,673 exact valuation-two steps before its first collision.

The same verifier continues the generated seed exactly to ``1``.  This is a
finite spatial primitive for bouncer synthesis, not a counterexample.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from path_compiler import accelerated_step, affine_block, replay_word


SCHEMA = "collatz-colussi-spatial-delay-v1"
ORDER = 10
HEADER = (1, 1, 2, 1, 1, 1, 5, 1, 4, 1)
POSTCOLLISION_STEPS = 1024
CONTINUATION_LIMIT = 1_000_000


def colussi_seed(order: int) -> tuple[int, int]:
    """Return ``(lambda_h,a_h)`` for Colussi's order-h seed value."""
    if order < 1:
        raise ValueError("order must be positive")
    lam = pow(3, order - 1)
    numerator = pow(4, lam) - 1
    denominator = pow(3, order)
    if numerator % denominator:
        raise AssertionError("Colussi seed formula was not integral")
    return lam, numerator // denominator


def decimal_digits(n: int) -> int:
    # The artifact is deliberately at the 10k-digit scale.  Python's safety
    # guard is raised only for this exact local conversion.
    sys.set_int_max_str_digits(max(sys.get_int_max_str_digits(), 100_000))
    return len(str(n))


def postcollision_audit(state: int, steps: int) -> dict[str, object]:
    """Measure whether a collision quickly regenerates a wide empty gap."""
    maximum_gap = -1
    maximum_gap_at = -1
    maximum_valuation = -1
    maximum_valuation_at = -1
    hit_one = False
    for t in range(steps):
        if state == 1:
            hit_one = True
            break
        gap = ((state - 1) & -(state - 1)).bit_length() - 1
        if gap > maximum_gap:
            maximum_gap = gap
            maximum_gap_at = t
        state, valuation = accelerated_step(state)
        if valuation > maximum_valuation:
            maximum_valuation = valuation
            maximum_valuation_at = t
    return {
        "steps_requested": steps,
        "steps_completed": t + 1 if steps else 0,
        "hit_one": hit_one,
        "maximum_v2_state_minus_one": maximum_gap,
        "maximum_gap_at_step": maximum_gap_at,
        "maximum_step_valuation": maximum_valuation,
        "maximum_valuation_at_step": maximum_valuation_at,
        "endpoint_significant_binary_bits": state.bit_length(),
    }


def continuation_audit(seed: int, limit: int) -> dict[str, object]:
    """Literally continue one generated seed to 1 within a stated limit."""
    state = seed
    peak = seed
    peak_at = 0
    accelerated_steps = 0
    total_halvings = 0
    while state != 1 and accelerated_steps < limit:
        state, valuation = accelerated_step(state)
        accelerated_steps += 1
        total_halvings += valuation
        if state > peak:
            peak = state
            peak_at = accelerated_steps
    return {
        "step_limit": limit,
        "reached_one": state == 1,
        "accelerated_steps": accelerated_steps,
        "total_halvings": total_halvings,
        "ordinary_steps": accelerated_steps + total_halvings,
        "peak_at_accelerated_step": peak_at,
        "peak_significant_binary_bits": peak.bit_length(),
    }


def build_certificate() -> dict[str, object]:
    lam, seed = colussi_seed(ORDER)
    block = affine_block(HEADER)
    padded_bits = 2 * lam
    gap = padded_bits - block.halvings
    delay_steps = (gap - 2) // 2

    if block.steps != ORDER:
        raise AssertionError("header must cancel the seed's 3^order denominator")
    if block.constant != (1 << block.halvings) + 1:
        raise AssertionError("header does not decode to a one-packet delay state")
    expected_endpoint = 1 + (1 << gap)
    if replay_word(seed, HEADER) != expected_endpoint:
        raise AssertionError("literal header replay failed")

    collision_endpoint = (1 + pow(3, delay_steps + 1)) // 2
    continuation = continuation_audit(seed, CONTINUATION_LIMIT)
    if not continuation["reached_one"]:
        raise AssertionError("generated seed did not reach 1 within the stated limit")
    return {
        "schema": SCHEMA,
        "map": "accelerated_odd_3x_plus_1",
        "claim_scope": (
            "one exact finite delay-line macro plus full exact continuation "
            "of the generated seed to 1; no nontermination is claimed"
        ),
        "seed_generator": {
            "colussi_order": ORDER,
            "lambda": lam,
            "expression": "(4^lambda-1)/3^order",
            "padded_binary_bits": padded_bits,
            "significant_binary_bits": seed.bit_length(),
            "decimal_digits": decimal_digits(seed),
        },
        "header": {
            "valuations": list(HEADER),
            "accelerated_steps": block.steps,
            "total_halvings": block.halvings,
            "affine_constant": str(block.constant),
            "exact_endpoint": f"1+2^{gap}",
        },
        "delay_line": {
            "gap_exponent": gap,
            "valuation": 2,
            "steps": delay_steps,
            "closed_form": f"x_t=1+3^t*2^({gap}-2t)",
            "last_state": f"1+4*3^{delay_steps}",
            "collision_valuation": 3,
            "collision_endpoint": f"(1+3^{delay_steps + 1})/2",
        },
        "postcollision_audit": postcollision_audit(
            collision_endpoint, POSTCOLLISION_STEPS
        ),
        "full_continuation": continuation,
        "verification": {
            "arithmetic": "python_exact_integer",
            "header_replayed_stepwise": True,
            "delay_replayed_stepwise": True,
            "collision_replayed": True,
            "full_continuation_replayed_stepwise": True,
        },
    }


def verify(data: dict[str, object]) -> None:
    expected = build_certificate()
    if data != expected:
        raise ValueError("artifact fields do not match exact reconstruction")

    lam, seed = colussi_seed(ORDER)
    del lam
    state = replay_word(seed, HEADER)
    gap = int(data["delay_line"]["gap_exponent"])
    steps = int(data["delay_line"]["steps"])
    if state != 1 + (1 << gap):
        raise AssertionError("decoded separated-packet state is wrong")

    # Independent literal replay of the symbolic delay formula.  This is a
    # certificate check over one generated object, not an interval search.
    for t in range(steps):
        expected_state = 1 + pow(3, t) * (1 << (gap - 2 * t))
        if state != expected_state:
            raise AssertionError(f"delay closed form failed at t={t}")
        state, valuation = accelerated_step(state)
        if valuation != 2:
            raise AssertionError(f"delay valuation failed at t={t}")

    if state != 1 + 4 * pow(3, steps):
        raise AssertionError("last pre-collision state is wrong")
    collision, valuation = accelerated_step(state)
    if valuation != 3:
        raise AssertionError("terminal collision does not have valuation three")
    if collision != (1 + pow(3, steps + 1)) // 2:
        raise AssertionError("collision endpoint formula is wrong")
    if postcollision_audit(collision, POSTCOLLISION_STEPS) != data[
        "postcollision_audit"
    ]:
        raise AssertionError("post-collision bounded audit failed replay")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    check = subparsers.add_parser("verify")
    check.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        data = build_certificate()
        verify(data)
        print("colussi_delay selftest: PASS")
    elif args.command == "build":
        data = build_certificate()
        verify(data)
        args.output.write_text(json.dumps(data, indent=2) + "\n")
        print(f"wrote {args.output}")
    else:
        verify(json.loads(args.artifact.read_text()))
        print("colussi_delay artifact: PASS")


if __name__ == "__main__":
    main()
