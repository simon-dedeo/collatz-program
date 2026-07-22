#!/usr/bin/env python3
"""Exact carry-splash gates between ``+1`` spatial delay lines.

For an odd payload Q, the state ``1+2^(2r+2) Q`` executes ``r`` exact
valuation-two steps before collision.  This module solves the congruence which
makes that collision emit another sparse state ``1+2^(2r'+2) Q'``.

Finite splashes always exist, but this pure +1 rail is dissipative: every gate
constructed here strictly decreases the represented positive integer.  It is
therefore a timing/cleanup primitive, not a counterexample by itself.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass

from path_compiler import accelerated_step


@dataclass(frozen=True)
class SplashGate:
    delay_steps: int
    next_delay_steps: int
    collision_extra: int
    input_gap: int
    output_gap: int
    modulus_three: int
    next_payload_base: int
    next_payload_stride: int
    input_payload_base: int
    input_payload_stride: int

    def payloads(self, family_index: int) -> tuple[int, int]:
        if family_index < 0:
            raise ValueError("family index must be nonnegative")
        current = self.input_payload_base + self.input_payload_stride * family_index
        following = self.next_payload_base + self.next_payload_stride * family_index
        return current, following


def splash_gate(delay_steps: int, next_delay_steps: int, collision_extra: int) -> SplashGate:
    """Construct the affine family of payloads for one exact gap splash."""
    if min(delay_steps, next_delay_steps, collision_extra) < 1:
        raise ValueError("delay lengths and collision extra must be positive")
    input_gap = 2 * delay_steps + 2
    output_gap = 2 * next_delay_steps + 2
    modulus_three = pow(3, delay_steps + 1)

    coefficient = pow(2, collision_extra + output_gap)
    target = 1 - pow(2, collision_extra)
    residue = target * pow(coefficient, -1, modulus_three) % modulus_three

    # Q' must be odd.  Adding the odd modulus flips parity, so there is a
    # unique odd representative modulo 2*3^(r+1).
    next_payload_base = residue
    if next_payload_base == 0 or next_payload_base % 2 == 0:
        next_payload_base += modulus_three
    next_payload_stride = 2 * modulus_three

    numerator = pow(2, collision_extra) * (
        1 + pow(2, output_gap) * next_payload_base
    ) - 1
    if numerator % modulus_three:
        raise AssertionError("splash congruence did not make an integer payload")
    input_payload_base = numerator // modulus_three
    input_payload_stride = pow(2, collision_extra + output_gap + 1)

    gate = SplashGate(
        delay_steps=delay_steps,
        next_delay_steps=next_delay_steps,
        collision_extra=collision_extra,
        input_gap=input_gap,
        output_gap=output_gap,
        modulus_three=modulus_three,
        next_payload_base=next_payload_base,
        next_payload_stride=next_payload_stride,
        input_payload_base=input_payload_base,
        input_payload_stride=input_payload_stride,
    )
    _check_coefficients(gate)
    return gate


def _check_coefficients(gate: SplashGate) -> None:
    r = gate.delay_steps
    a = gate.collision_extra
    q, next_q = gate.payloads(0)
    assert q > 0 and q % 2 == 1
    assert next_q > 0 and next_q % 2 == 1
    assert gate.input_payload_stride == pow(2, a + gate.output_gap + 1)
    assert gate.next_payload_stride == 2 * gate.modulus_three
    assert (
        pow(3, r + 1) * q + 1
        == pow(2, a) * (1 + pow(2, gate.output_gap) * next_q)
    )


def verify_member(gate: SplashGate, family_index: int, literal: bool = True) -> tuple[int, int]:
    """Verify one splash, optionally replaying every delay tick literally."""
    r = gate.delay_steps
    a = gate.collision_extra
    q, next_q = gate.payloads(family_index)
    start = 1 + pow(2, gate.input_gap) * q
    expected_output = 1 + pow(2, gate.output_gap) * next_q

    # Coefficientwise universal identity for the affine family.
    assert (
        pow(3, r + 1) * q + 1
        == pow(2, a) * expected_output
    )

    if literal:
        state = start
        for t in range(r):
            assert state == 1 + pow(3, t) * pow(2, gate.input_gap - 2 * t) * q
            state, valuation = accelerated_step(state)
            assert valuation == 2
        assert state == 1 + 4 * pow(3, r) * q
        state, valuation = accelerated_step(state)
        assert valuation == 2 + a
        assert state == expected_output

    # A pure +1 delay/splash macro is necessarily dissipative.
    assert expected_output < start
    return start, expected_output


def selftest() -> None:
    for r in range(1, 9):
        for next_r in range(1, 11):
            for a in range(1, 7):
                gate = splash_gate(r, next_r, a)
                for family_index in range(32):
                    verify_member(gate, family_index)

    # Small human-readable regression: the gap grows from 4 to 6, even though
    # the dissipative macro sends 2961 to 833.
    gate = splash_gate(1, 2, 1)
    assert gate.payloads(0) == (185, 13)
    assert verify_member(gate, 0) == (2961, 833)


def summary(gate: SplashGate, family_index: int) -> dict[str, object]:
    start, endpoint = verify_member(gate, family_index)
    current_q, next_q = gate.payloads(family_index)
    out: dict[str, object] = {
        "delay_steps": gate.delay_steps,
        "next_delay_steps": gate.next_delay_steps,
        "collision_extra": gate.collision_extra,
        "input_gap": gate.input_gap,
        "output_gap": gate.output_gap,
        "family_index": family_index,
        "modulus_three_bits": gate.modulus_three.bit_length(),
        "current_payload_bits": current_q.bit_length(),
        "next_payload_bits": next_q.bit_length(),
        "start_bits": start.bit_length(),
        "endpoint_bits": endpoint.bit_length(),
        "strictly_decreases": endpoint < start,
        "payload_family": (
            "Q=Q0+2^(a+Jprime+1)z; "
            "Qprime=Qprime0+2*3^(r+1)z"
        ),
    }
    if max(start.bit_length(), endpoint.bit_length()) <= 256:
        out.update(
            {
                "modulus_three": str(gate.modulus_three),
                "input_payload_base": str(gate.input_payload_base),
                "input_payload_stride": str(gate.input_payload_stride),
                "next_payload_base": str(gate.next_payload_base),
                "next_payload_stride": str(gate.next_payload_stride),
                "current_payload": str(current_q),
                "next_payload": str(next_q),
                "start": str(start),
                "endpoint": str(endpoint),
            }
        )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    describe = subparsers.add_parser("describe")
    describe.add_argument("delay_steps", type=int)
    describe.add_argument("next_delay_steps", type=int)
    describe.add_argument("collision_extra", type=int)
    describe.add_argument("--family-index", type=int, default=0)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("splash_gate selftest: PASS")
    else:
        gate = splash_gate(
            args.delay_steps, args.next_delay_steps, args.collision_extra
        )
        print(json.dumps(summary(gate, args.family_index), indent=2))


if __name__ == "__main__":
    main()
