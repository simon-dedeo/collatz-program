#!/usr/bin/env python3
"""Exact two-rail Collatz splash gates and a 10k-digit finite program.

The ``-1`` rail uses valuation-one ticks as a spatial amplifier.  A first
collision switches to a ``+1`` rail, valuation-two ticks clean/tune the carry,
and a second collision returns to ``-1`` at a larger dyadic gap.  Congruences
give a complete affine payload family for every fixed gate shape.

The standard chain uses shapes ``r=4+i, s=1, a=b=1, L=r+2``.  At depth 247
it produces a formula-generated 10,040-digit seed and 247 outward rounds, but
exact continuation reaches 1.  It is a finite program, not a counterexample.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from math import gcd
from pathlib import Path

from path_compiler import accelerated_step


SCHEMA = "collatz-two-rail-chain-v1"
STANDARD_ROUNDS = 247
CONTINUATION_LIMIT = 1_000_000


@dataclass(frozen=True)
class TwoRailGate:
    amp_ticks: int
    clean_ticks: int
    to_plus_extra: int
    to_minus_extra: int
    input_gap: int
    plus_gap: int
    output_gap: int
    input_payload_base: int
    input_payload_stride: int
    plus_payload_base: int
    plus_payload_stride: int
    output_payload_base: int
    output_payload_stride: int

    def payloads(self, family_index: int) -> tuple[int, int, int]:
        if family_index < 0:
            raise ValueError("family index must be nonnegative")
        p = self.input_payload_base + self.input_payload_stride * family_index
        q = self.plus_payload_base + self.plus_payload_stride * family_index
        p_next = self.output_payload_base + self.output_payload_stride * family_index
        return p, q, p_next


def two_rail_gate(
    amp_ticks: int,
    clean_ticks: int,
    to_plus_extra: int,
    to_minus_extra: int,
    output_gap: int,
) -> TwoRailGate:
    if amp_ticks < 1 or clean_ticks < 0:
        raise ValueError("invalid rail lengths")
    if min(to_plus_extra, to_minus_extra) < 0 or output_gap < 2:
        raise ValueError("invalid collision extras or output gap")

    input_gap = amp_ticks + 1
    plus_gap = 2 * clean_ticks + 2

    # Solve the +1 -> -1 switch first:
    #   1+3^(s+1)Q = 2^b(-1+2^L P').
    modulus_plus = pow(3, clean_ticks + 1)
    output_residue = (
        (pow(2, to_minus_extra) + 1)
        * pow(pow(2, to_minus_extra + output_gap), -1, modulus_plus)
    ) % modulus_plus
    output_payload_seed = output_residue
    if output_payload_seed == 0 or output_payload_seed % 2 == 0:
        output_payload_seed += modulus_plus
    plus_payload_seed = (
        pow(2, to_minus_extra)
        * (-1 + pow(2, output_gap) * output_payload_seed)
        - 1
    ) // modulus_plus

    # Vary P' through its odd class, then solve the -1 -> +1 switch:
    #   3^(r+1)P-1 = 2^a(1+2^K Q).
    modulus_amp = pow(3, amp_ticks + 1)
    plus_stride_in_aux = pow(2, to_minus_extra + output_gap + 1)
    constant = 1 + pow(2, to_plus_extra) * (
        1 + pow(2, plus_gap) * plus_payload_seed
    )
    coefficient = pow(2, to_plus_extra + plus_gap) * plus_stride_in_aux
    auxiliary_residue = (
        -constant * pow(coefficient, -1, modulus_amp)
    ) % modulus_amp

    output_payload_base = (
        output_payload_seed + 2 * modulus_plus * auxiliary_residue
    )
    plus_payload_base = (
        plus_payload_seed + plus_stride_in_aux * auxiliary_residue
    )
    input_numerator = 1 + pow(2, to_plus_extra) * (
        1 + pow(2, plus_gap) * plus_payload_base
    )
    if input_numerator % modulus_amp:
        raise AssertionError("two-rail input congruence failed")
    input_payload_base = input_numerator // modulus_amp

    gate = TwoRailGate(
        amp_ticks=amp_ticks,
        clean_ticks=clean_ticks,
        to_plus_extra=to_plus_extra,
        to_minus_extra=to_minus_extra,
        input_gap=input_gap,
        plus_gap=plus_gap,
        output_gap=output_gap,
        input_payload_base=input_payload_base,
        input_payload_stride=pow(
            2,
            to_plus_extra
            + plus_gap
            + to_minus_extra
            + output_gap
            + 1,
        ),
        plus_payload_base=plus_payload_base,
        plus_payload_stride=plus_stride_in_aux * modulus_amp,
        output_payload_base=output_payload_base,
        output_payload_stride=2 * modulus_plus * modulus_amp,
    )
    _check_gate_coefficients(gate)
    return gate


def _check_gate_coefficients(gate: TwoRailGate) -> None:
    p, q, p_next = gate.payloads(0)
    assert p > 0 and p % 2 == 1
    assert q > 0 and q % 2 == 1
    assert p_next > 0 and p_next % 2 == 1
    assert (
        pow(3, gate.amp_ticks + 1) * p - 1
        == pow(2, gate.to_plus_extra)
        * (1 + pow(2, gate.plus_gap) * q)
    )
    assert (
        1 + pow(3, gate.clean_ticks + 1) * q
        == pow(2, gate.to_minus_extra)
        * (-1 + pow(2, gate.output_gap) * p_next)
    )


def verify_member(gate: TwoRailGate, family_index: int) -> tuple[int, int]:
    p, q, p_next = gate.payloads(family_index)
    start = -1 + pow(2, gate.input_gap) * p
    endpoint = -1 + pow(2, gate.output_gap) * p_next
    state = start

    for t in range(gate.amp_ticks):
        assert state == -1 + pow(3, t) * pow(2, gate.input_gap - t) * p
        state, valuation = accelerated_step(state)
        assert valuation == 1
    state, valuation = accelerated_step(state)
    assert valuation == 1 + gate.to_plus_extra
    assert state == 1 + pow(2, gate.plus_gap) * q

    for t in range(gate.clean_ticks):
        assert state == 1 + pow(3, t) * pow(2, gate.plus_gap - 2 * t) * q
        state, valuation = accelerated_step(state)
        assert valuation == 2
    state, valuation = accelerated_step(state)
    assert valuation == 2 + gate.to_minus_extra
    assert state == endpoint
    return start, endpoint


def standard_gate(amp_ticks: int) -> TwoRailGate:
    return two_rail_gate(
        amp_ticks=amp_ticks,
        clean_ticks=1,
        to_plus_extra=1,
        to_minus_extra=1,
        output_gap=amp_ticks + 2,
    )


@dataclass(frozen=True)
class CompiledChain:
    rounds: int
    input_payload_base: int
    input_payload_stride: int
    output_payload_base: int
    output_payload_stride: int


def compile_standard_chain(rounds: int) -> CompiledChain:
    """Intersect consecutive gate families without enumerating any seed range."""
    if rounds < 1:
        raise ValueError("round count must be positive")
    first = standard_gate(4)
    root_base = first.input_payload_base
    root_stride = first.input_payload_stride
    output_base = first.output_payload_base
    output_stride = first.output_payload_stride

    for index in range(1, rounds):
        gate = standard_gate(4 + index)
        common = gcd(output_stride, gate.input_payload_stride)
        difference = gate.input_payload_base - output_base
        if difference % common:
            raise AssertionError("consecutive gate progressions do not intersect")
        reduced_modulus = gate.input_payload_stride // common
        parameter_residue = (
            (difference // common)
            * pow(output_stride // common, -1, reduced_modulus)
        ) % reduced_modulus

        root_base += root_stride * parameter_residue
        root_stride *= reduced_modulus
        matched_payload = output_base + output_stride * parameter_residue
        next_family_index = (
            matched_payload - gate.input_payload_base
        ) // gate.input_payload_stride
        next_family_stride = (
            output_stride * reduced_modulus // gate.input_payload_stride
        )
        output_base = (
            gate.output_payload_base
            + gate.output_payload_stride * next_family_index
        )
        output_stride = gate.output_payload_stride * next_family_stride

    return CompiledChain(
        rounds=rounds,
        input_payload_base=root_base,
        input_payload_stride=root_stride,
        output_payload_base=output_base,
        output_payload_stride=output_stride,
    )


def verify_chain(chain: CompiledChain) -> dict[str, int | bool]:
    payload = chain.input_payload_base
    state = -1 + 32 * payload
    initial_state = state
    accelerated_steps = 0
    total_halvings = 0
    outward_rounds = 0
    for index in range(chain.rounds):
        gate = standard_gate(4 + index)
        difference = payload - gate.input_payload_base
        if difference < 0 or difference % gate.input_payload_stride:
            raise AssertionError("compiled payload missed a gate family")
        family_index = difference // gate.input_payload_stride
        expected_start, endpoint = verify_member(gate, family_index)
        if expected_start != state:
            raise AssertionError("consecutive rail states do not match")
        if endpoint > state:
            outward_rounds += 1
        state = endpoint
        payload = gate.payloads(family_index)[2]
        accelerated_steps += gate.amp_ticks + gate.clean_ticks + 2
        total_halvings += (
            gate.amp_ticks
            + 1
            + gate.to_plus_extra
            + 2 * gate.clean_ticks
            + 2
            + gate.to_minus_extra
        )
    if payload != chain.output_payload_base:
        raise AssertionError("compiled output payload mismatch")
    return {
        "initial_state": initial_state,
        "endpoint": state,
        "accelerated_steps": accelerated_steps,
        "total_halvings": total_halvings,
        "ordinary_steps": accelerated_steps + total_halvings,
        "outward_rounds": outward_rounds,
        "all_rounds_outward": outward_rounds == chain.rounds,
    }


def decimal_digits(n: int) -> int:
    sys.set_int_max_str_digits(max(sys.get_int_max_str_digits(), 100_000))
    return len(str(n))


def continuation_audit(seed: int) -> dict[str, int | bool]:
    state = seed
    peak = seed
    peak_at = 0
    steps = 0
    halvings = 0
    while state != 1 and steps < CONTINUATION_LIMIT:
        state, valuation = accelerated_step(state)
        steps += 1
        halvings += valuation
        if state > peak:
            peak = state
            peak_at = steps
    if state != 1:
        raise AssertionError("standard chain did not reach 1 within the limit")
    return {
        "step_limit": CONTINUATION_LIMIT,
        "reached_one": True,
        "accelerated_steps": steps,
        "total_halvings": halvings,
        "ordinary_steps": steps + halvings,
        "peak_at_accelerated_step": peak_at,
        "peak_significant_binary_bits": peak.bit_length(),
    }


def build_certificate(rounds: int = STANDARD_ROUNDS) -> dict[str, object]:
    chain = compile_standard_chain(rounds)
    checked = verify_chain(chain)
    seed = int(checked["initial_state"])
    endpoint = int(checked["endpoint"])
    previous = compile_standard_chain(rounds - 1) if rounds > 1 else None
    continuation = continuation_audit(seed)
    return {
        "schema": SCHEMA,
        "map": "accelerated_odd_3x_plus_1",
        "claim_scope": (
            "a low-description finite outward two-rail program; exact full "
            "continuation reaches 1, so this is not a counterexample"
        ),
        "schedule": {
            "rounds": rounds,
            "round_index": "i=0,...,rounds-1",
            "amp_ticks": "r_i=4+i",
            "clean_ticks": 1,
            "to_plus_extra": 1,
            "to_minus_extra": 1,
            "input_gap": "5+i",
            "output_gap": "6+i",
            "valuation_word_per_round": "[1]^r_i ++ [2,2,3]",
        },
        "seed_generator": {
            "method": "least affine-family intersection for all rounds",
            "decimal_literal_stored": False,
            "significant_binary_bits": seed.bit_length(),
            "decimal_digits": decimal_digits(seed),
            "previous_depth_has_same_seed": (
                previous is not None
                and previous.input_payload_base == chain.input_payload_base
            ),
        },
        "program": {
            "accelerated_steps": checked["accelerated_steps"],
            "total_halvings": checked["total_halvings"],
            "ordinary_steps": checked["ordinary_steps"],
            "outward_rounds": checked["outward_rounds"],
            "all_rounds_outward": checked["all_rounds_outward"],
            "initial_gap": 5,
            "final_gap": 5 + rounds,
            "endpoint_significant_binary_bits": endpoint.bit_length(),
            "endpoint_decimal_digits": decimal_digits(endpoint),
        },
        "first_round_regression": {
            "seed": "94751",
            "valuations": [1, 1, 1, 1, 2, 2, 3],
            "endpoint": "101183",
            "input_payload": "2961",
            "output_payload": "1581",
        },
        "full_continuation": continuation,
        "verification": {
            "arithmetic": "python_exact_integer",
            "every_gate_reconstructed": True,
            "every_designed_step_replayed": True,
            "full_continuation_replayed": True,
        },
    }


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported artifact schema")
    rounds = int(data["schedule"]["rounds"])
    expected = build_certificate(rounds)
    if data != expected:
        raise ValueError("artifact fields failed exact reconstruction")


def selftest() -> None:
    gate = standard_gate(4)
    assert gate.payloads(0) == (2961, 22485, 1581)
    assert verify_member(gate, 0) == (94751, 101183)
    for rounds in range(1, 17):
        checked = verify_chain(compile_standard_chain(rounds))
        assert checked["all_rounds_outward"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--rounds", type=int, default=STANDARD_ROUNDS)
    check = subparsers.add_parser("verify")
    check.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("two_rail_gate selftest: PASS")
    elif args.command == "build":
        data = build_certificate(args.rounds)
        args.output.write_text(json.dumps(data, indent=2) + "\n")
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("two_rail_gate artifact: PASS")


if __name__ == "__main__":
    main()
