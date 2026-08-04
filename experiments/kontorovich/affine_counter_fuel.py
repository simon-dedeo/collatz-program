#!/usr/bin/env python3
"""Exact scaling audit for a recurrent Collatz counter/fuel cell.

The fixed accelerated valuation word ``[1, 1, 2]`` has

    16*y = 27*x + 19.

It supports the exact two-coordinate chart

    x(c,u) = 16*c + 176*u + 7,
    16*u' = c + 27*u + 2,
    y       = x(c-1,u').

Whenever the link equation is integral, one literal cell decreases ``c`` by
one, executes the advertised valuation word, and strictly increases the
Collatz state.  A length-R countdown is compiled by one exact congruence
modulo ``16^R`` and replayed cell by cell.

This is deliberately a scaling audit, not a counterexample.  The modulus
shows the obstruction: the apparent counter may have only log2(R) logical
bits, but its fuel address consumes four actual seed bits per round.  The
same audit also records the existing standard two-rail bounds and the unary
bit cost of the YAH lasso parameter.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence

from path_compiler import accelerated_step, affine_block
from two_rail_gate import compile_standard_chain, verify_chain


SCHEMA = "collatz-affine-counter-fuel-scaling-v1"
WORD = (1, 1, 2)
ODD_STEPS = len(WORD)
HALVINGS = sum(WORD)
A = 1 << HALVINGS
C = 3**ODD_STEPS
DELTA = affine_block(WORD).constant
B = C - A
GAMMA = 2
OFFSET = 7


def canonical_json(data: Any) -> bytes:
    return json.dumps(data, sort_keys=True, separators=(",", ":")).encode()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def encode(counter: int, fuel: int) -> int:
    if counter < 0 or fuel < 0:
        raise ValueError("counter and fuel must be nonnegative")
    return A * counter + A * B * fuel + OFFSET


def compile_fuel(rounds: int) -> int:
    """Least nonnegative initial fuel supporting exactly ``rounds`` cells."""

    if rounds < 1:
        raise ValueError("round count must be positive")
    # A^j*u_j = C^j*u_0 + D_j and
    # D_(j+1) = C*D_j + A^j*(c_j+GAMMA).
    defect = 0
    a_power = 1
    for index in range(rounds):
        counter = rounds - index
        defect = C * defect + a_power * (counter + GAMMA)
        a_power *= A
    c_power = C**rounds
    return (-defect * pow(c_power, -1, a_power)) % a_power


def replay_countdown(rounds: int) -> dict[str, Any]:
    fuel = compile_fuel(rounds)
    initial_fuel = fuel
    state = encode(rounds, fuel)
    seed = state
    peak = state
    trace_digest = hashlib.sha256()

    for index in range(rounds):
        counter = rounds - index
        numerator = counter + C * fuel + GAMMA
        next_fuel, remainder = divmod(numerator, A)
        if remainder:
            raise AssertionError("compiled fuel missed its next dyadic cylinder")
        expected = encode(counter - 1, next_fuel)
        valuations: list[int] = []
        for _ in WORD:
            state, valuation = accelerated_step(state)
            valuations.append(valuation)
        if tuple(valuations) != WORD:
            raise AssertionError("literal Collatz replay disagrees with the cell word")
        if state != expected:
            raise AssertionError("counter/fuel endpoint linkage failed")
        if state <= peak:
            # Every individual cell must be outward, not merely the whole run.
            raise AssertionError("counter/fuel cell was not a strict boost")
        peak = state
        trace_digest.update(
            canonical_json([counter, fuel, next_fuel, state, valuations])
        )
        fuel = next_fuel

    address_bits = HALVINGS * rounds
    seed_bit_cap = address_bits + 9
    if seed.bit_length() > seed_bit_cap:
        raise AssertionError("advertised seed-bit cap failed")
    return {
        "rounds": rounds,
        "logical_counter_bits": rounds.bit_length(),
        "initial_fuel_bits": initial_fuel.bit_length(),
        "seed_bits": seed.bit_length(),
        "seed_bit_cap": seed_bit_cap,
        "dyadic_address_bits": address_bits,
        "accelerated_steps": ODD_STEPS * rounds,
        "total_halvings": HALVINGS * rounds,
        "ordinary_steps": (ODD_STEPS + HALVINGS) * rounds,
        "all_cells_strict_boosts": True,
        "endpoint_bits": state.bit_length(),
        "peak_bits": peak.bit_length(),
        "initial_fuel_sha256": sha256_bytes(str(initial_fuel).encode()),
        "trace_sha256": trace_digest.hexdigest(),
    }


def standard_two_rail_record(rounds: int) -> dict[str, Any]:
    chain = compile_standard_chain(rounds)
    checked = verify_chain(chain)
    bit_cap = (rounds * rounds + 23 * rounds + 12) // 2
    accelerated = (rounds * rounds + 13 * rounds) // 2
    halvings = (rounds * rounds + 21 * rounds) // 2
    ordinary = rounds * rounds + 17 * rounds
    if checked["accelerated_steps"] != accelerated:
        raise AssertionError("standard accelerated-step formula failed")
    if checked["total_halvings"] != halvings:
        raise AssertionError("standard halving formula failed")
    if checked["ordinary_steps"] != ordinary:
        raise AssertionError("standard ordinary-step formula failed")
    seed_bits = int(checked["initial_state"]).bit_length()
    if seed_bits > bit_cap:
        raise AssertionError("standard seed-bit cap failed")
    return {
        "rounds": rounds,
        "seed_bits": seed_bits,
        "seed_bit_cap": bit_cap,
        "accelerated_steps": accelerated,
        "total_halvings": halvings,
        "ordinary_steps": ordinary,
        "strict_outward_rounds": int(checked["outward_rounds"]),
    }


def yah_unary_record(logical_bits: int) -> dict[str, int]:
    if logical_bits < 1:
        raise ValueError("logical bit count must be positive")
    parameter = (1 << logical_bits) - 1
    packet_trits = 35 + 256 * parameter
    # canonical_value begins with an implicit leading ternary one, so its
    # binary length is strictly larger than the displayed trit length.
    return {
        "logical_bits": logical_bits,
        "maximum_parameter": parameter,
        "packet_trits": packet_trits,
        "seed_bits_lower_bound": packet_trits + 1,
    }


def build_audit(max_countdown_rounds: int) -> dict[str, Any]:
    if max_countdown_rounds < 16:
        raise ValueError("maximum countdown must be at least 16")
    block = affine_block(WORD)
    if (block.two_power, block.three_power, block.constant) != (A, C, DELTA):
        raise AssertionError("valuation-word affine data changed")
    if (A, C, DELTA, B, GAMMA, OFFSET) != (16, 27, 19, 11, 2, 7):
        raise AssertionError("counter/fuel constants changed")
    if B * (A * GAMMA - OFFSET) - A * A != DELTA:
        raise AssertionError("counter/fuel translation congruence failed")

    row_rounds = sorted(
        {1, 2, 4, 8, 16, 32, 64, 128, 247, 512, max_countdown_rounds}
    )
    row_rounds = [r for r in row_rounds if r <= max_countdown_rounds]
    countdown_rows = [replay_countdown(r) for r in row_rounds]
    standard_rows = [standard_two_rail_record(r) for r in (1, 2, 4, 8, 16, 64, 247)]
    yah_rows = [yah_unary_record(m) for m in (1, 2, 4, 8, 12, 16, 20)]

    return {
        "map": "accelerated_odd_3x_plus_1",
        "counter_fuel_cell": {
            "valuation_word": list(WORD),
            "balance": "16*y=27*x+19",
            "source": "x(c,u)=16*c+176*u+7",
            "link": "16*u_next=c+27*u+2",
            "endpoint": "y=x(c-1,u_next)",
            "all_cells_strict_boosts": True,
            "rows": countdown_rows,
            "uniform_bounds": {
                "seed_bits": "at most 4*R+9",
                "accelerated_steps": "3*R",
                "ordinary_steps": "7*R",
                "actual_scaling": "Theta(R)",
                "logical_counter_warning": (
                    "R may be written with log2(R) symbols, but the exact fuel "
                    "address is a residue modulo 16^R and costs 4R bits"
                ),
            },
        },
        "scalar_affine_decrement": {
            "status": "universally impossible for one fixed nonempty word",
            "reason": (
                "two adjacent equal-stride pairs force 2^S=3^O; the universal "
                "proof is kernel-checked in AffineBinaryCounterNoGo.lean"
            ),
        },
        "standard_two_rail": {
            "rows": standard_rows,
            "uniform_bounds": {
                "seed_bits": "at most (R^2+23R+12)/2",
                "accelerated_steps": "(R^2+13R)/2",
                "ordinary_steps": "R^2+17R",
                "strict_regenerated_rounds": "R",
                "actual_scaling": "Theta(seed_bits)",
                "renewal_scaling": "Theta(sqrt(seed_bits))",
            },
        },
        "yah_lift_parameter": {
            "rows": yah_rows,
            "exact_packet_length": "35+256*t ternary cells",
            "accounting": (
                "using t=2^m-1 as an m-bit logical counter costs at least "
                "36+256*(2^m-1) actual binary seed bits"
            ),
            "actual_scaling": "unary, not exponential in actual seed bits",
        },
        "closure_status": {
            "counterexample": None,
            "two_to_n_steps_from_n_actual_bits": None,
            "achieved": (
                "an exact recurrent boost cell and arbitrary finite countdowns, "
                "with exact linear bit accounting"
            ),
            "missing": (
                "a writer which regenerates the four dyadic fuel bits consumed "
                "per cell, or a nonlinear/multi-rail encoding avoiding that cost"
            ),
        },
    }


def worker_sha256() -> str:
    return sha256_bytes(Path(__file__).read_bytes())


def build_artifact(max_countdown_rounds: int) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "worker_sha256": worker_sha256(),
        "audit": build_audit(max_countdown_rounds),
    }
    payload = dict(data)
    data["artifact_sha256"] = sha256_bytes(canonical_json(payload))
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    required = {
        "schema",
        "generated_at_utc",
        "worker_sha256",
        "audit",
        "artifact_sha256",
    }
    if set(data) != required or data["schema"] != SCHEMA:
        raise ValueError("artifact schema mismatch")
    if data["worker_sha256"] != worker_sha256():
        raise ValueError("worker hash mismatch")
    payload = dict(data)
    advertised = payload.pop("artifact_sha256")
    if advertised != sha256_bytes(canonical_json(payload)):
        raise ValueError("artifact self-hash mismatch")
    rows = data["audit"]["counter_fuel_cell"]["rows"]
    maximum = max(int(row["rounds"]) for row in rows)
    if data["audit"] != build_audit(maximum):
        raise ValueError("exact scaling audit replay mismatch")
    return {
        "artifact_sha256": advertised,
        "worker_sha256": data["worker_sha256"],
        "maximum_countdown_rounds": maximum,
        "counterexample": None,
        "two_to_n_steps_from_n_actual_bits": None,
    }


def selftest() -> None:
    if DELTA != 19 or B != 11:
        raise AssertionError("affine cell selftest failed")
    for rounds in range(1, 33):
        replay_countdown(rounds)
    if standard_two_rail_record(4)["ordinary_steps"] != 84:
        raise AssertionError("standard-family selftest failed")
    if yah_unary_record(4)["packet_trits"] != 3875:
        raise AssertionError("YAH accounting selftest failed")


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-countdown-rounds", type=int, default=1024)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.command == "selftest":
        selftest()
        print("selftest: ok")
        return 0
    if args.command == "build":
        selftest()
        artifact = build_artifact(args.max_countdown_rounds)
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.output), sort_keys=True))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), sort_keys=True))
        return 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
