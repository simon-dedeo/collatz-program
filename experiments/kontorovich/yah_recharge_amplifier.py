#!/usr/bin/env python3
"""Exact certificates for the YAH packet recharge amplifier.

The queue packet ``P(q)=2(01)^q`` has a distinguished nonlocal address.  If

    41*9^q + 15 = 0 (mod 2^(K+5)),

then its (neutral-length) queue macro writes at least ``K`` units of dyadic
charge into the endpoint defect ``N+1``.  A maximal prefix of subsequent
all-odd shortcut steps converts that charge into ternary program space.  The
choice ``K=4G+1`` guarantees at least ``G`` new trits.

The address has a free lift ``q=q0+2^(K+2)t``.  After division by the forced
power of two, its normalized cofactor register is a 2-adic isometry in ``t``.  Thus
the amplifier preserves a lossless, globally distributed address register;
the remaining counterexample obligation is to make that register select the
next amplifier invocation autonomously.

The finite burst also has a spatially typed endpoint.  The normalized defect
has exact 3-adic valuation two, so after ``J`` safe odd steps the ternary word
ends in exactly ``J+2`` maximal trits.  Recharge therefore emits a contiguous
right-hand reservoir as well as preserving the prefix register.

This is not an infinite-orbit certificate.  Bounded word traces below replay
the exact queue transducer.  The unbounded statements are recorded as
algebraic/LTE proof schemas pending independent Lean formalization.
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence

import yah_context_loop as yah
import yah_queue_macro as queue


SCHEMA = "yah_recharge_amplifier_v1"


def log9_mod_power(target: int, modulus_exponent: int) -> int:
    """Return the unique q mod 2^(e-3) with 9^q=target mod 2^e."""

    if modulus_exponent < 3:
        raise ValueError("modulus exponent must be at least three")
    modulus = 1 << modulus_exponent
    target %= modulus
    if target % 8 != 1:
        raise ValueError("target is not in 1+8 Z/2^e Z")
    q = 0
    for exponent in range(3, modulus_exponent):
        lifted_modulus = 1 << (exponent + 1)
        lift_bit = 1 << (exponent - 3)
        candidates = (q, q + lift_bit)
        matches = [
            candidate
            for candidate in candidates
            if pow(9, candidate, lifted_modulus)
            == target % lifted_modulus
        ]
        if len(matches) != 1:
            raise AssertionError("base-nine discrete-log lift is not unique")
        q = matches[0]
    if pow(9, q, modulus) != target:
        raise AssertionError("base-nine discrete logarithm failed")
    return q


def packet_address(growth_cells: int) -> dict[str, int]:
    """Construct the least packet address guaranteeing ``growth_cells``."""

    if growth_cells < 1:
        raise ValueError("growth target must be positive")
    charge = 4 * growth_cells + 1
    modulus_exponent = charge + 5
    modulus = 1 << modulus_exponent
    target = (-15 * pow(41, -1, modulus)) % modulus
    q0 = log9_mod_power(target, modulus_exponent)
    period = 1 << (charge + 2)
    if not (0 <= q0 < period and q0 % 4 == 1):
        raise AssertionError("packet address has the wrong phase")
    if (41 * pow(9, q0, modulus) + 15) % modulus:
        raise AssertionError("packet address misses the recharge cylinder")
    return {
        "growth_cells": growth_cells,
        "charge_K": charge,
        "modulus_exponent": modulus_exponent,
        "least_q": q0,
        "q_period": period,
        "packet_trit_length": 2 * q0 + 1,
    }


def guaranteed_length_gain(odd_steps: int) -> int:
    """Integer lower bound from 2^(J+1) 3^delta > 3^J."""

    if odd_steps < 0:
        raise ValueError("odd-step count must be nonnegative")
    delta = 0
    while (1 << (odd_steps + 1)) * 3**delta <= 3**odd_steps:
        delta += 1
    return delta


def quotient_register_mod(address: dict[str, int], lift: int, bits: int) -> int:
    """Return A_K(t) modulo 2^bits without constructing 9^q as an integer.

    A_K(t)=3*(41*9^(q0+2^(K+2)t)+15)/2^(K+5).
    """

    if lift < 0 or bits < 1:
        raise ValueError("lift must be nonnegative and bits positive")
    exponent = address["modulus_exponent"]
    modulus = 1 << (exponent + bits)
    q = address["least_q"] + address["q_period"] * lift
    numerator = (3 * (41 * pow(9, q, modulus) + 15)) % modulus
    divisor = 1 << exponent
    if numerator % divisor:
        raise AssertionError("lifted packet lost its forced dyadic charge")
    return (numerator // divisor) % (1 << bits)


def symbolic_address_audit(max_growth: int) -> dict[str, Any]:
    if max_growth < 1:
        raise ValueError("symbolic growth bound must be positive")
    addresses = [packet_address(growth) for growth in range(1, max_growth + 1)]
    for address in addresses:
        growth = address["growth_cells"]
        charge = address["charge_K"]
        if charge - 1 < 4 * growth:
            raise AssertionError("safe odd prefix is too short")
        if guaranteed_length_gain(charge - 1) < growth:
            raise AssertionError("integer scale bound does not force growth")
        # The elementary all-G proof is the stronger contradiction inequality
        # at delta=G-1: 2^(4G+1)*3^(G-1) <= 3^(4G).
        if (1 << (4 * growth + 1)) * 3 ** (growth - 1) > 3 ** (4 * growth):
            raise AssertionError("uniform 4G scale inequality failed")
    return {
        "max_growth_cells": max_growth,
        "addresses": addresses,
        "all_growth_schema": (
            "for G>=1 take K=4G+1 and q=q0 mod 2^(K+2), where "
            "41*9^q+15=0 mod 2^(K+5); the neutral packet macro writes "
            "v2(N+1)>=K, and a safe all-odd macro prefix contains J>=K-1 "
            "odd steps and gains at least G trits"
        ),
        "scale_inequality": (
            "if the gain were at most G-1 after J>=4G odd steps, canonical "
            "ternary scale would force 3^(4G)<2^(4G+1)*3^(G-1), but "
            "2*16^G<=3*27^G"
        ),
    }


def register_audit(max_growth: int, register_bits: int) -> dict[str, Any]:
    if max_growth < 1 or register_bits < 1:
        raise ValueError("register bounds must be positive")
    modulus = 1 << register_bits
    cases: list[dict[str, Any]] = []
    for growth in range(1, max_growth + 1):
        address = packet_address(growth)
        outputs = [
            quotient_register_mod(address, lift, register_bits)
            for lift in range(modulus)
        ]
        if len(set(outputs)) != modulus:
            raise AssertionError("lift register is not a finite permutation")
        cases.append(
            {
                "growth_cells": growth,
                "charge_K": address["charge_K"],
                "register_bits": register_bits,
                "lifts_checked": modulus,
                "output_digest_sha256": yah.sha256_bytes(
                    yah.canonical_json(outputs)
                ),
            }
        )
    return {
        "cases": cases,
        "isometry_schema": (
            "for A_K(t)=3*(41*9^(q0+2^(K+2)t)+15)/2^(K+5), "
            "LTE gives v2(A_K(t)-A_K(u))=v2(t-u); hence every finite "
            "binary address is transmitted bijectively"
        ),
        "scope": (
            "the displayed LTE identity is an all-length proof schema; the "
            "artifact exhausts all lift residues at the stated bit width"
        ),
    }


def trace_amplifier(growth_cells: int) -> dict[str, Any]:
    """Replay one bounded packet and its conservative all-odd prefix."""

    address = packet_address(growth_cells)
    charge = address["charge_K"]
    q0 = address["least_q"]
    packet = "2" + "01" * q0
    endpoint, starts, carries = queue.macro_factorized(packet)
    if starts != [1, 0] or len(endpoint) != len(packet):
        raise AssertionError("phase-one packet macro is not neutral")
    if endpoint != queue.phase_packet_formula(0, q0):
        raise AssertionError("packet compiler formula failed")

    word = endpoint
    initial_length = len(word)
    odd_steps = 0
    macro_count = 0
    heads: list[str] = []
    trace_digest_input: list[dict[str, Any]] = [
        {"head": "2", "endpoint_sha256": yah.sha256_bytes(endpoint.encode())}
    ]
    while True:
        step_count = 1 if word[0] == "0" else 2
        if odd_steps + step_count > charge:
            break
        next_word, _, terminal_carries = queue.macro_factorized(word)
        if terminal_carries != [1] * step_count:
            raise AssertionError("recharge cylinder left the all-odd path early")
        heads.append(word[0])
        odd_steps += step_count
        macro_count += 1
        word = next_word
        trace_digest_input.append(
            {
                "head": heads[-1],
                "odd_steps": odd_steps,
                "length": len(word),
                "endpoint_sha256": yah.sha256_bytes(word.encode()),
            }
        )

    if odd_steps < charge - 1:
        raise AssertionError("maximal safe macro prefix lost two odd steps")
    length_gain = len(word) - initial_length
    lower_bound = guaranteed_length_gain(odd_steps)
    if length_gain < lower_bound or lower_bound < growth_cells:
        raise AssertionError("recharge amplifier did not meet its guarantee")
    trailing_max_trits = len(word) - len(word.rstrip("2"))
    if trailing_max_trits != odd_steps + 2:
        raise AssertionError("amplifier did not emit its exact maximal-trit reservoir")
    return {
        **address,
        "initial_packet_sha256": yah.sha256_bytes(packet.encode()),
        "post_recharge_sha256": yah.sha256_bytes(endpoint.encode()),
        "final_word_sha256": yah.sha256_bytes(word.encode()),
        "safe_macro_count": macro_count,
        "safe_odd_steps": odd_steps,
        "head_schedule": "".join(heads),
        "actual_length_gain": length_gain,
        "scale_lower_bound": lower_bound,
        "trailing_max_trits": trailing_max_trits,
        "trace_sha256": yah.sha256_bytes(yah.canonical_json(trace_digest_input)),
    }


def literal_trace_audit(max_growth: int) -> dict[str, Any]:
    if max_growth < 1:
        raise ValueError("literal growth bound must be positive")
    traces = [trace_amplifier(growth) for growth in range(1, max_growth + 1)]
    return {
        "max_growth_cells": max_growth,
        "traces": traces,
        "scope": (
            "exact queue-transducer replay at every displayed word; the "
            "all-length queue factorization is independently kernel-checked"
        ),
    }


def worker_sha256() -> str:
    return yah.sha256_bytes(Path(__file__).read_bytes())


def build_artifact(
    max_symbolic_growth: int, max_literal_growth: int, register_bits: int
) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "worker_sha256": worker_sha256(),
        "queue_worker_sha256": yah.sha256_bytes(Path(queue.__file__).read_bytes()),
        "symbolic_addresses": symbolic_address_audit(max_symbolic_growth),
        "register_audit": register_audit(
            min(max_symbolic_growth, max_literal_growth), register_bits
        ),
        "bounded_traces": literal_trace_audit(max_literal_growth),
        "closure_status": {
            "counterexample": None,
            "achieved_instruction": (
                "arbitrarily large finite space amplification with a lossless "
                "2-adic lift register"
            ),
            "missing_instruction": (
                "the exhausted register must autonomously write the next "
                "packet recharge address"
            ),
        },
    }
    payload = dict(data)
    data["artifact_sha256"] = yah.sha256_bytes(yah.canonical_json(payload))
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    required = {
        "schema",
        "generated_at_utc",
        "worker_sha256",
        "queue_worker_sha256",
        "symbolic_addresses",
        "register_audit",
        "bounded_traces",
        "closure_status",
        "artifact_sha256",
    }
    if set(data) != required or data["schema"] != SCHEMA:
        raise ValueError("artifact schema mismatch")
    if data["worker_sha256"] != worker_sha256():
        raise ValueError("worker hash mismatch")
    if data["queue_worker_sha256"] != yah.sha256_bytes(
        Path(queue.__file__).read_bytes()
    ):
        raise ValueError("queue worker hash mismatch")
    payload = dict(data)
    advertised = payload.pop("artifact_sha256")
    if advertised != yah.sha256_bytes(yah.canonical_json(payload)):
        raise ValueError("artifact self-hash mismatch")
    max_symbolic = data["symbolic_addresses"]["max_growth_cells"]
    max_literal = data["bounded_traces"]["max_growth_cells"]
    register_bits = data["register_audit"]["cases"][0]["register_bits"]
    if data["symbolic_addresses"] != symbolic_address_audit(max_symbolic):
        raise ValueError("symbolic address replay mismatch")
    if data["register_audit"] != register_audit(
        min(max_symbolic, max_literal), register_bits
    ):
        raise ValueError("register replay mismatch")
    if data["bounded_traces"] != literal_trace_audit(max_literal):
        raise ValueError("bounded trace replay mismatch")
    if data["closure_status"]["counterexample"] is not None:
        raise ValueError("unexpected counterexample claim")
    return {
        "artifact_sha256": advertised,
        "worker_sha256": data["worker_sha256"],
        "symbolic_growth_targets": max_symbolic,
        "literal_growth_targets": max_literal,
        "register_bits": register_bits,
        "counterexample": None,
    }


def selftest() -> None:
    if log9_mod_power(9, 12) != 1:
        raise AssertionError("discrete-log selftest failed")
    if guaranteed_length_gain(4) < 1 or guaranteed_length_gain(8) < 2:
        raise AssertionError("scale-bound selftest failed")
    address = packet_address(1)
    outputs = [quotient_register_mod(address, lift, 4) for lift in range(16)]
    if len(set(outputs)) != 16:
        raise AssertionError("register selftest failed")
    trace_amplifier(1)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-symbolic-growth", type=int, default=32)
    build.add_argument("--max-literal-growth", type=int, default=4)
    build.add_argument("--register-bits", type=int, default=10)
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
        artifact = build_artifact(
            args.max_symbolic_growth,
            args.max_literal_growth,
            args.register_bits,
        )
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.output), sort_keys=True))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), sort_keys=True))
        return 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
