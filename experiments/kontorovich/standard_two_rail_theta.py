#!/usr/bin/env python3
"""Exact partial-theta form of the standard two-rail payload recurrence.

Lean commit ``db0971c`` proves the necessary recurrence

    2^(r+8) P_(r+1) = 3^(r+3) P_r + 69.

Every outgoing payload is exactly divisible by three.  Writing ``P_r=3U_r``
after the first gate gives

    2^(r+8) U_(r+1) = 3^(r+3) U_r + 23,  r >= 5.

Its unique 2-adic initial candidate is a rational multiple of the
Tschakaloff/partial-theta function.  This script checks every finite identity
against the exact gate compiler.  It does not assert the candidate is
irrational; the applicability of published p-adic irrationality theorems is a
separate literature/theorem-hypothesis audit.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from two_rail_gate import compile_standard_chain, standard_gate


SCHEMA = "collatz-standard-two-rail-theta-v1"
DEFAULT_ROUNDS = 247


def v3(value: int) -> int:
    exponent = 0
    while value % 3 == 0:
        value //= 3
        exponent += 1
    return exponent


def compiled_payloads(rounds: int) -> list[int]:
    if rounds < 2:
        raise ValueError("at least two gates are required")
    chain = compile_standard_chain(rounds)
    payload = chain.input_payload_base
    payloads = [payload]
    for index in range(rounds):
        gate = standard_gate(4 + index)
        difference = payload - gate.input_payload_base
        if difference < 0 or difference % gate.input_payload_stride:
            raise AssertionError("compiled payload missed its standard gate")
        family_index = difference // gate.input_payload_stride
        p, _, p_next = gate.payloads(family_index)
        if p != payload:
            raise AssertionError("gate input payload mismatch")
        payload = p_next
        payloads.append(payload)
    if payload != chain.output_payload_base:
        raise AssertionError("compiled terminal payload mismatch")
    return payloads


def theta_exponents(term_index: int) -> tuple[int, int]:
    if term_index < 0:
        raise ValueError("term index must be nonnegative")
    return (
        term_index * (term_index + 25) // 2,
        (term_index + 1) * (term_index + 16) // 2,
    )


def truncation_exponents(term_count: int) -> tuple[int, int]:
    if term_count < 1:
        raise ValueError("term count must be positive")
    return (
        term_count * (term_count + 25) // 2,
        term_count * (term_count + 15) // 2,
    )


def partial_theta_numerator(term_count: int) -> tuple[int, int]:
    """Return ``numerator, 3^G`` for the negative 23-scaled truncation."""
    _, denominator_exponent = truncation_exponents(term_count)
    denominator = pow(3, denominator_exponent)
    numerator = 0
    for index in range(term_count):
        two_exponent, three_exponent = theta_exponents(index)
        numerator -= (
            23 * pow(2, two_exponent) * pow(3, denominator_exponent - three_exponent)
        )
    return numerator, denominator


def verify_finite_identity(rounds: int) -> dict[str, int | bool]:
    payloads = compiled_payloads(rounds)
    if any(v3(payload) != 1 for payload in payloads[1:]):
        raise AssertionError("persistent exact factor of three failed")

    normalized = [payload // 3 for payload in payloads[1:]]
    for offset in range(len(normalized) - 1):
        r = 5 + offset
        if (
            pow(2, r + 8) * normalized[offset + 1]
            != pow(3, r + 3) * normalized[offset] + 23
        ):
            raise AssertionError("normalized standard recurrence failed")

    term_count = rounds - 1
    two_exponent, three_exponent = truncation_exponents(term_count)
    partial_numerator, common_denominator = partial_theta_numerator(term_count)
    if common_denominator != pow(3, three_exponent):
        raise AssertionError("partial-theta denominator mismatch")

    # Exact rational equality:
    # U_5 = partial + 2^E U_(5+K) / 3^G.
    if (
        normalized[0] * common_denominator
        != partial_numerator + pow(2, two_exponent) * normalized[-1]
    ):
        raise AssertionError("finite partial-theta identity failed")

    modulus = pow(2, two_exponent)
    theta_residue = (
        partial_numerator * pow(common_denominator, -1, modulus)
    ) % modulus
    if normalized[0] % modulus != theta_residue:
        raise AssertionError("2-adic truncation residue failed")
    return {
        "rounds": rounds,
        "normalized_recurrences": term_count,
        "all_outgoing_payloads_have_v3_exactly_one": True,
        "terminal_two_adic_precision_bits": two_exponent,
        "terminal_triadic_denominator_exponent": three_exponent,
        "initial_normalized_payload_significant_bits": normalized[0].bit_length(),
        "terminal_normalized_payload_significant_bits": normalized[-1].bit_length(),
        "finite_rational_identity_checked": True,
        "two_adic_residue_checked": True,
    }


def build_certificate(rounds: int = DEFAULT_ROUNDS) -> dict[str, object]:
    checked = verify_finite_identity(rounds)
    return {
        "schema": SCHEMA,
        "claim_scope": (
            "exact finite reduction of the standard two-rail compiler to a "
            "partial-theta truncation; no irrationality claim"
        ),
        "lean_input": {
            "commit": "db0971c",
            "necessary_recurrence": "2^(r+8) P_(r+1) = 3^(r+3) P_r + 69",
            "persistent_factor": "v3(P_(r+1))=1",
        },
        "normalized_recurrence": (
            "2^(r+8) U_(r+1) = 3^(r+3) U_r + 23, r>=5"
        ),
        "two_adic_candidate": {
            "formula": (
                "U_5 = -(23/3^8) * sum_(n>=0) "
                "(2/3)^(n(n-1)/2) * (2^13/3^9)^n"
            ),
            "function": "Tschakaloff_partial_theta",
            "q": "2/3",
            "z": "8192/19683",
            "scale": "-23/6561",
            "irrationality_status": (
                "open in this project pending a line-by-line hypothesis audit "
                "of p-adic Tschakaloff theorems"
            ),
        },
        "finite_check": checked,
    }


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported artifact schema")
    rounds = int(data["finite_check"]["rounds"])
    expected = build_certificate(rounds)
    if data != expected:
        raise ValueError("partial-theta artifact failed exact reconstruction")


def selftest() -> None:
    assert theta_exponents(0) == (0, 8)
    assert theta_exponents(1) == (13, 17)
    assert truncation_exponents(1) == (13, 8)
    for rounds in range(2, 20):
        verify_finite_identity(rounds)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--rounds", type=int, default=DEFAULT_ROUNDS)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("standard_two_rail_theta selftest: PASS")
    elif args.command == "build":
        data = build_certificate(args.rounds)
        args.output.write_text(json.dumps(data, indent=2) + "\n")
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("standard_two_rail_theta artifact: PASS")


if __name__ == "__main__":
    main()
