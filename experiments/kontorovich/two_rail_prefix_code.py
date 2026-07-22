#!/usr/bin/env python3
"""Exact least-significant-bit prefix grammar of two-rail splash gates.

For fixed amplifier length ``r``, every complete two-rail gate shape
``(s,a,b,L)`` accepts one odd payload residue modulo

    2^E,  E = a+b+2s+L+3.

Exact valuations make these LSB-first codewords prefix-free.  A successful
gate deletes the ``E-1`` nontrivial address bits and the next affine handoff
writes through a power of three.  This script audits the finite prefix tree
and independently decodes payloads from their literal valuations.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path

from two_rail_gate import TwoRailGate, two_rail_gate, verify_member


SCHEMA = "collatz-two-rail-prefix-code-audit-v1"


@dataclass(frozen=True)
class DecodedGate:
    amp_ticks: int
    clean_ticks: int
    to_plus_extra: int
    to_minus_extra: int
    output_gap: int
    input_payload: int
    plus_payload: int
    output_payload: int
    family_index: int


def v2(value: int) -> int:
    if value <= 0:
        raise ValueError("v2 expects a positive integer")
    exponent = 0
    while value & 1 == 0:
        exponent += 1
        value >>= 1
    return exponent


def code_exponent(s: int, a: int, b: int, output_gap: int) -> int:
    return a + b + 2 * s + output_gap + 3


def decode_payload(amp_ticks: int, payload: int) -> DecodedGate | None:
    """Decode the unique complete gate beginning at ``-1+2^(r+1)P``."""
    if amp_ticks < 1 or payload < 1 or payload % 2 == 0:
        raise ValueError("expected positive r and positive odd payload")

    first = pow(3, amp_ticks + 1) * payload - 1
    a = v2(first)
    plus_state = first >> a
    if plus_state <= 1:
        return None
    plus_gap = v2(plus_state - 1)
    if plus_gap < 2 or plus_gap % 2:
        return None
    s = (plus_gap - 2) // 2
    q = (plus_state - 1) >> plus_gap
    if q <= 0 or q % 2 == 0:
        raise AssertionError("decoded plus payload is not positive odd")

    second = 1 + pow(3, s + 1) * q
    b = v2(second)
    minus_state = second >> b
    output_gap = v2(minus_state + 1)
    if output_gap < 2:
        return None
    p_next = (minus_state + 1) >> output_gap
    if p_next <= 0 or p_next % 2 == 0:
        raise AssertionError("decoded output payload is not positive odd")

    gate = two_rail_gate(amp_ticks, s, a, b, output_gap)
    difference = payload - gate.input_payload_base
    if difference < 0 or difference % gate.input_payload_stride:
        raise AssertionError("decoded payload missed its complete affine family")
    family_index = difference // gate.input_payload_stride
    p, q_checked, p_next_checked = gate.payloads(family_index)
    if (p, q_checked, p_next_checked) != (payload, q, p_next):
        raise AssertionError("decoded payload triple disagrees with gate family")
    verify_member(gate, family_index)
    return DecodedGate(
        amp_ticks=amp_ticks,
        clean_ticks=s,
        to_plus_extra=a,
        to_minus_extra=b,
        output_gap=output_gap,
        input_payload=payload,
        plus_payload=q,
        output_payload=p_next,
        family_index=family_index,
    )


def codeword(gate: TwoRailGate) -> tuple[int, int]:
    exponent = code_exponent(
        gate.clean_ticks,
        gate.to_plus_extra,
        gate.to_minus_extra,
        gate.output_gap,
    )
    if gate.input_payload_stride != 1 << exponent:
        raise AssertionError("gate input stride is not the predicted code length")
    return gate.input_payload_base, exponent


def bounded_codes(amp_ticks: int, max_code_bits: int) -> list[TwoRailGate]:
    gates: list[TwoRailGate] = []
    for s in range((max_code_bits - 7) // 2 + 1):
        for a in range(1, max_code_bits + 1):
            for b in range(1, max_code_bits + 1):
                for output_gap in range(2, max_code_bits + 1):
                    if code_exponent(s, a, b, output_gap) <= max_code_bits:
                        gates.append(
                            two_rail_gate(amp_ticks, s, a, b, output_gap)
                        )
    return gates


def verify_prefix_free(gates: list[TwoRailGate]) -> None:
    codes = [codeword(gate) for gate in gates]
    for i, (left_residue, left_bits) in enumerate(codes):
        for right_residue, right_bits in codes[i + 1 :]:
            common_bits = min(left_bits, right_bits)
            if (left_residue - right_residue) % (1 << common_bits) == 0:
                raise AssertionError("two LSB-first gate codewords overlap")


def bounded_audit(max_amp_ticks: int = 16, max_code_bits: int = 20) -> dict[str, object]:
    if max_amp_ticks < 1 or max_code_bits < 7:
        raise ValueError("invalid audit bounds")
    per_r_counts: list[int] = []
    covered_numerators: list[int] = []
    sample_decodes: list[dict[str, int]] = []
    for r in range(1, max_amp_ticks + 1):
        gates = bounded_codes(r, max_code_bits)
        verify_prefix_free(gates)
        per_r_counts.append(len(gates))
        covered = sum(1 << (max_code_bits - bits) for _, bits in map(codeword, gates))
        covered_numerators.append(covered)

        # One member of every bounded cylinder is decoded independently from
        # the literal valuation equations.
        for gate in gates:
            decoded = decode_payload(r, gate.input_payload_base)
            if decoded is None:
                raise AssertionError("gate base failed literal decoder")
            if len(sample_decodes) < 8:
                sample_decodes.append(asdict(decoded))

    if len(set(per_r_counts)) != 1 or len(set(covered_numerators)) != 1:
        raise AssertionError("prefix combinatorics unexpectedly depend on r")

    odd_residues = 1 << (max_code_bits - 1)
    covered_fraction = Fraction(covered_numerators[0], odd_residues)
    infinite_kraft_mass = (
        sum(Fraction(1, 2**a) for a in range(1, 128))
        * sum(Fraction(1, 2**b) for b in range(1, 128))
        * sum(Fraction(1, 2 ** (2 * s)) for s in range(128))
        * sum(Fraction(1, 2**L) for L in range(2, 128))
        / 4
    )
    # The finite sums above omit positive tails; record the exact geometric
    # limit independently and check that the truncation lies below it.
    if not infinite_kraft_mass < Fraction(1, 6):
        raise AssertionError("truncated Kraft mass should lie below 1/6")
    if not covered_fraction < Fraction(1, 6):
        raise AssertionError("bounded prefix mass should lie below 1/6")

    return {
        "schema": SCHEMA,
        "claim_scope": (
            "exact bounded prefix-free and literal-decoder audit; the 1/6 "
            "infinite Kraft mass is an exact geometric-series derivation"
        ),
        "bounds": {
            "amp_ticks": f"1..{max_amp_ticks}",
            "maximum_code_bits_including_forced_odd_bit": max_code_bits,
            "positive_collision_extras": True,
            "minimum_output_gap": 2,
        },
        "per_amp_tick": {
            "codewords": per_r_counts[0],
            "pairwise_prefix_comparisons": (
                per_r_counts[0] * (per_r_counts[0] - 1) // 2
            ),
            "covered_odd_residues_mod_2^B": covered_numerators[0],
            "all_odd_residues_mod_2^B": odd_residues,
            "covered_fraction": (
                f"{covered_fraction.numerator}/{covered_fraction.denominator}"
            ),
        },
        "total_gate_bases_decoded": max_amp_ticks * per_r_counts[0],
        "all_bounded_codes_prefix_free": True,
        "infinite_kraft_mass_among_odd_payloads": "1/6",
        "kraft_factorization": (
            "(sum_a>=1 2^-a)(sum_b>=1 2^-b)"
            "(sum_s>=0 2^-2s)(sum_L>=2 2^-L)/4"
        ),
        "interpretation": (
            "a gate reads a sparse LSB-first binary prefix; affine linkage "
            "then multiplies the residual tape by a power of three"
        ),
        "sample_decodes": sample_decodes,
    }


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported artifact schema")
    amp_range = str(data["bounds"]["amp_ticks"])
    max_amp_ticks = int(amp_range.split("..", 1)[1])
    max_code_bits = int(data["bounds"]["maximum_code_bits_including_forced_odd_bit"])
    if data != bounded_audit(max_amp_ticks, max_code_bits):
        raise ValueError("prefix-code artifact failed exact reconstruction")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-amp-ticks", type=int, default=16)
    build.add_argument("--max-code-bits", type=int, default=20)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        for r in range(1, 8):
            for payload in range(1, 1 << 12, 2):
                decode_payload(r, payload)
        bounded_audit(4, 14)
        print("two_rail_prefix_code selftest: PASS")
    elif args.command == "build":
        data = bounded_audit(args.max_amp_ticks, args.max_code_bits)
        args.output.write_text(json.dumps(data, indent=2) + "\n")
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("two_rail_prefix_code artifact: PASS")


if __name__ == "__main__":
    main()
