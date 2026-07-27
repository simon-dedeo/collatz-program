#!/usr/bin/env python3
"""Exact near-neutral first-passage audit for a Yap-style local energy.

For a shortcut parity word of length L with O odd steps, the homogeneous
Archimedean multiplier is 3^O/2^L.  A first-passage word has multiplier above
one while every proper prefix has multiplier at most one.  For each
1 <= L <= B this worker chooses the least O with 3^O > 2^L and tests the
explicit word

    0^(L-O) 1^O.

It records every new exact minimum of (3^O-2^L)/2^L, constructs the canonical
least nonnegative parity-cylinder representative, and literally replays it.
The finite records show that multiplier drift alone has a very small gap;
they do not prove the gap tends to zero and do not address one infinite orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from decimal import Decimal, localcontext
from pathlib import Path
from typing import Any, Sequence


SCHEMA = "collatz-ias-yap-local-energy-v1"
DEFAULT_MAX_LENGTH = 10_000


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def shortcut_step(value: int) -> int:
    if value < 0:
        raise ValueError("shortcut state must be nonnegative")
    return (3 * value + 1) // 2 if value & 1 else value // 2


def factor_2_3(value: int) -> tuple[int, int, int]:
    if value <= 0:
        raise ValueError("factorization requires a positive integer")
    a = b = 0
    while value % 2 == 0:
        a += 1
        value //= 2
    while value % 3 == 0:
        b += 1
        value //= 3
    if math.gcd(value, 6) != 1:
        raise AssertionError("primitive factor retained a two or three")
    return a, b, value


def resource_23(value: int) -> int:
    a, b, unit = factor_2_3(value + 1)
    return a + b + unit


def canonical_parity_cylinder(bits: tuple[int, ...]) -> tuple[int, int]:
    """Return the least residue modulo 2^L and its literal endpoint."""

    residue = 0
    modulus = 1
    three_power = 1
    affine_constant = 0
    for bit in bits:
        if bit not in (0, 1):
            raise ValueError("parity symbols must be zero or one")
        quotient = (three_power * residue + affine_constant) // modulus
        if quotient & 1 != bit:
            residue += modulus
        if bit:
            affine_constant = 3 * affine_constant + modulus
            three_power *= 3
        modulus *= 2
        if (three_power * residue + affine_constant) % modulus:
            raise AssertionError("parity-cylinder lift lost integrality")

    state = residue
    for bit in bits:
        if state & 1 != bit:
            raise AssertionError("canonical parity cylinder failed literal replay")
        state = shortcut_step(state)
    formula = (three_power * residue + affine_constant) // modulus
    if state != formula:
        raise AssertionError("literal endpoint disagrees with affine formula")
    return residue, state


def first_passage_record(length: int, odd_count: int, three_power: int) -> dict[str, Any]:
    two_power = 1 << length
    zeros = length - odd_count
    if zeros < 0 or not three_power > two_power:
        raise AssertionError("record is not outward")
    if three_power // 3 > two_power // 2:
        raise AssertionError("penultimate prefix is already outward")
    bits = (0,) * zeros + (1,) * odd_count

    prefix_three = 1
    prefix_two = 1
    for index, bit in enumerate(bits, start=1):
        prefix_two *= 2
        if bit:
            prefix_three *= 3
        if index < length and prefix_three > prefix_two:
            raise AssertionError("explicit word crossed before its final symbol")
    if prefix_three != three_power or prefix_two != two_power:
        raise AssertionError("prefix-product replay changed")

    seed, endpoint = canonical_parity_cylinder(bits)
    if seed <= 0 or endpoint <= seed:
        raise AssertionError("first-passage cylinder is not positive and outward")
    expected_seed = (1 << zeros) * ((1 << odd_count) - 1)
    expected_endpoint = pow(3, odd_count) - 1
    if seed != expected_seed or endpoint != expected_endpoint:
        raise AssertionError("zero-then-one cylinder lost its closed form")
    source_factorization = factor_2_3(seed + 1)
    endpoint_factorization = factor_2_3(endpoint + 1)
    if endpoint_factorization != (0, odd_count, 1):
        raise AssertionError("endpoint boundary energy did not collapse to 3^O")
    resource_change = resource_23(endpoint) - resource_23(seed)
    if length > 1 and resource_change >= 0:
        raise AssertionError("nontrivial near-neutral record did not decrease R23")
    numerator = three_power - two_power
    with localcontext() as context:
        context.prec = 30
        decimal = format(Decimal(numerator) / Decimal(two_power), ".20E")
    return {
        "length": length,
        "odd_count": odd_count,
        "word_shape": f"0^{zeros}1^{odd_count}",
        "word_sha256": hashlib.sha256(bytes(bits)).hexdigest(),
        "multiplier_excess": {
            "numerator": str(numerator),
            "denominator": str(two_power),
            "decimal_diagnostic": decimal,
        },
        "canonical_seed": str(seed),
        "canonical_seed_bits": seed.bit_length(),
        "literal_endpoint": str(endpoint),
        "closed_form": {
            "canonical_seed": "2^(L-O)*(2^O-1)",
            "literal_endpoint": "3^O-1",
        },
        "source_n_plus_one_factorization": [
            source_factorization[0],
            source_factorization[1],
            str(source_factorization[2]),
        ],
        "endpoint_n_plus_one_factorization": [0, odd_count, "1"],
        "R23_change": str(resource_change),
        "strict_first_passage_checked": True,
        "literal_parity_replay_checked": True,
    }


def audit(max_length: int) -> dict[str, Any]:
    if max_length < 1:
        raise ValueError("maximum length must be positive")
    two_power = 1
    three_power = 1
    odd_count = 0
    best: tuple[int, int] | None = None
    records: list[dict[str, Any]] = []
    valid_pairs = 0
    for length in range(1, max_length + 1):
        two_power *= 2
        while three_power <= two_power:
            three_power *= 3
            odd_count += 1
        if three_power // 3 > two_power // 2:
            continue
        valid_pairs += 1
        numerator = three_power - two_power
        if best is None or numerator * best[1] < best[0] * two_power:
            records.append(first_passage_record(length, odd_count, three_power))
            best = numerator, two_power
    if not records or best is None:
        raise AssertionError("first-passage record set is empty")
    return {
        "max_length": max_length,
        "lengths_exhausted": max_length,
        "valid_explicit_first_passage_pairs": valid_pairs,
        "strict_record_count": len(records),
        "records": records,
        "smallest_exact_multiplier_excess": records[-1]["multiplier_excess"],
        "interpretation": (
            "exact finite obstruction to treating homogeneous Archimedean "
            "multiplier drift as a visibly uniform Yap-style local energy"
        ),
        "analytic_extrapolation_status": (
            "conjecture-free standard continued-fraction argument drafted in "
            "the companion note, but not machine-checked here"
        ),
        "required_next_term": (
            "a mixed dyadic/triadic boundary energy with a global identity and "
            "a separately proved uniform positive gap; the existing R23 "
            "resource decreases on every nontrivial record in this family"
        ),
        "claim_scope": (
            "complete exact scan only for 1<=L<=max_length; finite near-neutral "
            "blocks neither prove an asymptotic no-gap theorem nor construct "
            "an infinite compatible ordinary orbit"
        ),
        "counterexample": None,
    }


def build_artifact(max_length: int) -> dict[str, Any]:
    result = {"schema": SCHEMA, "worker_sha256": source_sha256(), "audit": audit(max_length)}
    result["artifact_sha256"] = hashlib.sha256(canonical_json(result)).hexdigest()
    return result


def verify_artifact(path: Path) -> dict[str, Any]:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unexpected Yap-energy schema")
    if expected.get("worker_sha256") != source_sha256():
        raise ValueError("worker hash mismatch")
    payload = dict(expected)
    advertised = payload.pop("artifact_sha256", None)
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("artifact self-hash mismatch")
    actual = build_artifact(int(expected["audit"]["max_length"]))
    if actual != expected:
        raise AssertionError("artifact differs from exact recomputation")
    if expected["audit"]["counterexample"] is not None:
        raise AssertionError("finite energy audit claims a counterexample")
    return {
        "artifact_sha256": expected["artifact_sha256"],
        "max_length": expected["audit"]["max_length"],
        "record_count": expected["audit"]["strict_record_count"],
        "last_record_length": expected["audit"]["records"][-1]["length"],
        "smallest_exact_multiplier_excess": expected["audit"][
            "smallest_exact_multiplier_excess"
        ],
        "counterexample": None,
    }


def selftest() -> None:
    tiny = audit(19)
    if [row["length"] for row in tiny["records"]] != [1, 3, 11, 19]:
        raise AssertionError("near-neutral record lengths changed")
    if tiny["records"][1]["multiplier_excess"] != {
        "numerator": "1",
        "denominator": "8",
        "decimal_diagnostic": "1.25000000000000000000E-1",
    }:
        raise AssertionError("length-three exact gap changed")
    if canonical_parity_cylinder((0, 1, 1)) != (6, 8):
        raise AssertionError("011 parity-cylinder regression changed")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    build = sub.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-length", type=int, default=DEFAULT_MAX_LENGTH)
    verify = sub.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    sub.add_parser("selftest")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(100_000)
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print(json.dumps({"selftest": "ok", "counterexample": None}, sort_keys=True))
    elif args.command == "build":
        artifact = build_artifact(args.max_length)
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.output), indent=2, sort_keys=True))
    elif args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), indent=2, sort_keys=True))
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()
