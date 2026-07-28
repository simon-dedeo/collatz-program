#!/usr/bin/env python3
"""Exact modular CEGIS for the singular ``c -> 2 -> 2`` recharge family.

The singular alternating construction has an exact link equation

    2^(M_d+d+4) q' = 3^(M_c+d+1) q + 7*3^(d+1) + 2^(d+4),
    M_j = 2*3^j.

This worker fixes ``d=e=2`` and scans canonical ordinary sources in increasing
``c`` using only 49-bit recurrences.  It proves that the first source whose
canonical link renews once more occurs at ``c=11,626,231``.  A 52-bit replay
then gives the exact first failure: the third writer valuation is only three.
The finite two-link event is not a Collatz counterexample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Sequence


SCHEMA = "collatz-outward-singular-link-cegis-v1"
TARGET_COUNTER = 2
LINK_DIVISION_POWER = 24
SEARCH_PRECISION = 49
FAILURE_PRECISION = 52
FIRST_HIT_COUNTER = 11_626_231
LINK_CONSTANT = 253


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def v2(value: int) -> int:
    if value <= 0:
        raise ValueError("v2 requires a positive integer")
    return (value & -value).bit_length() - 1


def modular_A_z(c: int, precision: int) -> tuple[int, int]:
    """Return A=3^(2*3^c+3) and z=3^(c+1), modulo 2^precision."""

    if c < 1 or precision < 3:
        raise ValueError("invalid singular-link modular parameters")
    modulus = 2**precision
    exponent_period = 2 ** (precision - 2)
    exponent = (
        2 * pow(3, c, 2 ** (precision - 3)) + 3
    ) % exponent_period
    return pow(3, exponent, modulus), pow(3, c + 1, modulus)


def canonical_h(A: int, z: int) -> tuple[int, bool]:
    """Least ordinary h satisfying the first exact odd link.

    The dyadic gate fixes h modulo 2^25.  Exact source valuation excludes
    h=2 mod 3; if necessary the next lift by 2^25 is the least allowed one.
    """

    modulus = 2 ** (LINK_DIVISION_POWER + 1)
    h = (
        (2**LINK_DIVISION_POWER - A - LINK_CONSTANT)
        * pow((A * z) % modulus, -1, modulus)
    ) % modulus
    if h % 2:
        raise AssertionError("canonical link coefficient was not even")
    lifted = h % 3 == 2
    if lifted:
        h += modulus
    if h % 3 == 2:
        raise AssertionError("canonical source missed its exact ternary valuation")
    return h, lifted


def link_residues(c: int, precision: int) -> dict[str, int | bool]:
    modulus = 2**precision
    mask = modulus - 1
    A, z = modular_A_z(c, precision)
    h, lifted = canonical_h(A, z)
    q = (1 + z * h) & mask
    first = (A * q + LINK_CONSTANT) & mask
    second_numerator = (
        pow(3, 21, modulus) * first
        + 2**LINK_DIVISION_POWER * LINK_CONSTANT
    ) & mask
    return {
        "A": A,
        "z": z,
        "h": h,
        "ternary_lift_used": lifted,
        "q": q,
        "first_numerator": first,
        "second_composite_numerator": second_numerator,
    }


def exhaustive_first_hit(maximum_c: int) -> dict[str, Any]:
    if maximum_c < 1:
        raise ValueError("counter bound must be positive")
    modulus = 2**SEARCH_PRECISION
    mask = modulus - 1
    small_modulus = 2 ** (LINK_DIVISION_POWER + 1)
    small_mask = small_modulus - 1
    A = pow(3, 9, modulus)  # c=1: 2*3^c+3=9
    inverse_A = pow(A, -1, modulus)
    z = 9
    inverse_z = pow(z, -1, modulus)
    inverse_729 = pow(729, -1, modulus)
    inverse_3 = pow(3, -1, modulus)
    power_21 = pow(3, 21, modulus)
    ternary_lifts = 0
    hit: dict[str, Any] | None = None

    for c in range(1, maximum_c + 1):
        h = (
            (2**LINK_DIVISION_POWER - A - LINK_CONSTANT)
            * inverse_A
            * inverse_z
        ) & small_mask
        if h % 2:
            raise AssertionError("fixed-class canonical h became odd")
        if h % 3 == 2:
            h += small_modulus
            ternary_lifts += 1
        q = (1 + z * h) & mask
        first = (A * q + LINK_CONSTANT) & mask
        if first % small_modulus != 2**LINK_DIVISION_POWER:
            raise AssertionError("first link quotient was not odd")
        composite = (
            power_21 * first
            + 2**LINK_DIVISION_POWER * LINK_CONSTANT
        ) & mask
        if composite == 2 ** (2 * LINK_DIVISION_POWER):
            hit = {
                "c": c,
                "h": h,
                "A_mod_2^49": A,
                "z_mod_2^49": z,
                "q_mod_2^49": q,
                "first_numerator_mod_2^49": first,
                "second_composite_numerator_mod_2^49": composite,
            }
            break

        # E_(c+1)=3*E_c-6, so A_(c+1)=A_c^3/3^6.
        A = (A * A * A * inverse_729) & mask
        inverse_A = (inverse_A * inverse_A * inverse_A * 729) & mask
        z = (3 * z) & mask
        inverse_z = (inverse_z * inverse_3) & mask

    return {
        "counter_interval_checked": [1, maximum_c],
        "candidates_checked": hit["c"] if hit is not None else maximum_c,
        "canonical_sources_requiring_one_ternary_lift": ternary_lifts,
        "first_two_link_hit": hit,
        "leastness_scope": (
            "exhaustive only for the fixed canonical c->2->2 class; not over "
            "other target-counter pairs"
        ),
    }


def third_failure_certificate(c: int) -> dict[str, Any]:
    row = link_residues(c, FAILURE_PRECISION)
    composite = int(row["second_composite_numerator"])
    if composite % 2 ** (2 * LINK_DIVISION_POWER):
        raise AssertionError("two-link composite lost its exact division")
    q_second_mod_16 = (composite >> (2 * LINK_DIVISION_POWER)) % 16
    writer_mod_16 = (pow(3, 18, 16) * q_second_mod_16 + 7) % 16
    if writer_mod_16 != 8:
        raise AssertionError("third writer failure residue changed")
    writer_valuation = v2(writer_mod_16)
    if writer_valuation != 3:
        raise AssertionError("third writer failure valuation changed")
    public = {
        "precision_bits": FAILURE_PRECISION,
        "c": c,
        "d": TARGET_COUNTER,
        "e": TARGET_COUNTER,
        "h": int(row["h"]),
        "A_mod_2^52": int(row["A"]),
        "z_mod_2^52": int(row["z"]),
        "q_mod_2^52": int(row["q"]),
        "first_numerator_mod_2^52": int(row["first_numerator"]),
        "second_composite_numerator_mod_2^52": composite,
        "post_second_payload_mod_16": q_second_mod_16,
        "third_writer_numerator_mod_16": writer_mod_16,
        "third_writer_v2": writer_valuation,
        "minimum_legal_writer_v2": 6,
        "third_link_defined": False,
    }
    public["certificate_sha256"] = hashlib.sha256(
        (json.dumps(public, sort_keys=True, separators=(",", ":")) + "\n").encode()
    ).hexdigest()
    return public


def build_artifact(maximum_c: int) -> dict[str, Any]:
    scan = exhaustive_first_hit(maximum_c)
    hit = scan["first_two_link_hit"]
    failure = third_failure_certificate(int(hit["c"])) if hit is not None else None
    result = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "architecture": {
            "family": "canonical singular alternating links",
            "fixed_target_counters": [2, 2],
            "M_c": "2*3^c",
            "link_equation": (
                "2^(M_d+d+4)q'=3^(M_c+d+1)q+7*3^(d+1)+2^(d+4)"
            ),
            "canonical_source": "q=1+3^(c+1)h with h!=2 mod3",
        },
        "exact_scan": scan,
        "third_link_failure": failure,
        "bounded_conclusion": (
            "the first canonical c->2->2 renewal occurs at c=11626231 and "
            "fails before a third singular writer"
            if hit is not None
            else "no c->2->2 renewal in the displayed counter interval"
        ),
        "claim_scope": (
            "exact modular exhaustive search in one fixed two-link architecture; "
            "no conclusion for other counter schedules or the full Collatz map"
        ),
        "counterexample": None,
    }
    result["artifact_sha256"] = hashlib.sha256(canonical_json(result)).hexdigest()
    return result


def report(artifact: dict[str, Any]) -> dict[str, Any]:
    scan = artifact["exact_scan"]
    failure = artifact["third_link_failure"]
    return {
        "artifact_sha256": artifact["artifact_sha256"],
        "candidates_checked": scan["candidates_checked"],
        "first_two_link_hit": scan["first_two_link_hit"],
        "third_link_failure": failure,
        "counterexample": artifact["counterexample"],
    }


def verify_artifact(path: Path) -> dict[str, Any]:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unexpected singular-link schema")
    payload = dict(expected)
    advertised = payload.pop("artifact_sha256", None)
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("singular-link artifact self-hash mismatch")
    maximum_c = int(expected["exact_scan"]["counter_interval_checked"][1])
    actual = build_artifact(maximum_c)
    if actual != expected:
        raise AssertionError("singular-link artifact differs from recomputation")
    if expected.get("counterexample") is not None:
        raise AssertionError("singular-link artifact claims a counterexample")
    return report(expected)


def selftest() -> None:
    A, z = modular_A_z(1, 52)
    if A != 3**9 or z != 9:
        raise AssertionError("base modular recurrence changed")
    tiny = exhaustive_first_hit(1000)
    if tiny["first_two_link_hit"] is not None:
        raise AssertionError("unexpected tiny two-link renewal")
    failure = third_failure_certificate(FIRST_HIT_COUNTER)
    if failure["post_second_payload_mod_16"] != 9:
        raise AssertionError("third-failure certificate changed")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("selftest")
    build = sub.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--maximum-c", type=int, default=FIRST_HIT_COUNTER)
    verify = sub.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print(json.dumps({"selftest": "ok", "counterexample": None}, sort_keys=True))
        return
    if args.command == "build":
        artifact = build_artifact(args.maximum_c)
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(report(artifact), indent=2, sort_keys=True))
        return
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), indent=2, sort_keys=True))
        return
    raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()
