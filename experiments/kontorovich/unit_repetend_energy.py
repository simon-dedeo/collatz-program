#!/usr/bin/env python3
"""Exact energy no-go for consecutive sign-negative unit repetend splashes.

For the marker-one, sign-negative repetend, integrality forces

    T=(2j+1)*3^(q-1).

If q>=3, then ``3^(q-1)>=2q+1`` and hence

    2^T >= 2^(2q+1) = 2*4^q > 2*3^q.

The unit recurrence ``2^T h'=3^q h-1`` therefore implies ``h>2h'``.
No positive integer core can support infinitely many consecutive splashes of
this type.  This worker audits the generic integer chain and the three finite
sign-negative hierarchy levels; it does not exclude interleaved charge phases
or other markers.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from breakoff_renormalization import construct_hierarchy
from breakoff_unit_slice import unit_isa
from unit_repetend_splash import minimal_target_exponent


SCHEMA = "collatz-unit-repetend-energy-v1"


def generic_inequality_audit(q: int) -> dict[str, object]:
    if q < 3:
        raise ValueError("the exact energy separator uses q>=3")
    half_order = pow(3, q - 1)
    if half_order < 2 * q + 1:
        raise AssertionError("3^(q-1) did not dominate 2q+1")
    if not pow(4, q) > pow(3, q):
        raise AssertionError("4^q did not dominate 3^q")
    return {
        "q": q,
        "half_order_decimal_digits": len(str(half_order)),
        "three_power_dominates_2q_plus_1": True,
        "four_power_dominates_three_power": True,
        "symbolic_conclusion": (
            "for every odd k>=1 and T=k*3^(q-1), "
            "2^T>2*3^q"
        ),
    }


def level_record(parent: object) -> dict[str, object]:
    unit = unit_isa(parent)
    if unit.collision_sign != -1:
        raise ValueError("energy record requires a negative collision sign")
    marker, q, _, target, target_cells = minimal_target_exponent(parent, 1)
    if marker != 1:
        raise AssertionError("negative repetend did not use marker one")
    half_order = pow(3, q - 1)
    if target % half_order:
        raise AssertionError("target exponent is not a half-order multiple")
    multiplier = target // half_order
    if multiplier < 1 or multiplier % 2 != 1:
        raise AssertionError("repetend multiplier is not positive odd")
    generic = generic_inequality_audit(q)
    return {
        "level": unit.level,
        "source_cells": 1,
        "collision_sign": unit.collision_sign,
        "marker": marker,
        "q": q,
        "T": str(target),
        "target_cells": str(target_cells),
        "half_order_multiplier": str(multiplier),
        "half_order_multiplier_is_positive_odd": True,
        "exact_core_implication": (
            "2^T*h_next=3^q*h-1 with positive cores implies h>2*h_next"
        ),
        "generic_audit": generic,
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("unit_repetend_splash.py"),
        Path(__file__).with_name("breakoff_unit_slice.py"),
        Path(__file__).with_name("breakoff_renormalization.py"),
        Path(__file__).with_name("breakoff_superether.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def build_certificate() -> dict[str, object]:
    hierarchy, _ = construct_hierarchy(6)
    records = [
        level_record(parent)
        for parent in hierarchy
        if unit_isa(parent).collision_sign == -1
    ]
    if [record["level"] for record in records] != [2, 4, 6]:
        raise AssertionError("unexpected sign-negative hierarchy levels")
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact elementary no-go for an infinite consecutive stream of "
            "marker-one sign-negative full-order repetend splashes, plus "
            "concrete parameter audits at finite levels 2,4,6; interleaved "
            "charge phases and other collision programs remain open"
        ),
        "generic_proof": {
            "exponent_form": "T=(2j+1)*3^(q-1)",
            "separator": "q>=3 => 2^T>2*3^q",
            "one_step": (
                "2^T*h_next=3^q*h-1 => h>2*h_next"
            ),
            "infinite_conclusion": (
                "N consecutive splashes force h0>2^N*hN>=2^N, "
                "impossible for one fixed positive integer h0 as N grows"
            ),
        },
        "records": records,
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported repetend-energy schema")
    if data != build_certificate():
        raise ValueError("repetend-energy artifact failed reconstruction")


def selftest() -> None:
    for q in (3, 4, 17, 57):
        generic_inequality_audit(q)


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(200_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("unit repetend-energy selftest: PASS")
    elif args.command == "build":
        data = build_certificate()
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit repetend-energy artifact: PASS")


if __name__ == "__main__":
    main()
