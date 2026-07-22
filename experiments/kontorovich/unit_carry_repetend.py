#!/usr/bin/env python3
"""Formula-compressed catcher rails which translate collision carry intact.

The unit gap regenerator isolates a finite collision carry ``B``:

    3^q*A+s = 2^p*C + 2^(p+L)*B.

Let ``r=v3(B)``, ``e=q-r``, and choose

    D = ord_(3^e)(2),
    z = B*(2^D-1)/3^q.

Then ``z`` is an ordinary positive ``D``-bit catcher word and

    B + 3^q*z = 2^D*B.

Consequently the first collision executes the exact symbolic family

    A+2^(p+L)*(z+2^D*u)
      -> C+2^(L+D)*(B+3^q*u).

The low carry is eaten, ``D`` zero positions are created, and the same carry
``B`` reappears beyond them.  This is a literal regenerative splash, but it
is only a finite delay-line cell: an infinite orbit would still need an
ordinary end cap which writes another catcher rail.

The exponents are too large to materialize at the upper compiled hierarchy
levels.  Verification uses exact modular arithmetic modulo ``3^e`` and the
odd invariant-register stride; it never constructs ``2^D`` or ``z``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from breakoff_renormalization import construct_hierarchy
from breakoff_superether import RegisterISA
from breakoff_unit_slice import unit_isa
from unit_gap_regenerator import construct_regenerator


SCHEMA = "collatz-unit-carry-repetend-v1"


def v3(value: int) -> int:
    if value == 0:
        raise ValueError("zero carry has no finite 3-adic valuation")
    value = abs(value)
    valuation = 0
    while value % 3 == 0:
        value //= 3
        valuation += 1
    return valuation


def exact_order_of_two(q: int) -> int:
    """Check ``ord_(3^q)(2)=2*3^(q-1)`` at one concrete exponent."""
    if q < 1:
        raise ValueError("the reduced ternary exponent must be positive")
    modulus = pow(3, q)
    order = 2 * pow(3, q - 1)
    if pow(2, order, modulus) != 1:
        raise AssertionError("candidate catcher period is not an order")
    if pow(2, order // 2, modulus) == 1:
        raise AssertionError("catcher order retained an unnecessary factor two")
    if q > 1 and pow(2, order // 3, modulus) == 1:
        raise AssertionError("catcher order retained an unnecessary factor three")
    return order


def divided_repetend_mod(
    reduced_carry: int, reduced_exponent: int, gap: int, modulus: int
) -> int:
    """Return ``reduced_carry*(2^gap-1)/3^e mod modulus`` exactly."""
    denominator = pow(3, reduced_exponent)
    lifted_modulus = denominator * modulus
    numerator_residue = (
        reduced_carry * (pow(2, gap, lifted_modulus) - 1)
    ) % lifted_modulus
    if numerator_residue % denominator:
        raise AssertionError("formula catcher is not integral modulo the lift")
    return (numerator_residue // denominator) % modulus


def decimal_sha256(value: int) -> str:
    return hashlib.sha256(str(value).encode()).hexdigest()


def construct_record(
    parent: RegisterISA,
    source_cells: int = 1,
    target_cells: int = 1,
    following_cells: int = 1,
) -> dict[str, object]:
    skeleton = construct_regenerator(
        parent, source_cells, target_cells, following_cells, 1
    )
    unit = unit_isa(parent)
    carry = skeleton.carry_before_splash
    q = skeleton.first_ternary_exponent
    if not 0 < carry < pow(3, q):
        raise AssertionError("canonical carry is not a positive proper ternary residue")
    carry_valuation = v3(carry)
    reduced_exponent = q - carry_valuation
    gap = exact_order_of_two(reduced_exponent)
    reduced_carry = carry // pow(3, carry_valuation)

    # The order check is the exact, formula-compressed proof that z is an
    # integer.  Positivity and z<2^D follow from 0<B<3^q.
    denominator = pow(3, reduced_exponent)
    if pow(2, gap, denominator) != 1:
        raise AssertionError("catcher numerator is not divisible")

    modulus = unit.register_stride
    catcher_mod_register = divided_repetend_mod(
        reduced_carry, reduced_exponent, gap, modulus
    )
    source_public = skeleton.source_public_exponent
    target_public = skeleton.target_public_exponent
    following_public = skeleton.following_public_exponent
    correction = skeleton.first_correction
    prefix = skeleton.next_instruction_prefix
    prefix_width = skeleton.next_instruction_width
    division = skeleton.first_division_exponent
    if (
        pow(3, q) * correction + unit.collision_sign
        != (1 << division) * prefix
        + (1 << (division + prefix_width)) * carry
    ):
        raise AssertionError("gap regenerator did not isolate the stated carry")
    if correction % 2 != 1 or prefix % 2 != 1:
        raise AssertionError("formula splash lost an odd core")
    target_power = pow(3, skeleton.second_ternary_exponent, modulus)
    source_phase = (
        unit.register_offset
        * pow(pow(2, source_public, modulus), -1, modulus)
    ) % modulus

    # Select one positive ordinary remote tail u in the invariant register.
    fixed_source = (
        correction
        + pow(2, division + prefix_width, modulus) * catcher_mod_register
    ) % modulus
    tail_coefficient = pow(
        2, division + prefix_width + gap, modulus
    )
    tail_residue = (
        (source_phase - fixed_source)
        * pow(tail_coefficient, -1, modulus)
    ) % modulus
    if tail_residue == 0:
        tail_residue = modulus

    translated_tail_mod = (
        carry + pow(3, q, modulus) * tail_residue
    ) % modulus
    target_core_mod = (
        prefix
        + pow(2, prefix_width + gap, modulus) * translated_tail_mod
    ) % modulus
    if (
        pow(2, target_public, modulus) * target_core_mod
        - unit.register_offset
    ) % modulus:
        raise AssertionError("translated target lost its register phase")

    # Consume C as the next exact instruction.  Its deterministic low carry
    # is separated from the translated packet by D+1 zero positions.
    second_numerator = (
        pow(3, skeleton.second_ternary_exponent)
        * prefix
        + unit.collision_sign
    )
    if second_numerator % (1 << skeleton.second_division_exponent):
        raise AssertionError("second instruction prefix is not divisible")
    second_carry = second_numerator >> skeleton.second_division_exponent
    if second_carry % 2 != 1:
        raise AssertionError("second instruction prefix is not valuation-exact")
    following_core_mod = (
        second_carry
        + pow(2, gap + 1, modulus)
        * target_power
        * translated_tail_mod
    ) % modulus
    if (
        pow(2, following_public, modulus) * following_core_mod
        - unit.register_offset
    ) % modulus:
        raise AssertionError("post-prefix state lost its register phase")

    return {
        "level": unit.level,
        "collision_sign": unit.collision_sign,
        "source_cells": source_cells,
        "target_cells": target_cells,
        "following_cells": following_cells,
        "ternary_exponent_q": q,
        "carry_v3": carry_valuation,
        "reduced_ternary_exponent": reduced_exponent,
        "catcher_gap_D": gap,
        "catcher_gap_decimal_digits": len(str(gap)),
        "catcher_gap_sha256": decimal_sha256(gap),
        "carry_B": carry,
        "carry_B_bits": carry.bit_length(),
        "correction_A_bits": correction.bit_length(),
        "next_instruction_C_bits": prefix.bit_length(),
        "next_instruction_width_L": prefix_width,
        "ordinary_tail_residue_mod_register": tail_residue,
        "register_stride_bits": modulus.bit_length(),
        "checks": {
            "exact_order_of_two_mod_3e": True,
            "isolated_carry_identity": True,
            "formula_catcher_integral_and_between_zero_and_2_to_D": True,
            "carry_translation_B_plus_3qz_equals_2DB": True,
            "source_register_phase": True,
            "target_register_phase": True,
            "following_register_phase": True,
            "next_instruction_valuation_exact": True,
        },
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("unit_gap_regenerator.py"),
        Path(__file__).with_name("breakoff_unit_slice.py"),
        Path(__file__).with_name("breakoff_renormalization.py"),
        Path(__file__).with_name("breakoff_superether.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def build_certificate(levels: int = 6) -> dict[str, object]:
    hierarchy, _ = construct_hierarchy(levels)
    records = [construct_record(parent) for parent in hierarchy]
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "formula-compressed exact carry-translation identity and invariant-"
            "register embedding at the stated finite hierarchy levels; no "
            "infinite catcher rail, self-writing end cap, or Collatz "
            "counterexample is claimed"
        ),
        "symbolic_identity": {
            "isolated_carry": "3^q*A+s=2^p*C+2^(p+L)*B",
            "catcher": "z=B*(2^D-1)/3^q",
            "carry_translation": "B+3^q*z=2^D*B",
            "embedded_splash": (
                "A+2^(p+L)*(z+2^D*u) -> "
                "C+2^(L+D)*(B+3^q*u)"
            ),
        },
        "bounds": {
            "compiled_levels": levels,
            "branch_triple_at_each_level": [1, 1, 1],
            "symbolic_families": len(records),
        },
        "records": records,
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported unit carry-repetend schema")
    expected = build_certificate(int(data["bounds"]["compiled_levels"]))
    if data != expected:
        raise ValueError("unit carry-repetend artifact failed reconstruction")


def selftest() -> None:
    hierarchy, _ = construct_hierarchy(2)
    records = [construct_record(parent) for parent in hierarchy]
    assert [record["ternary_exponent_q"] for record in records] == [17, 57]
    assert records[0]["carry_v3"] == 1
    assert records[0]["catcher_gap_D"] == 2 * pow(3, 15)


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(100_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--levels", type=int, default=6)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("unit carry-repetend selftest: PASS")
    elif args.command == "build":
        args.output.write_text(render(build_certificate(args.levels)))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit carry-repetend artifact: PASS")


if __name__ == "__main__":
    main()
