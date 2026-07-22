#!/usr/bin/env python3
"""Exact symbolic renewal of two sign-negative unit repetend splashes.

At hierarchy level two the unit collision has sign ``s=-1``.  The first
repetend splash from source length one is

    R0=(2^T0+1)/3^q0,
    R0+2^(T0+1)K0  ->  1+2*3^q0*K0.

To make the marker ``1`` launch a second splash, define

    c_m=(2^(3^(m-1))+1)/3^m.

The exact recurrence

    c_(m+1)=c_m-3^m*c_m^2+3^(2m-1)*c_m^3

shows ``c_m`` stabilizes modulo ``3^P`` once ``m>=P``.  Choose an odd k with
``k*c_(q1)=1 (mod 3^P)`` and put ``T1=3^(q1-1)*k``.  Binomial expansion then
gives

    R1=(2^T1+1)/3^q1 = 1 (mod 3^P).

Taking P large enough to include the first ternary bank and the register's
3-primary conductor makes ``A=(R1-1)/(2*3^q0)`` available modulo the complete
odd register.  One final residue choice gives the unbounded exact chain

    h0=R0+2^(T0+1)*(A+2^(T1+D-1)*L)
      -> R1+2^(T1+D)*3^q0*L
      -> 1+2^D*3^(q0+q1)*L.

The second exponent has an astronomical number of digits, so the verifier
uses stable 3-adic quotients and exponent reduction modulo the exact register
Carmichael exponent.  It does not construct a third splash or an infinite
ordinary orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path

from breakoff_renormalization import construct_hierarchy
from breakoff_unit_slice import unit_isa
from unit_repetend_splash import crt_pair, minimal_target_exponent


SCHEMA = "collatz-unit-double-repetend-v1"


def factor_integer(value: int) -> list[tuple[int, int]]:
    if value < 1:
        raise ValueError("factorization input must be positive")
    factors: list[tuple[int, int]] = []
    prime = 2
    while prime * prime <= value:
        if value % prime == 0:
            exponent = 0
            while value % prime == 0:
                value //= prime
                exponent += 1
            factors.append((prime, exponent))
        prime = 3 if prime == 2 else prime + 2
    if value > 1:
        factors.append((value, 1))
    return factors


def carmichael(value: int) -> int:
    result = 1
    for prime, exponent in factor_integer(value):
        if prime == 2 and exponent >= 3:
            component = 1 << (exponent - 2)
        else:
            component = (prime - 1) * pow(prime, exponent - 1)
        result = math.lcm(result, component)
    return result


def valuation(value: int, prime: int) -> int:
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def stable_quotient(precision: int) -> tuple[int, int]:
    """Return ``c_precision mod 3^precision`` by its exact recurrence."""
    if precision < 1:
        raise ValueError("3-adic precision must be positive")
    modulus = pow(3, precision)
    current = 1
    recurrence_checks = 0
    for index in range(1, precision):
        following = (
            current
            - pow(3, index) * current * current
            + pow(3, 2 * index - 1) * current * current * current
        ) % modulus
        if (following - current) % pow(3, index):
            raise AssertionError("3-adic quotient failed to stabilize")
        current = following
        recurrence_checks += 1
    if current % 3 == 0:
        raise AssertionError("stable quotient is not a 3-adic unit")
    return current, recurrence_checks


def residue_of_second_repetend(
    q0: int,
    q1: int,
    k: int,
    precision: int,
    register_modulus: int,
) -> tuple[int, int]:
    """Compute ``R1`` modulo ``2*3^q0*M`` without forming T1 or R1."""
    conductor = valuation(register_modulus, 3)
    if precision != q0 + conductor or q1 < precision:
        raise AssertionError("insufficient stable-quotient precision")
    nonternary = register_modulus // pow(3, conductor)
    ternary_modulus = pow(3, precision)
    other_modulus = 2 * nonternary

    # Modulo 3^precision the quotient was forced to equal one.  Modulo the
    # coprime factor 2*M0, reduce T1=3^(q1-1)k by lambda(M0).
    exponent_modulus = carmichael(nonternary)
    exponent_residue = (
        pow(3, q1 - 1, exponent_modulus) * k
    ) % exponent_modulus
    power_mod_nonternary = pow(2, exponent_residue, nonternary)
    # The actual power is even; combine that parity with its odd-modulus row.
    power_mod_other = (
        power_mod_nonternary
        + nonternary * (power_mod_nonternary % 2)
    ) % other_modulus
    if power_mod_other % 2 or power_mod_other % nonternary != power_mod_nonternary:
        raise AssertionError("second power CRT failed")
    repetend_mod_other = (
        (power_mod_other + 1)
        * pow(pow(3, q1, other_modulus), -1, other_modulus)
    ) % other_modulus
    combined = crt_pair(
        1, ternary_modulus, repetend_mod_other, other_modulus
    )
    expected_modulus = 2 * pow(3, q0) * register_modulus
    if combined.modulus != expected_modulus:
        raise AssertionError("second repetend residue has the wrong modulus")
    if (combined.residue - 1) % (2 * pow(3, q0)):
        raise AssertionError("second repetend did not retain the first bank")
    return combined.residue, combined.modulus


def build_record(final_gap_bits: int) -> dict[str, object]:
    if final_gap_bits < 1:
        raise ValueError("final regenerated gap must be positive")
    hierarchy, _ = construct_hierarchy(6)
    parent = hierarchy[1]
    unit = unit_isa(parent)
    if unit.level != 2 or unit.collision_sign != -1:
        raise AssertionError("double renewal requires the sign-negative level")

    marker, q0, _, t0, n1 = minimal_target_exponent(parent, 1)
    if marker != 1:
        raise AssertionError("first negative repetend did not emit one")
    q1 = unit.ternary_cell * n1 + unit.ternary_offset
    register_modulus = unit.register_stride
    conductor = valuation(register_modulus, 3)
    precision = q0 + conductor
    stable, recurrence_checks = stable_quotient(precision)

    # k*c_(q1)=1 mod 3^precision, T1=3^(q1-1)k=p(n2), and k is odd.
    ternary_precision = pow(3, precision)
    k_ternary = pow(stable, -1, ternary_precision)
    a = unit.binary_cell
    affine_offset = unit.binary_offset + unit.division_exponent
    k_affine = (
        affine_offset
        * pow(pow(3, q1 - 1, a), -1, a)
    ) % a
    k_solution = crt_pair(k_ternary, ternary_precision, k_affine, a)
    k = k_solution.residue or k_solution.modulus
    if k % 2 == 0:
        k += k_solution.modulus
    if k * stable % ternary_precision != 1:
        raise AssertionError("second repetend lost its retained ternary bank")
    if pow(3, q1 - 1, a) * k % a != affine_offset % a:
        raise AssertionError("second target exponent missed the affine class")
    if k % 2 != 1:
        raise AssertionError("second repetend multiplier must be odd")

    r1_residue, r1_modulus = residue_of_second_repetend(
        q0, q1, k, precision, register_modulus
    )
    bridge_residue = (
        (r1_residue - 1) // (2 * pow(3, q0))
    ) % register_modulus

    # Reduce the unmaterialized exponent T1 modulo lambda(M), then choose the
    # free final packet L so that the first source core is in the register.
    register_exponent = carmichael(register_modulus)
    t1_mod_register_exponent = (
        pow(3, q1 - 1, register_exponent) * k
    ) % register_exponent
    power_t1_mod_register = pow(
        2, t1_mod_register_exponent, register_modulus
    )

    power0 = pow(3, q0)
    lifted_modulus0 = power0 * register_modulus
    numerator0 = (pow(2, t0, lifted_modulus0) + 1) % lifted_modulus0
    if numerator0 % power0:
        raise AssertionError("first repetend residue is not integral")
    r0_mod_register = (numerator0 // power0) % register_modulus

    source_public = unit.binary_cell + unit.binary_offset
    invariant_source_core = (
        unit.register_offset
        * pow(pow(2, source_public, register_modulus), -1, register_modulus)
    ) % register_modulus
    fixed_source = (
        r0_mod_register
        + pow(2, t0 + 1, register_modulus) * bridge_residue
    ) % register_modulus
    free_coefficient = (
        pow(2, t0 + final_gap_bits, register_modulus)
        * power_t1_mod_register
    ) % register_modulus
    final_packet_residue = (
        (invariant_source_core - fixed_source)
        * pow(free_coefficient, -1, register_modulus)
    ) % register_modulus
    if final_packet_residue == 0:
        final_packet_residue = register_modulus

    source_core_mod_register = (
        fixed_source + free_coefficient * final_packet_residue
    ) % register_modulus
    r1_mod_register = r1_residue % register_modulus
    middle_core_mod_register = (
        r1_mod_register
        + power_t1_mod_register
        * pow(2, final_gap_bits, register_modulus)
        * pow(3, q0, register_modulus)
        * final_packet_residue
    ) % register_modulus
    final_core_mod_register = (
        1
        + pow(2, final_gap_bits, register_modulus)
        * pow(3, q0 + q1, register_modulus)
        * final_packet_residue
    ) % register_modulus
    first_target_public = t0 - unit.division_exponent
    second_target_public_mod = (
        t1_mod_register_exponent - unit.division_exponent
    ) % register_exponent
    expected_phase = unit.register_offset % register_modulus
    phases = (
        pow(2, source_public, register_modulus)
        * source_core_mod_register
        % register_modulus,
        pow(2, first_target_public, register_modulus)
        * middle_core_mod_register
        % register_modulus,
        pow(2, second_target_public_mod, register_modulus)
        * final_core_mod_register
        % register_modulus,
    )
    if any(phase != expected_phase for phase in phases):
        raise AssertionError("double repetend register phase failed")
    if any(value % 3 == 0 for value in (
        source_core_mod_register,
        middle_core_mod_register,
        final_core_mod_register,
    )):
        raise AssertionError("double repetend core lost coprimality to three")

    return {
        "level": unit.level,
        "collision_sign": unit.collision_sign,
        "source_cells": 1,
        "q0": q0,
        "T0": str(t0),
        "n1": str(n1),
        "q1": str(q1),
        "register_3_adic_conductor": conductor,
        "stable_quotient_precision": precision,
        "stable_quotient_recurrence_checks": recurrence_checks,
        "stable_quotient_sha256": hashlib.sha256(str(stable).encode()).hexdigest(),
        "second_multiplier_k": str(k),
        "second_multiplier_decimal_digits": len(str(k)),
        "T1_formula": f"3^({q1 - 1})*{k}",
        "n2_formula": (
            f"(3^({q1 - 1})*{k}-{affine_offset})/{a}"
        ),
        "final_gap_bits": final_gap_bits,
        "final_packet_residue_mod_register_sha256": hashlib.sha256(
            str(final_packet_residue).encode()
        ).hexdigest(),
        "final_packet_residue_bits": final_packet_residue.bit_length(),
        "symbolic_chain": {
            "R0": "(2^T0+1)/3^q0",
            "R1": "(2^T1+1)/3^q1",
            "A": "(R1-1)/(2*3^q0)",
            "K0": "A+2^(T1+D-1)*L",
            "h0": "R0+2^(T0+1)*K0",
            "h1": "R1+2^(T1+D)*3^q0*L",
            "h2": "1+2^D*3^(q0+q1)*L",
        },
        "checks": {
            "stable_3_adic_quotient_checked": True,
            "second_repetend_retains_first_ternary_bank": True,
            "second_target_affine_exponent_checked": True,
            "second_multiplier_odd_checked": True,
            "bridge_integrality_checked": True,
            "all_three_register_phases_checked": True,
            "all_three_cores_coprime_to_six_checked": True,
            "unbounded_positive_final_packet_family": True,
        },
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


def build_certificate(gap_sizes: tuple[int, ...] = (1, 64)) -> dict[str, object]:
    if not gap_sizes or min(gap_sizes) < 1:
        raise ValueError("all final gaps must be positive")
    records = [build_record(gap) for gap in gap_sizes]
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact symbolic two-splash renewal at the finite sign-negative "
            "level-two unit ISA, with stable 3-adic quotient, affine-exponent, "
            "bridge-integrality, and register-phase audits; T1 is represented "
            "by a power expression and no infinite ordinary orbit is claimed"
        ),
        "quotient_recurrence": (
            "c_(m+1)=c_m-3^m*c_m^2+3^(2m-1)*c_m^3 for "
            "c_m=(2^(3^(m-1))+1)/3^m"
        ),
        "bounds": {
            "compiled_level": 2,
            "source_cells": 1,
            "final_gap_sizes": list(gap_sizes),
            "symbolic_two_splash_families": len(records),
        },
        "records": records,
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported double-repetend schema")
    bounds = data["bounds"]
    expected = build_certificate(
        tuple(int(value) for value in bounds["final_gap_sizes"])
    )
    if data != expected:
        raise ValueError("double-repetend artifact failed reconstruction")


def selftest() -> None:
    build_record(7)


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(200_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--gap-sizes", default="1,64")
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("unit double-repetend selftest: PASS")
    elif args.command == "build":
        gaps = tuple(int(value) for value in args.gap_sizes.split(","))
        data = build_certificate(gaps)
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit double-repetend artifact: PASS")


if __name__ == "__main__":
    main()
