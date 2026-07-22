#!/usr/bin/env python3
"""Formula-generated repetend splashes for enormous nonlinear unit jumps.

For a unit branch with ternary exponent q and collision sign s, choose an odd
marker C and an exponent T satisfying

    2^T*C = s  (mod 3^q).

Then ``R=(2^T*C-s)/3^q`` is an ordinary positive integer and, for every D and
K,

    3^q*(R+2^(T+D)*K)+s = 2^T*(C+2^D*3^q*K).

Thus one periodic rational-base correction rail is annihilated at collision,
emits C, and regenerates D clean binary positions before the surviving
packet.  If additionally ``T=p(n')`` in the affine unit exponent schedule,
the identity is a genuine source-length to enormous target-length unit jump.

This worker constructs one such symbolic jump at each of the six finite unit
hierarchy levels.  The exponents rapidly become far too large to materialize;
the certificate verifies exact modular identities and register phases without
expanding ``2^T``.  It supplies no infinite orbit or self-renewal rule.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from dataclasses import dataclass
from pathlib import Path

from breakoff_renormalization import construct_hierarchy
from breakoff_superether import RegisterISA
from breakoff_unit_slice import unit_isa


SCHEMA = "collatz-unit-repetend-splash-v1"


@dataclass(frozen=True)
class CongruenceSolution:
    residue: int
    modulus: int


def extended_gcd(left: int, right: int) -> tuple[int, int, int]:
    if right == 0:
        return left, 1, 0
    common, x, y = extended_gcd(right, left % right)
    return common, y, x - (left // right) * y


def crt_pair(
    first_residue: int,
    first_modulus: int,
    second_residue: int,
    second_modulus: int,
) -> CongruenceSolution:
    common, inverse, _ = extended_gcd(first_modulus, second_modulus)
    difference = second_residue - first_residue
    if difference % common:
        raise ValueError("incompatible exponent congruences")
    reduced_second = second_modulus // common
    multiplier = (
        (difference // common) * inverse
    ) % reduced_second
    modulus = first_modulus * reduced_second
    residue = (first_residue + first_modulus * multiplier) % modulus
    return CongruenceSolution(residue=residue, modulus=modulus)


def baby_step_giant_step(
    base: int, target: int, modulus: int, order: int
) -> int:
    """Exact bounded discrete logarithm in a supplied cyclic subgroup."""
    width = math.isqrt(order) + 1
    table: dict[int, int] = {}
    value = 1
    for index in range(width):
        table.setdefault(value, index)
        value = value * base % modulus
    giant_factor = pow(pow(base, width, modulus), -1, modulus)
    value = target % modulus
    for giant in range(width + 1):
        if value in table:
            exponent = giant * width + table[value]
            if exponent < order and pow(base, exponent, modulus) == target % modulus:
                return exponent
        value = value * giant_factor % modulus
    raise ValueError("discrete logarithm not found in supplied order")


def exact_order_of_two(q: int) -> int:
    """Audit ``ord_(3^q)(2)=2*3^(q-1)`` at the supplied concrete q."""
    if q < 2:
        raise ValueError("the repetend audit uses q>=2")
    modulus = pow(3, q)
    order = 2 * pow(3, q - 1)
    if pow(2, order, modulus) != 1:
        raise AssertionError("candidate power is not an order")
    if pow(2, order // 2, modulus) == 1:
        raise AssertionError("order retained an unnecessary factor two")
    if pow(2, order // 3, modulus) == 1:
        raise AssertionError("order retained an unnecessary factor three")
    return order


def marker_exponent_class(
    parent: RegisterISA, source_cells: int
) -> tuple[int, int, int, int]:
    """Return ``(C,t0,O,q)`` with ``2^t0*C=s (mod 3^q)``."""
    unit = unit_isa(parent)
    q = unit.ternary_cell * source_cells + unit.ternary_offset
    modulus = pow(3, q)
    order = exact_order_of_two(q)
    sign = unit.collision_sign

    # C=1 gives the ordinary minus/plus-one repetend at five levels.  The
    # level-one affine p-class is odd while +1 needs an even order multiple;
    # C=5 changes the mod-3 phase and has a small exact discrete logarithm.
    if unit.level == 1:
        marker = 5
        exponent = baby_step_giant_step(
            2,
            sign * pow(marker, -1, modulus),
            modulus,
            order,
        )
    else:
        marker = 1
        exponent = 0 if sign == 1 else order // 2
    if pow(2, exponent, modulus) * marker % modulus != sign % modulus:
        raise AssertionError("marker exponent class failed")
    return marker, exponent, order, q


def minimal_target_exponent(
    parent: RegisterISA, source_cells: int
) -> tuple[int, int, int, int, int]:
    """Intersect the repetend exponent with ``p(n')=a*n'+B``."""
    unit = unit_isa(parent)
    marker, exponent, order, q = marker_exponent_class(parent, source_cells)
    a = unit.binary_cell
    offset = unit.binary_offset + unit.division_exponent
    solution = crt_pair(exponent, order, offset % a, a)
    target = solution.residue
    minimum = a + offset
    if target < minimum:
        target += (
            (minimum - target + solution.modulus - 1) // solution.modulus
        ) * solution.modulus
    if target % a != offset % a or target % order != exponent:
        raise AssertionError("target exponent lost a CRT condition")
    target_cells = (target - offset) // a
    if target_cells < 1:
        raise AssertionError("target unit length is not positive")
    return marker, q, order, target, target_cells


def decimal_sha256(value: int) -> str:
    return hashlib.sha256(str(value).encode()).hexdigest()


def construct_record(
    parent: RegisterISA,
    source_cells: int,
    gap_bits: int,
) -> dict[str, object]:
    if min(source_cells, gap_bits) < 1:
        raise ValueError("source length and gap must be positive")
    unit = unit_isa(parent)
    marker, q, order, target, target_cells = minimal_target_exponent(
        parent, source_cells
    )
    power = pow(3, q)
    if (pow(2, target, power) * marker - unit.collision_sign) % power:
        raise AssertionError("repetend numerator is not integral")

    # Compute R modulo the odd register stride without ever forming 2^T.
    register_modulus = unit.register_stride
    lifted_modulus = power * register_modulus
    numerator_residue = (
        pow(2, target, lifted_modulus) * marker - unit.collision_sign
    ) % lifted_modulus
    if numerator_residue % power:
        raise AssertionError("lifted repetend residue is not divisible")
    repetend_mod_register = (numerator_residue // power) % register_modulus

    source_public = unit.binary_cell * source_cells + unit.binary_offset
    target_public = target - unit.division_exponent
    if target_public != (
        unit.binary_cell * target_cells + unit.binary_offset
    ):
        raise AssertionError("target public exponent is inconsistent")
    invariant_source_core = (
        unit.register_offset
        * pow(1 << source_public, -1, register_modulus)
    ) % register_modulus
    packet_coefficient = pow(2, target + gap_bits, register_modulus)
    packet_residue = (
        (invariant_source_core - repetend_mod_register)
        * pow(packet_coefficient, -1, register_modulus)
    ) % register_modulus
    if packet_residue == 0:
        packet_residue = register_modulus

    source_core_mod_register = (
        repetend_mod_register + packet_coefficient * packet_residue
    ) % register_modulus
    target_core_mod_register = (
        marker
        + (1 << gap_bits) * power * packet_residue
    ) % register_modulus
    if source_core_mod_register != invariant_source_core:
        raise AssertionError("source register phase failed")
    if (
        pow(2, source_public, register_modulus)
        * source_core_mod_register
        - unit.register_offset
    ) % register_modulus:
        raise AssertionError("source public register failed")
    if (
        pow(2, target_public, register_modulus)
        * target_core_mod_register
        - unit.register_offset
    ) % register_modulus:
        raise AssertionError("target public register failed")
    if invariant_source_core % 3 == 0 or marker % 3 == 0:
        raise AssertionError("repetend splash core lost coprimality to three")
    if marker % 2 != 1:
        raise AssertionError("emitted marker is not odd")

    return {
        "level": unit.level,
        "collision_sign": unit.collision_sign,
        "source_cells": source_cells,
        "source_ternary_exponent_q": q,
        "emitted_marker_C": marker,
        "order_of_two_mod_3q": str(order),
        "target_division_exponent_T": str(target),
        "target_division_exponent_decimal_digits": len(str(target)),
        "target_cells": str(target_cells),
        "target_cells_decimal_digits": len(str(target_cells)),
        "regenerated_gap_bits_D": gap_bits,
        "packet_residue_mod_register_sha256": decimal_sha256(packet_residue),
        "packet_residue_bits": packet_residue.bit_length(),
        "formula": {
            "repetend": "R=(2^T*C-s)/3^q",
            "source_core": "h=R+2^(T+D)*(K0+M*v)",
            "target_core": "h'=C+2^D*3^q*(K0+M*v)",
            "identity": "3^q*h+s=2^T*h'",
        },
        "checks": {
            "exact_order_of_two_checked": True,
            "marker_congruence_checked": True,
            "affine_target_exponent_checked": True,
            "ordinary_repetend_integrality_checked": True,
            "source_register_phase_checked": True,
            "target_register_phase_checked": True,
            "odd_exact_target_core_checked": True,
            "arbitrary_natural_tail_family": True,
        },
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("breakoff_unit_slice.py"),
        Path(__file__).with_name("breakoff_renormalization.py"),
        Path(__file__).with_name("breakoff_superether.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def build_certificate(
    source_cells: int = 1, gap_sizes: tuple[int, ...] = (1, 64)
) -> dict[str, object]:
    hierarchy, _ = construct_hierarchy(6)
    records = [
        construct_record(parent, source_cells, gap)
        for parent in hierarchy
        for gap in gap_sizes
    ]
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact symbolic repetend-splash and register-phase certificates "
            "for one source length at six finite unit levels and the listed "
            "gap sizes; huge powers are verified modularly, not materialized; "
            "no infinite orbit is claimed"
        ),
        "universal_identity": (
            "if 3^q divides 2^T*C-s, then R=(2^T*C-s)/3^q and "
            "3^q*(R+2^(T+D)*K)+s=2^T*(C+2^D*3^q*K)"
        ),
        "bounds": {
            "compiled_levels": 6,
            "source_cells": source_cells,
            "gap_sizes": list(gap_sizes),
            "symbolic_families": len(records),
        },
        "records": records,
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported unit repetend-splash schema")
    bounds = data["bounds"]
    expected = build_certificate(
        int(bounds["source_cells"]),
        tuple(int(value) for value in bounds["gap_sizes"]),
    )
    if data != expected:
        raise ValueError("unit repetend-splash artifact failed reconstruction")


def selftest() -> None:
    hierarchy, _ = construct_hierarchy(6)
    for parent in hierarchy:
        construct_record(parent, 1, 7)


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(200_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--source-cells", type=int, default=1)
    build.add_argument("--gap-sizes", default="1,64")
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("unit repetend-splash selftest: PASS")
    elif args.command == "build":
        gaps = tuple(int(value) for value in args.gap_sizes.split(","))
        data = build_certificate(args.source_cells, gaps)
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit repetend-splash artifact: PASS")


if __name__ == "__main__":
    main()
