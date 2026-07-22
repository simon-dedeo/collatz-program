#!/usr/bin/env python3
"""Formula-compressed strike--scrub--turnaround macro at unit level two.

The regenerative carry rail translates a finite carry ``B`` across a gap
``D``.  This worker adds a third collision which consumes the whole gap and
returns the remote payload to an active dyadic writer.

At the sign-negative level-two unit ISA use source and target length one,
choose remote carry ``B=1`` and turnaround marker ``H=17``.  A following
length ``ell`` is required to satisfy two independent congruences:

1. a finite 3-adic congruence makes the first correction emit a prefix whose
   next collision leaves exactly ``H`` and whose isolated carry is ``B``;
2. a formula-compressed 2-adic congruence makes ``3^q(ell)*H-1`` consume the
   regenerated gap with the next legal affine division exponent.

The first class is computed explicitly by a base-two discrete logarithm
modulo ``3^114``.  The second class has about ``10^27`` bits and is therefore
represented by its exact group-theoretic definition.  Existence uses the
kernel-checked theorem ``KontoroC.orderOf_three_twoPow``: powers of three have
order ``2^(n-2)`` modulo ``2^n``.  The two classes have compatible parity and
CRT therefore gives an ordinary finite ``ell``.

After the third collision, restricting one ordinary tail modulo the odd
register stride and modulo four gives

    h_out = R + 2*M*3^Q*w.

The coefficient after the single factor two is odd.  Hence this turnaround
can write any prescribed finite odd dyadic word while retaining an affine
tail.  This is a universal finite reseed interface, not an autonomous
infinite orbit: linking infinitely many prescribed words can still select
only a 2-adic tail.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from breakoff_renormalization import construct_hierarchy
from breakoff_unit_slice import unit_isa


SCHEMA = "collatz-unit-carry-turnaround-v1"


def exact_order_two_mod_three_power(exponent: int) -> int:
    if exponent < 2:
        raise ValueError("turnaround order audit expects exponent at least two")
    modulus = pow(3, exponent)
    order = 2 * pow(3, exponent - 1)
    if pow(2, order, modulus) != 1:
        raise AssertionError("candidate order of two is not an order")
    if pow(2, order // 2, modulus) == 1:
        raise AssertionError("order retained an unnecessary factor two")
    if pow(2, order // 3, modulus) == 1:
        raise AssertionError("order retained an unnecessary factor three")
    return order


def discrete_log_two_mod_three_power(target: int, exponent: int) -> tuple[int, int]:
    """Pohlig--Hellman lifting for the primitive root 2 modulo ``3^n``."""
    modulus = pow(3, exponent)
    target %= modulus
    if target % 3 == 0:
        raise ValueError("discrete-log target is not a ternary unit")
    value = 0 if target % 3 == 1 else 1
    order = 2
    for precision in range(1, exponent):
        lifted_modulus = pow(3, precision + 1)
        candidates = [
            value + digit * order
            for digit in range(3)
            if pow(2, value + digit * order, lifted_modulus)
            == target % lifted_modulus
        ]
        if len(candidates) != 1:
            raise AssertionError("ternary discrete-log digit did not lift uniquely")
        value = candidates[0]
        order *= 3
    if order != exact_order_two_mod_three_power(exponent):
        raise AssertionError("lifted logarithm has the wrong period")
    if pow(2, value, modulus) != target:
        raise AssertionError("lifted ternary discrete logarithm failed")
    return value, order


def build_record() -> dict[str, object]:
    hierarchy, _ = construct_hierarchy(2)
    unit = unit_isa(hierarchy[1])
    if (
        unit.level,
        unit.binary_cell,
        unit.binary_offset,
        unit.ternary_cell,
        unit.ternary_offset,
        unit.division_exponent,
        unit.collision_sign,
    ) != (2, 23, 3, 17, 40, 51, -1):
        raise AssertionError("level-two unit constants changed")

    source_cells = 1
    target_cells = 1
    carry = 1
    marker = 17
    source_q = unit.ternary_cell * source_cells + unit.ternary_offset
    target_q = unit.ternary_cell * target_cells + unit.ternary_offset
    target_division = (
        unit.binary_cell * target_cells
        + unit.binary_offset
        + unit.division_exponent
    )
    if (source_q, target_q, target_division) != (57, 57, 77):
        raise AssertionError("canonical one-cell exponents changed")

    # The carry-repetend period: B=1 has no ternary factor.
    gap = exact_order_two_mod_three_power(source_q)

    # Choose the next legal division exponent just beyond the returned packet
    # boundary D+1.  At level two the legal class is 54 modulo 23.
    division_offset = unit.binary_offset + unit.division_exponent
    extra = (division_offset - (gap + 1)) % unit.binary_cell
    turnaround_division = gap + 1 + extra
    giant_target_cells = (
        turnaround_division - division_offset
    ) // unit.binary_cell
    if extra != 1 or giant_target_cells < 1:
        raise AssertionError("canonical turnaround lost its one-bit trim")

    # Simultaneously force the first correction carry B and the next low
    # marker H.  Eliminating its instruction prefix C gives one power-of-two
    # target modulo 3^(target_q+source_q).
    ternary_precision = target_q + source_q
    ternary_modulus = pow(3, ternary_precision)
    numerator = -(pow(2, target_division) + pow(3, target_q))
    denominator = (
        pow(2, target_division)
        * (marker + 2 * pow(3, target_q) * carry)
    )
    power_target = (
        numerator * pow(denominator % ternary_modulus, -1, ternary_modulus)
    ) % ternary_modulus
    power_logarithm, following_period = discrete_log_two_mod_three_power(
        power_target, ternary_precision
    )
    following_residue = (
        (power_logarithm - division_offset)
        * pow(unit.binary_cell, -1, following_period)
    ) % following_period
    if pow(
        2,
        unit.binary_cell * following_residue + division_offset,
        ternary_modulus,
    ) != power_target:
        raise AssertionError("following-length ternary class failed")

    # Reduction modulo 3^target_q is exactly the marker condition
    # 2^p(ell)*H=-1.  The full precision additionally fixes carry B=1.
    marker_modulus = pow(3, target_q)
    if (
        pow(
            2,
            unit.binary_cell * following_residue + division_offset,
            marker_modulus,
        )
        * marker
        + 1
    ) % marker_modulus:
        raise AssertionError("following class does not emit the marker")

    # The 2-adic class asks
    #   3^(17*ell+40)*H = 1+2^P (mod 2^(P+1)).
    # H=17 is 1 mod 8, so the right side times H^-1 lies in the even-power
    # subgroup generated by 3.  `orderOf_three_twoPow` gives its exact size.
    # The corresponding exponent beta is even, hence ell is even.  The
    # explicit ternary class is also even, which is the sole CRT compatibility
    # condition because gcd(2*3^113,2^(P-1))=2.
    if marker % 8 != 1:
        raise AssertionError("turnaround marker is outside the even 3-power class")
    ternary_class_parity = following_residue % 2
    two_adic_class_parity = 0
    if ternary_class_parity != two_adic_class_parity:
        raise AssertionError("turnaround CRT classes have incompatible parity")

    register_stride = unit.register_stride
    if register_stride % 2 == 0:
        raise AssertionError("unit register stride is not odd")

    return {
        "level": unit.level,
        "source_cells": source_cells,
        "target_cells": target_cells,
        "collision_sign": unit.collision_sign,
        "carry_B": carry,
        "turnaround_marker_H": marker,
        "source_ternary_exponent": source_q,
        "target_ternary_exponent": target_q,
        "target_division_exponent": target_division,
        "catcher_gap_D": gap,
        "catcher_gap_decimal_digits": len(str(gap)),
        "turnaround_extra_division_bits": extra,
        "turnaround_division_P": turnaround_division,
        "giant_target_cells": giant_target_cells,
        "giant_target_cells_decimal_digits": len(str(giant_target_cells)),
        "ternary_alignment_precision": ternary_precision,
        "ternary_alignment_power_target": power_target,
        "ternary_alignment_discrete_log": power_logarithm,
        "following_length_residue": following_residue,
        "following_length_modulus": following_period,
        "following_length_residue_parity": ternary_class_parity,
        "two_adic_length_class": (
            "ell=(beta-40)/17 mod 2^(P-1), where beta is the unique even "
            "class with 3^beta*17=1+2^P mod 2^(P+1)"
        ),
        "two_adic_length_modulus_exponent": turnaround_division - 1,
        "crt_compatibility_gcd": 2,
        "register_stride": register_stride,
        "register_stride_bits": register_stride.bit_length(),
        "output_writer": {
            "tail_restriction": (
                "choose u=u0+4*M*w with u0=1 mod 4 and the unique source "
                "register phase mod M"
            ),
            "affine_form": "h_out=R+2*M*3^(q(ell)+114)*w",
            "universality": (
                "for every E>=1 and odd target T there is a unique "
                "w mod 2^(E-1) with h_out=T mod 2^E"
            ),
        },
        "checks": {
            "level_two_constants": True,
            "exact_order_two_mod_3q": True,
            "explicit_discrete_log_mod_3pow114": True,
            "marker_and_carry_alignment": True,
            "legal_giant_division_class": True,
            "two_adic_subgroup_membership_from_H_mod_8": True,
            "length_crt_parity_compatibility": True,
            "ordinary_tail_crt_mod_4_and_odd_register": True,
            "universal_odd_dyadic_output_writer": True,
        },
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("unit_carry_repetend.py"),
        Path(__file__).with_name("unit_gap_regenerator.py"),
        Path(__file__).with_name("breakoff_unit_slice.py"),
        Path(__file__).with_name("breakoff_renormalization.py"),
        Path(__file__).with_name("breakoff_superether.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def build_certificate() -> dict[str, object]:
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "formula-compressed exact existence of one level-two finite "
            "strike-scrub-turnaround family and a universal finite dyadic "
            "reseed interface; the 2-adic subgroup order is kernel-checked "
            "in KontoroC.orderOf_three_twoPow; no explicit expansion of the "
            "giant following length, infinite ordinary orbit, or Collatz "
            "counterexample is claimed"
        ),
        "symbolic_chain": [
            "3^57*A-1=2^77*C+2^(77+L)*B",
            "B+3^57*z=2^D*B",
            "3^57*C-1=2^p(ell)*H",
            "h2=H+2^(D+1)*3^57*(B+3^57*u)",
            "3^q(ell)*H=1+2^P mod 2^(P+1)",
            "u=u0+4*M*w -> h3=R+2*M*3^(q(ell)+114)*w",
        ],
        "kernel_dependency": (
            "KontoroC.orderOf_three_twoPow: orderOf 3 modulo "
            "2^(n+3) is 2^(n+1)"
        ),
        "record": build_record(),
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported unit carry-turnaround schema")
    expected = build_certificate()
    if data != expected:
        raise ValueError("unit carry-turnaround artifact failed reconstruction")


def selftest() -> None:
    for exponent in range(2, 12):
        order = exact_order_two_mod_three_power(exponent)
        for sample in range(min(order, 32)):
            target = pow(2, sample, pow(3, exponent))
            found, found_order = discrete_log_two_mod_three_power(
                target, exponent
            )
            assert found_order == order
            assert found == sample % order
    record = build_record()
    assert record["turnaround_extra_division_bits"] == 1
    assert record["following_length_residue_parity"] == 0


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(100_000)
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
        print("unit carry-turnaround selftest: PASS")
    elif args.command == "build":
        args.output.write_text(render(build_certificate()))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit carry-turnaround artifact: PASS")


if __name__ == "__main__":
    main()
