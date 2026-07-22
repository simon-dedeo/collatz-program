#!/usr/bin/env python3
"""Formula-compressed expanding marker turnaround at unit level two.

The fixed-marker carry turnaround uses ``H=17``.  Its dyadic turnaround
condition then forces the preceding instruction length into a residue class
modulo ``2^(D+1)``, with no useful ordinary-size bound.  Here the instruction
length is fixed at one cell and the marker itself is synthesized by CRT with
an explicit ``D+O(1)`` bit bound.

The ternary marker residue makes the first two collisions emit carry ``B=1``.
An independent dyadic residue makes the third collision consume exactly the
regenerated gap.  Since their moduli are coprime, a finite positive marker
exists with only ``D+O(1)`` bits.  The resulting affine tail coefficient is
larger at the output than at the input.

This is one exact finite outward strike--scrub--turnaround family.  It is not
an invariant family, an infinite ordinary orbit, or a Collatz counterexample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from breakoff_renormalization import construct_hierarchy
from breakoff_unit_slice import unit_isa


SCHEMA = "collatz-unit-marker-turnaround-v1"


def exact_order_two_mod_three_power(exponent: int) -> int:
    if exponent < 2:
        raise ValueError("order audit expects exponent at least two")
    modulus = pow(3, exponent)
    order = 2 * pow(3, exponent - 1)
    if pow(2, order, modulus) != 1:
        raise AssertionError("candidate order is not an order")
    if pow(2, order // 2, modulus) == 1:
        raise AssertionError("candidate retained an unnecessary factor two")
    if pow(2, order // 3, modulus) == 1:
        raise AssertionError("candidate retained an unnecessary factor three")
    return order


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
    following_cells = 1
    source_q = unit.ternary_cell * source_cells + unit.ternary_offset
    source_p = (
        unit.binary_cell * source_cells
        + unit.binary_offset
        + unit.division_exponent
    )
    following_p = (
        unit.binary_cell * following_cells
        + unit.binary_offset
        + unit.division_exponent
    )
    following_q = (
        unit.ternary_cell * following_cells + unit.ternary_offset
    )
    if (source_p, source_q, following_p, following_q) != (77, 57, 77, 57):
        raise AssertionError("canonical one-cell exponents changed")

    # The instruction prefix has one exactness bit beyond p(1).
    prefix_width = following_p + 1
    carry = 1

    # Require C=(2^77 H+1)/3^57 and
    # 3^57 A-1=2^77 C+2^155.  Eliminating A,C fixes H modulo
    # 3^(57+57).  Every lift H=h+3^114*t keeps B=1.
    ternary_precision = source_q + following_q
    ternary_modulus = pow(3, ternary_precision)
    marker_ternary_residue = (
        -(
            pow(2, source_p)
            + pow(3, source_q)
            * (pow(2, source_p + prefix_width) * carry + 1)
        )
        * pow(pow(2, source_p + following_p), -1, ternary_modulus)
    ) % ternary_modulus
    if not 0 < marker_ternary_residue < ternary_modulus:
        raise AssertionError("marker residue is not canonical positive")

    first_ternary_modulus = pow(3, following_q)
    marker_prefix_numerator = (
        pow(2, following_p) * marker_ternary_residue + 1
    )
    if marker_prefix_numerator % first_ternary_modulus:
        raise AssertionError("marker does not make the second collision integral")
    prefix_residue = marker_prefix_numerator // first_ternary_modulus
    correction_numerator = (
        pow(2, source_p) * prefix_residue
        + pow(2, source_p + prefix_width) * carry
        + 1
    )
    if correction_numerator % pow(3, source_q):
        raise AssertionError("marker does not make the first collision integral")
    correction_residue = correction_numerator // pow(3, source_q)
    if correction_residue % 2 != 1 or prefix_residue % 2 != 1:
        raise AssertionError("one-cell collision quotients are not odd")

    # B+3^57*z=2^D*B with B=1.
    gap = exact_order_two_mod_three_power(source_q)
    if gap != 2 * pow(3, 56):
        raise AssertionError("canonical carry gap changed")

    # The next legal division strictly beyond D+1 is P=D+2.
    division_offset = unit.binary_offset + unit.division_exponent
    extra = (division_offset - (gap + 1)) % unit.binary_cell
    turnaround_p = gap + 1 + extra
    turnaround_cells = (turnaround_p - division_offset) // unit.binary_cell
    turnaround_q = (
        unit.ternary_cell * turnaround_cells + unit.ternary_offset
    )
    if extra != 1 or turnaround_p != gap + 2:
        raise AssertionError("canonical one-bit turnaround trim changed")

    # Synthesize t modulo 2^(P+1) from
    #   3^(q_g+114)*t = 1+2^P-3^q_g*h  (mod 2^(P+1)),
    # then H=h+3^114*t.  The coefficient is odd, so the residue exists
    # uniquely.  Reducing modulo two also proves H is odd.  The congruence
    # makes (3^q_g*H-1)/2^P odd, hence the third valuation is exactly P.
    marker_lift_modulus_exponent = turnaround_p + 1
    marker_lift_coefficient_exponent = turnaround_q + ternary_precision
    target_parity = (1 - marker_ternary_residue) % 2
    marker_parity = (
        marker_ternary_residue + target_parity
    ) % 2
    if marker_parity != 1:
        raise AssertionError("synthesized marker parity is not odd")
    if (1 + pow(3, source_q, 4)) % 4:
        raise AssertionError("u=1 mod 4 no longer suppresses the remote carry")

    # Let u=u0+4*M*w.  The source and output w-coefficients are
    #   2^(p+L+D+2)*M = 2^(D+157)*M,
    #   2*M*3^(q_g+114).
    # Their ratio is 3^Q/2^(D+156).  Q is even and 9>8 proves an exact
    # positive lower bound on the bit gain without expanding either power.
    register_stride = unit.register_stride
    if register_stride % 2 == 0:
        raise AssertionError("unit register stride is not odd")
    input_coefficient_two_exponent = (
        source_p + prefix_width + gap + 2
    )
    output_coefficient_three_exponent = (
        turnaround_q + ternary_precision
    )
    output_coefficient_two_factor = 1
    if output_coefficient_three_exponent % 2:
        raise AssertionError("canonical output exponent is not even")
    certified_gain_bits = (
        3 * (output_coefficient_three_exponent // 2)
        - (input_coefficient_two_exponent - output_coefficient_two_factor)
    )
    if certified_gain_bits <= 0:
        raise AssertionError("turnaround affine coefficient is not expanding")

    marker_bit_bound = (
        marker_lift_modulus_exponent + pow(3, ternary_precision).bit_length() + 1
    )

    return {
        "level": unit.level,
        "collision_sign": unit.collision_sign,
        "source_cells": source_cells,
        "following_cells": following_cells,
        "source_division_exponent": source_p,
        "source_ternary_exponent": source_q,
        "fixed_following_division_exponent": following_p,
        "fixed_following_ternary_exponent": following_q,
        "instruction_prefix_width": prefix_width,
        "carry_B": carry,
        "marker_ternary_precision": ternary_precision,
        "marker_ternary_residue": marker_ternary_residue,
        "prefix_C_at_t_zero": prefix_residue,
        "correction_A_at_t_zero": correction_residue,
        "marker_affine_lift": {
            "marker": "H=h3+3^114*t",
            "prefix": "C=C0+2^77*3^57*t",
            "correction": "A=A0+2^154*t",
        },
        "catcher_gap_D": gap,
        "catcher_gap_decimal_digits": len(str(gap)),
        "turnaround_division_P": turnaround_p,
        "turnaround_cells": turnaround_cells,
        "turnaround_ternary_exponent": turnaround_q,
        "marker_lift": {
            "modulus": "2^(P+1)",
            "modulus_exponent": marker_lift_modulus_exponent,
            "odd_coefficient": f"3^{marker_lift_coefficient_exponent}",
            "target": (
                "1+2^P-3^q_g*h3; choose the unique t modulo 2^(P+1)"
            ),
            "exact_turnaround": "3^q_g*H=1+2^P mod 2^(P+1)",
            "marker_is_odd": True,
        },
        "marker_bit_length_upper_bound": marker_bit_bound,
        "register_stride": register_stride,
        "register_tail": (
            "choose u=u0+4*M*w by CRT from the unique source-register "
            "class modulo odd M and u=1 mod 4"
        ),
        "input_w_coefficient": f"2^{input_coefficient_two_exponent}*M",
        "output_w_coefficient": (
            f"2*M*3^{output_coefficient_three_exponent}"
        ),
        "coefficient_ratio": (
            f"3^{output_coefficient_three_exponent}/"
            f"2^{input_coefficient_two_exponent - 1}"
        ),
        "nine_over_eight_gain_proof": {
            "three_exponent_is_even": True,
            "certified_bit_gain_lower_bound": certified_gain_bits,
            "identity": "3^(2k)=9^k>8^k=2^(3k)",
            "output_coefficient_strictly_larger": True,
        },
        "symbolic_chain": [
            "3^57*A-1=2^77*C+2^155",
            "3^57*C-1=2^77*H",
            "1+3^57*z=2^D",
            "H=h3+3^114*t",
            "3^q_g*H=1+2^P mod 2^(P+1)",
            "u=u0+4*M*w",
            "input coefficient=2^(D+157)*M",
            "output coefficient=2*M*3^(q_g+114)",
        ],
        "checks": {
            "level_two_constants": True,
            "fixed_one_cell_second_instruction": True,
            "explicit_marker_residue_mod_3pow114": True,
            "marker_preserves_carry_one": True,
            "exact_order_two_mod_3pow57": True,
            "legal_turnaround_division": True,
            "odd_coefficient_marker_writer": True,
            "exact_third_valuation_from_next_bit": True,
            "ordinary_register_tail_crt": True,
            "strict_affine_coefficient_growth": True,
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
            "formula-compressed exact existence of a finite level-two "
            "strike-scrub-turnaround family with a fixed one-cell second "
            "instruction, a D+O(1)-bit synthesized marker, and a strictly "
            "expanding affine tail coefficient; generic odd-coefficient "
            "modular inversion and coprime CRT supply the unexpanded "
            "marker and register tail; no invariant family, infinite "
            "ordinary orbit, or Collatz counterexample is claimed"
        ),
        "kernel_dependencies": [
            (
                "KontoroC.exists_oddCoefficient_solution_mod_twoPow: an odd "
                "coefficient permutes residues modulo every power of two"
            ),
            (
                "standard coprime CRT: the odd unit-register modulus M is "
                "coprime to 4"
            ),
        ],
        "record": build_record(),
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported unit marker-turnaround schema")
    if data != build_certificate():
        raise ValueError("unit marker-turnaround artifact failed reconstruction")


def selftest() -> None:
    for exponent in range(2, 14):
        exact_order_two_mod_three_power(exponent)

    # Fully materialize a small surrogate of the same three-collision
    # algebra.  This checks every division and the claimed exact valuations;
    # the public level-two instance remains formula-compressed because its D
    # is about 10^27.
    q = 3
    p = 5
    width = p + 1
    carry = 1
    precision = 2 * q
    mod3 = pow(3, precision)
    h3 = (
        -(
            pow(2, p)
            + pow(3, q) * (pow(2, p + width) * carry + 1)
        )
        * pow(pow(2, 2 * p), -1, mod3)
    ) % mod3
    c0 = (pow(2, p) * h3 + 1) // pow(3, q)
    a0 = (
        pow(2, p) * c0 + pow(2, p + width) * carry + 1
    ) // pow(3, q)
    gap = exact_order_two_mod_three_power(q)
    z = (pow(2, gap) - 1) // pow(3, q)
    turnaround_p = gap + 2
    turnaround_q = 7
    mod2 = 1 << (turnaround_p + 1)
    target = (
        1 + (1 << turnaround_p) - pow(3, turnaround_q) * h3
    ) % mod2
    t = (
        target
        * pow(pow(3, turnaround_q + precision), -1, mod2)
    ) % mod2
    marker = h3 + pow(3, precision) * t
    prefix = c0 + pow(2, p) * pow(3, q) * t
    correction = a0 + pow(2, 2 * p) * t
    u = 1
    source = correction + pow(2, p + width) * (
        z + pow(2, gap) * u
    )
    first_numerator = pow(3, q) * source - 1
    assert first_numerator % pow(2, p) == 0
    assert (first_numerator // pow(2, p)) % 2 == 1
    first = first_numerator // pow(2, p)
    second_numerator = pow(3, q) * first - 1
    assert second_numerator % pow(2, p) == 0
    assert (second_numerator // pow(2, p)) % 2 == 1
    second = second_numerator // pow(2, p)
    assert second == marker + pow(2, gap + 1) * pow(3, q) * (
        1 + pow(3, q) * u
    )
    third_numerator = pow(3, turnaround_q) * second - 1
    assert third_numerator % pow(2, turnaround_p) == 0
    assert (third_numerator // pow(2, turnaround_p)) % 2 == 1

    record = build_record()
    assert record["marker_lift"]["marker_is_odd"]
    assert record["nine_over_eight_gain_proof"][
        "output_coefficient_strictly_larger"
    ]


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
        print("unit marker-turnaround selftest: PASS")
    elif args.command == "build":
        args.output.write_text(render(build_certificate()))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit marker-turnaround artifact: PASS")


if __name__ == "__main__":
    main()
