#!/usr/bin/env python3
"""Variable-length synthesized-marker bank and its rank-one normal form.

The expanding marker turnaround admits every later legal division

    P_j = D + 2 + 23*j,       q_j = q_0 + 17*j.

At first sight its marker lift and remote packet look like two independent
tails.  Exactness of the third division forces the remote catcher to acquire
the same extra ``23*j`` dyadic alignment as the marker, while register
invariance forces the remote lift to cancel the marker modulo the odd stride
``M``.  Consequently both tails enter through one combined natural register
``v=s+w`` with a common factor ``M``:

    x_j = X_j + 2^(P_j+155) * M * v,
    y_j = Y_j + 2 * M * 3^(q_j+114) * v.

This worker checks the public exponent algebra, the all-j coefficient-growth
factor, and fully materializes a small surrogate for several opcodes.  The
rank-one collapse prevents treating the two spatial islands as two free
stacks.  The unbounded opcode bank remains a variable-length positive-drift
tag language; no autonomous infinite orbit is claimed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from breakoff_renormalization import construct_hierarchy
from breakoff_unit_slice import unit_isa
from unit_marker_turnaround import (
    build_record as build_turnaround_record,
    exact_order_two_mod_three_power,
)


SCHEMA = "collatz-unit-marker-bank-v1"


def v2(value: int) -> int:
    if value == 0:
        raise ValueError("v2(0) is undefined")
    value = abs(value)
    return (value & -value).bit_length() - 1


def marker_residue(q: int, p: int) -> tuple[int, int, int]:
    """Return the canonical ``(h,C,A)`` residue triple for carry one."""
    width = p + 1
    precision = 2 * q
    modulus = pow(3, precision)
    h = (
        -(
            pow(2, p)
            + pow(3, q) * (pow(2, p + width) + 1)
        )
        * pow(pow(2, 2 * p), -1, modulus)
    ) % modulus
    c_numerator = pow(2, p) * h + 1
    if c_numerator % pow(3, q):
        raise AssertionError("marker prefix is not integral")
    c = c_numerator // pow(3, q)
    a_numerator = pow(2, p) * c + pow(2, p + width) + 1
    if a_numerator % pow(3, q):
        raise AssertionError("marker correction is not integral")
    a = a_numerator // pow(3, q)
    if not all(value > 0 and value % 2 for value in (h, c, a)):
        raise AssertionError("canonical marker triple is not positive odd")
    return h, c, a


def small_surrogate_record(opcode: int) -> dict[str, int | bool]:
    """Materialize one small analogue of the public rank-one instruction."""
    if opcode < 0:
        raise ValueError("opcode must be nonnegative")
    q = 3
    p = 5
    width = p + 1
    precision = 2 * q
    carry = 1
    gap = exact_order_two_mod_three_power(q)
    binary_step = 3
    ternary_step = 2
    turnaround_p = gap + 2 + binary_step * opcode
    turnaround_q = 7 + ternary_step * opcode
    marker_h, prefix_c, correction_a = marker_residue(q, p)

    marker_modulus = 1 << (turnaround_p + 1)
    marker_target = (
        1
        + (1 << turnaround_p)
        - pow(3, turnaround_q) * marker_h
    ) % marker_modulus
    marker_base = (
        marker_target
        * pow(pow(3, turnaround_q + precision), -1, marker_modulus)
    ) % marker_modulus

    # Exactness of the remote contribution through P_j requires
    # 1+3^q*u=0 mod 2^(P_j-D).  Intersect this with a small odd register
    # modulus.  When the marker lift changes by s, use (M-1)*s in
    # the remote lift: its equal dyadic coefficient cancels s modulo M.
    remote_exponent = turnaround_p - gap
    remote_modulus = 1 << remote_exponent
    remote_residue = (
        -carry * pow(pow(3, q), -1, remote_modulus)
    ) % remote_modulus
    register_modulus = 5
    register_residue = 1
    register_lift = (
        (register_residue - remote_residue)
        * pow(remote_modulus, -1, register_modulus)
    ) % register_modulus
    remote_base = remote_residue + remote_modulus * register_lift

    z = (pow(2, gap) - 1) // pow(3, q)

    def replay(marker_tail: int, remote_tail: int) -> tuple[int, int]:
        t = marker_base + marker_modulus * marker_tail
        marker = marker_h + pow(3, precision) * t
        prefix = prefix_c + pow(2, p) * pow(3, q) * t
        correction = correction_a + pow(2, 2 * p) * t
        u = remote_base + remote_modulus * (
            (register_modulus - 1) * marker_tail
            + register_modulus * remote_tail
        )
        source = correction + pow(2, p + width) * (
            z + pow(2, gap) * u
        )
        first_numerator = pow(3, q) * source - 1
        if v2(first_numerator) != p:
            raise AssertionError("small first valuation is not exact")
        first = first_numerator >> p
        second_numerator = pow(3, q) * first - 1
        if v2(second_numerator) != p:
            raise AssertionError("small second valuation is not exact")
        second = second_numerator >> p
        third_numerator = pow(3, turnaround_q) * second - 1
        if v2(third_numerator) != turnaround_p:
            raise AssertionError("small third valuation is not exact")
        third = third_numerator >> turnaround_p
        return source, third

    source_zero, output_zero = replay(0, 0)
    marker_tail = 2
    remote_tail = 3
    source, output = replay(marker_tail, remote_tail)
    combined = marker_tail + remote_tail
    expected_source_delta = pow(
        2, turnaround_p + 2 * p + 1
    ) * register_modulus * combined
    expected_output_delta = (
        2
        * register_modulus
        * pow(3, turnaround_q + precision)
        * combined
    )
    if source - source_zero != expected_source_delta:
        raise AssertionError("small source did not collapse to one register")
    if output - output_zero != expected_output_delta:
        raise AssertionError("small output did not collapse to one register")

    return {
        "opcode": opcode,
        "gap_D": gap,
        "turnaround_P": turnaround_p,
        "turnaround_q": turnaround_q,
        "remote_alignment_exponent": remote_exponent,
        "combined_register": combined,
        "source_zero": source_zero,
        "output_zero": output_zero,
        "source_combined_two_exponent": turnaround_p + 2 * p + 1,
        "output_combined_three_exponent": turnaround_q + precision,
        "source_bits": source.bit_length(),
        "output_bits": output.bit_length(),
        "three_exact_divisions_checked": True,
        "rank_one_source_delta_checked": True,
        "rank_one_output_delta_checked": True,
        "source_register_delta_checked": (
            (source - source_zero) % register_modulus == 0
        ),
    }


def build_record(opcodes: int = 16) -> dict[str, object]:
    if opcodes < 1:
        raise ValueError("opcode audit requires at least one opcode")
    hierarchy, _ = construct_hierarchy(2)
    unit = unit_isa(hierarchy[1])
    base = build_turnaround_record()
    if (
        unit.binary_cell,
        unit.ternary_cell,
        base["catcher_gap_D"],
        base["turnaround_division_P"],
    ) != (23, 17, 2 * pow(3, 56), 2 * pow(3, 56) + 2):
        raise AssertionError("public marker-turnaround constants changed")

    gap = int(base["catcher_gap_D"])
    base_p = int(base["turnaround_division_P"])
    base_cells = int(base["turnaround_cells"])
    base_q = int(base["turnaround_ternary_exponent"])
    base_output_q = base_q + 114
    register_modulus = unit.register_stride
    if register_modulus % 2 == 0:
        raise AssertionError("public register modulus is not odd")

    rows: list[dict[str, object]] = []
    for opcode in range(opcodes):
        turnaround_p = base_p + unit.binary_cell * opcode
        cells = base_cells + opcode
        turnaround_q = base_q + unit.ternary_cell * opcode
        if (
            unit.binary_cell * cells
            + unit.binary_offset
            + unit.division_exponent
            != turnaround_p
        ):
            raise AssertionError("bank division is outside the legal class")
        if unit.ternary_cell * cells + unit.ternary_offset != turnaround_q:
            raise AssertionError("bank ternary exponent is outside its class")

        remote_alignment = turnaround_p - gap
        source_combined_exponent = turnaround_p + 155
        marker_source_exponent = 154 + (turnaround_p + 1)
        remote_source_exponent = 155 + gap + remote_alignment
        if not (
            marker_source_exponent
            == remote_source_exponent
            == source_combined_exponent
        ):
            raise AssertionError("marker and remote coefficients did not collapse")

        output_three_exponent = turnaround_q + 114
        rows.append(
            {
                "opcode_j": opcode,
                "turnaround_cells": cells,
                "turnaround_division_Pj": turnaround_p,
                "turnaround_ternary_qj": turnaround_q,
                "remote_alignment_exponent": remote_alignment,
                "source_combined_two_exponent": source_combined_exponent,
                "output_combined_three_exponent": output_three_exponent,
                "source_normal_form": (
                    f"X_{opcode}+2^{source_combined_exponent}*M*(s+w)"
                ),
                "output_normal_form": (
                    f"Y_{opcode}+2*M*3^{output_three_exponent}*(s+w)"
                ),
                "rank_one_collapse_checked": True,
            }
        )

    base_gain = (
        3 * (base_output_q // 2) - (base_p + 154)
    )
    if base_output_q % 2 or base_gain <= 0:
        raise AssertionError("base opcode lost its exact 9-over-8 gain")
    per_opcode_three = pow(3, unit.ternary_cell)
    per_opcode_two = pow(2, unit.binary_cell)
    if per_opcode_three <= per_opcode_two:
        raise AssertionError("opcode increment is not coefficient-expanding")
    rows_sha256 = hashlib.sha256(
        json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()

    return {
        "level": unit.level,
        "collision_sign": unit.collision_sign,
        "carry_B": 1,
        "gap_D": gap,
        "binary_opcode_step": unit.binary_cell,
        "ternary_opcode_step": unit.ternary_cell,
        "base_turnaround_P0": base_p,
        "base_turnaround_q0": base_q,
        "base_output_three_exponent_Q0": base_output_q,
        "register_modulus_M": register_modulus,
        "all_opcode_formulas": {
            "P_j": "D+2+23*j",
            "q_j": "q_0+17*j",
            "marker_tail": "t=t_j+2^(P_j+1)*s",
            "remote_tail": (
                "u=u_j+2^(P_j-D)*((M-1)*s+M*w); u_j makes "
                "1+3^57*u_j=0 mod 2^(P_j-D), and M-1 cancels "
                "the marker lift in the invariant register"
            ),
            "combined_register": "v=s+w",
            "source": "x_j=X_j+2^(P_j+155)*M*v",
            "output": "y_j=Y_j+2*M*3^(q_j+114)*v",
        },
        "rank_one_identity": {
            "marker_source_exponent": "154+(P_j+1)=P_j+155",
            "remote_source_exponent": (
                "155+D+(P_j-D)=P_j+155"
            ),
            "conclusion": (
                "exact third-division alignment plus register invariance "
                "collapses the marker lift and remote packet to v=s+w, "
                "with a common factor M"
            ),
            "register_compensation": "remote marker coefficient is M-1",
        },
        "positive_drift": {
            "base_nine_over_eight_bit_margin": base_gain,
            "per_opcode_factor": "3^17/2^23",
            "three_pow_17": per_opcode_three,
            "two_pow_23": per_opcode_two,
            "per_opcode_factor_gt_one": True,
            "all_opcodes_have_larger_output_coefficient": True,
        },
        "audited_public_opcode_count": len(rows),
        "audited_public_opcodes_sha256": rows_sha256,
        "first_audited_public_opcode": rows[0],
        "last_audited_public_opcode": rows[-1],
        "small_materialized_replays": [
            small_surrogate_record(opcode) for opcode in range(6)
        ],
        "checks": {
            "legal_all_j_exponent_formulas": True,
            "exact_remote_alignment_formula": True,
            "rank_one_source_and_output_formulas": True,
            "positive_drift_for_every_nonnegative_opcode": True,
            "six_small_three_collision_replays": True,
        },
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("unit_marker_turnaround.py"),
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
            "formula-compressed all-nonnegative-opcode exponent and "
            "coefficient identities for the level-two synthesized-marker "
            "bank, plus exact materialized three-collision replays for six "
            "small surrogate opcodes; exact alignment plus invariant-register "
            "coupling forces the apparent marker and remote tails into one "
            "combined register, and every "
            "bank opcode has positive coefficient drift; no payload-selected "
            "opcode law, infinite ordinary orbit, or Collatz counterexample "
            "is claimed"
        ),
        "record": build_record(),
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported unit marker-bank schema")
    if data != build_certificate():
        raise ValueError("unit marker-bank artifact failed reconstruction")


def selftest() -> None:
    record = build_record()
    assert record["audited_public_opcode_count"] == 16
    assert len(record["small_materialized_replays"]) == 6
    assert all(
        row["source_register_delta_checked"]
        for row in record["small_materialized_replays"]
    )
    assert record["positive_drift"]["per_opcode_factor_gt_one"]


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
        print("unit marker-bank selftest: PASS")
    elif args.command == "build":
        args.output.write_text(render(build_certificate()))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit marker-bank artifact: PASS")


if __name__ == "__main__":
    main()
